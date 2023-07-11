options indenting = 4
options no_unused_block_arguments = false
options no_unused_function_arguments = false
options no_aot = true
options strict_smart_pointers = true

module parser_generator

require daslib/match public
require daslib/strings
require daslib/ast
require daslib/fio
require daslib/rtti
require daslib/ast_boost
require daslib/utf8_utils
require daslib/templates_boost

require peg/meta_ast


struct ParserGenerator
    // Provides information to generate unique names
    rule_counter: table<string; int>

    // Maps rule name into its declared type (typeof(add))
    // Action block returns the same result as in the mapping
    rule_types: table<string; TypeDeclPtr>

    // E.g. add => ResultAdd aka tuple<bool;typeof(add);int>
    return_types: table<string; TypeDeclPtr>

    // Contains the required result type for the current block return type
    // This is actully the tip of the stack of contexts. A different context
    // is entered during the generation of code for repetition (*) and option (MB)
    current_context: string

    // E.g. jsonParser
    parser_name: string

    // The constructed type for the parser
    parser_type: TypeDeclPtr


def abort(message: string)
    print("{message}\n")
    stackwalk(false, false)
    unsafe { exit(1); }


def iota
    return <- generator<int>() <|
        var i: int = 0
        while true
            i += 1
            return false if i == 0 else yield i

def rule_left_recursive(name: string; rule: Rule): bool
    match rule
        if [[Rule alt = $v(alts)]]
            for a in alts
                return true if rule_left_recursive(name, a.rule.rule)

        if [[Rule seq = $v(seq)]]
            return true if rule_left_recursive(name, seq[0].rule)

        if [[Rule maybe_repeat = $v(rule_)]]
            return true if rule_left_recursive(name, rule_.rule)

        if [[Rule repeat = $v(rule_)]]
            return true if rule_left_recursive(name, rule_.rule)

        if [[Rule not_rule = $v(rule_)]]
            return true if rule_left_recursive(name, rule_.rule)

        if [[Rule and_rule = $v(rule_)]]
            return true if rule_left_recursive(name, rule_.rule)

        if [[Rule nonterminal = $v(name_)]]
            return true if name == name_

        if [[Rule bound_nonterminal = $v(tup)]]
            return true if tup._0 == name

        if [[Rule terminal = _]]
            return false

        if [[Rule text_extraction = $v(rule_)]]
            return true if rule_left_recursive(name, rule_.rule)

        if _
            abort("TODO: rule_left_recursive")

    return false


def generate_wrapper(var gen: ParserGenerator)
    let rule_name = gen.current_context
    let cache_table = "{rule_name}_cache"
    let inner_parsing_fun = "parse_{rule_name}_inner"

    var inscope return_type <- gen.return_types[rule_name] |> clone_type

    var inscope wrapper_fun <- qmacro_function("parse_{rule_name}") <| $ (var parser: $t(gen.parser_type)): $t(return_type)
        var mark = parser.index

        if parser.$f(cache_table) |> key_exists(parser.index)
            var result = parser.$f(cache_table)[parser.index]
            parser.index = result.endpos
            return <- result

        var result <- $c(inner_parsing_fun)(parser)
        parser.$f(cache_table)[mark] = result

        return <- result

    wrapper_fun.moreFlags |= MoreFunctionFlags skipLockCheck

    return <- wrapper_fun


def generate_wrapper_leftrec(var gen: ParserGenerator)
    let rule_name = gen.current_context
    let cache_table = "{rule_name}_cache"
    let inner_parsing_fun = "parse_{rule_name}_inner"

    var inscope return_type <- gen.return_types[rule_name] |> clone_type

    var inscope wrapper_fun <- qmacro_function("parse_{rule_name}") <| $ (var parser: $t(gen.parser_type)): $t(return_type)
        var mark = parser.index

        if parser.$f(cache_table) |> key_exists(parser.index)
            var result = parser.$f(cache_table)[parser.index]
            parser.index = result.endpos
            return result

        // Build new cache entry from scratch

        var res = [[$t(return_type)]]
        parser.$f(cache_table)[mark] = res

        while true
            parser.index = mark

            var newres = $c(inner_parsing_fun)(parser)
            var endpos = parser.index

            // Break if no movement
            break if res.endpos >= endpos

            res = newres
            parser.$f(cache_table)[mark] = res


        parser.index = res.endpos
        return res

    wrapper_fun.moreFlags |= MoreFunctionFlags skipLockCheck

    return <- wrapper_fun


def generate_parser_class(var gen: ParserGenerator; parser_name: string)
    var inscope s: StructurePtr <- new [[Structure()]]

    // jsonParser, expressionParser, dasParser
    gen.parser_name = "{parser_name}Parser"
    s.name := gen.parser_name // := string -> das_string

    s._module = compiling_module()

    // Add a field for every type of cache

    for rule_name in keys(gen.rule_types)
        if true
            // Make cache table type: table<int; <result-type-for-rule>>
            var inscope t2 <- qmacro_type(type<table<int; int>>)
            t2.secondType |> move_new (gen.return_types[rule_name] |> clone_type)

            s |> add_structure_field("{rule_name}_cache", t2)

    // Add input and index fields

    s |> add_structure_field_new("input", qmacro_type(type<array<uint8>>))
    s |> add_structure_field_new("index", qmacro_type(type<int>))

    s.flags |= StructureFlags skipLockCheck

    // Save constructed parser type for later

    var inscope parser_type <- qmacro_type(type<ParserGenerator>)
    parser_type.structType = s |> get_ptr

    gen.parser_type |> move <| parser_type

    compiling_module() |> add_structure(s)


def add_structure_field_new(var struct_: StructurePtr; name: string; var t: TypeDeclPtr)
    add_structure_field(struct_, name, t)

def add_structure_field(var struct_: StructurePtr; name: string; var t: TypeDeclPtr&)
    //! Adds a field to the structure.

    let fi = length(struct_.fields)
    struct_.fields |> resize(fi + 1)

    struct_.fields[fi].name := name
    struct_.fields[fi]._type |> move <| t


def make_default_type_decl: TypeDeclPtr
    //! Make default result (field value to be replaced later)
    return <- qmacro_type(type<tuple<success:bool; value:int; endpos:int>>)


def generate_result_types(var gen: ParserGenerator)
    //! Result types are used internally in the compiler to store in the cache.
    //!
    //! Manually they would be defined like so:
    //!     typedef Result1 = tuple<success:bool; value:int; endpos:int>;
    //! for every possible rule type
    //!

    for rule, type_ in keys(gen.rule_types), values(gen.rule_types)
        if true
            var inscope rule_res_type <- make_default_type_decl()
            rule_res_type.argTypes[1] |> move_new <| clone_type(type_)

            // Map name of the rule to its 'result' type
            gen.return_types[rule] |> move <| rule_res_type

    gen.return_types["__repetition__"] |> move_new <| make_default_type_decl()
    gen.return_types["__option__"] |> move_new <| make_default_type_decl()
    gen.return_types["__PEEK__"] |> move_new <| make_default_type_decl()


def generate(var gen: ParserGenerator; var def_: Definition)
    gen.current_context = def_.name

    var inscope function_body <- gen |> generate(def_.rule)
    var inscope return_type <- gen.return_types[def_.name] |> clone_type

    var inscope fun <- qmacro_function("parse_{def_.name}_inner") <| $ (var parser: $t(gen.parser_type)): $t(return_type)
        // $b(function_body)
        return <- [[$t(return_type)]]

    // // XXX: disabling locks for the entire function
    fun.moreFlags |= MoreFunctionFlags skipLockCheck

    //fun |> describe |> print
    compiling_module() |> add_function(fun)

    if rule_left_recursive(def_.name, def_.rule)
        var inscope wrapper <- gen |> generate_wrapper_leftrec
        compiling_module() |> add_function(wrapper)
    else
        var inscope wrapper <- gen |> generate_wrapper
        compiling_module() |> add_function(wrapper)


def generate_grammar(var gen: ParserGenerator; var gram: array<Definition>; name: string)
    for rule in gram
        gen |> set_rule_type(rule.name |> string(), rule.type_)

    gen |> generate_result_types

    gen |> generate_parser_class(name)

    for def_ in gram
        gen |> generate(def_)


def get_rule_type(var gen: ParserGenerator; rule: Rule): TypeDeclPtr
    match rule
        if [[Rule nonterminal = $v(nonterm)]]
            return <- gen.rule_types[nonterm] |> clone_type

        if [[Rule subrule = $v(subrule)]]
            abort("Infer subrule type")

    //abort("Unreachable")
    return <- [[TypeDeclPtr]]


def set_rule_type(var gen: ParserGenerator; rule_name: string; type_: TypeDeclPtr)
    gen.rule_types[rule_name] |> move_new(type_ |> clone_type)


def set_rule_handle(var subrule_: Rule_?; handle: string)
    //! Motivating example: *CommaSeparatedElements as els
    //!
    //! Here the name 'els' is bound to the repetition (*)
    //! In order to get the contents of the repetition in the resulting vector
    //! we need to bind the name of the subrule

    assume subrule_variant = subrule_.rule

    match subrule_variant
        if [[Rule nonterminal = $v(nonterm)]]
            unsafe // Moving values that contain smart pointers is generally unsafe
                   // But here we know that the contained variant is nonterminal (string) and cannot
                   // possibly contain valid smart pointer. Therefore it should be safe to overwrite it.
                subrule_.rule <- [[Rule bound_nonterminal = [[auto nonterm, handle]]]]
                return

        if [[Rule terminal = $v(term)]]
            match term
                if [[Terminal lit = $v(l) ]]
                    // Something like (*"123" as foo)
                    return
                if [[Terminal string_ = $v(name)]]
                    name = handle
                    return
                if [[Terminal double_ = $v(name)]]
                    name = handle
                    return
                if [[Terminal charset = $v(r) ]]
                    // *[1-9] as numbers -- should be possible
                    abort("Matching repeated literals is not allowed")
                if [[Terminal number = $v(name)]]
                    name = handle
                if [[Terminal whitespace = _]]
                    abort("Matching repeated whitespace is not allowed")
                if [[Terminal EOF = _]]
                    abort("Matching repeated EOF is not allowed")


    abort("Unreachable `def set_rule_handle`")


// Contract: each action is taken only once
def get_action_block(var alternative: Alternative): ExpressionPtr
    return <- alternative.action


def generate(var gen: ParserGenerator; var rule_: Rule): array<ExpressionPtr>
    match rule_
        if [[Rule terminal = $v(term)]]
            var inscope termb <- gen |> generate_terminal(term)
            return <- flatten_block(termb as ExprBlock)


        if [[Rule seq = $v(rules)]]

            var inscope result: array<ExpressionPtr>

            for rule in rules
                if true
                    var inscope exprs <- gen |> generate(rule.rule)
                    for expr in exprs
                        result |> emplace_new (expr |> clone_expression)

            return <- result

        if [[Rule alt = $v(alts)]]

            var inscope results: array<ExpressionPtr>

            for alt, i in alts, iota()
                results |> emplace_new <| generate_one_alternative(gen, alt, i)

            return <- results



    abort("Unreachable")
    return <- [[array<ExpressionPtr>]]



def generate_one_alternative(var gen: ParserGenerator; var alt: Alternative; i: int)
    let parse_pos = "pos{i}"
    let result  = "res{i}"

    var inscope action <- alt.action
    var inscope action_block <- action as ExprBlock |> flatten_block
    var inscope block_contents <- gen |> generate(alt.rule.rule)

    // Add epilogue (code that executes the associated action)

    block_contents |> alternative_add_epilogue(gen, action_block)

    // Generate the alternative
    var inscope fun <- qmacro_function("parse_{gen.current_context}_alternative_{i}") <| $ (var parser: $t(gen.parser_type))
        $b(block_contents)

    compiling_module() |> add_function <| fun

    return <- qmacro_block <|
        var parse_pos = parser.index
        var $i(result) <- $c("parse_{gen.current_context}_alternative_{i}")(parser)
        return <- $i(result) if $i(result).success
        parser.index = parse_pos


def alternative_add_epilogue(var block_contents: array<ExpressionPtr>; var gen: ParserGenerator; var action_block)
    var inscope action_type <- gen.rule_types[gen.current_context] |> clone_type()
    var inscope return_type <- gen.return_types[gen.current_context] |> clone_type()

    var inscope t <- qmacro_block <|
        var val: $t(action_type) <- invoke <| $(): $t(action_type)
            $b(action_block)

        // For some reason I cannot directly return [[Result]]
        var result: $t(return_type) <- [[$t(return_type) true, val, parser.index]]
        return <- result

    //block_contents |> append_block_contents <| t


def generate_terminal(var gen: ParserGenerator; var terminal: Terminal): ExpressionPtr
    var inscope return_type <- gen.return_types[gen.current_context] |> clone_type()

    match terminal

        if [[Terminal charset = $v(ranges) ]]

            // Get the currect charachter from the stream

            var inscope rule_code: array<ExpressionPtr>

            // rule_code |> append_block_new <| ( qmacro_block <| {
            //     let current_char = parser |> get_current_char;
            // } )

            // Check in it is inside any of the ranges

            // for r in ranges
            //     rule_code |> append_range(r)

            // Otherwise return false
            var inscope t <- qmacro_block <|
                return false

            rule_code |> append_block_new <| t

            return <- qmacro_block <|
                invoke <|
                    return false

                //return <- [[$t(return_type)]] if !success

                parser.index += 1

    abort("Unreachable")
    return <- [[ExpressionPtr]]

def append_block_new(var old: array<ExpressionPtr>; var new_code: ExpressionPtr)
    var inscope flat <- flatten_block(new_code as ExprBlock)

    for e in flat
        old |> emplace_new (e |> clone_expression)

    // delete new_code


// Contract: block is managed externally and will clean up its own memory
def flatten_block(var blk: ExprBlock?)
    var inscope result : array<ExpressionPtr>
    for e in blk.list
        result |> emplace_new (e |> clone_expression)
    return <- result

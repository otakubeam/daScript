//require daslib/profiler

options stack = 1000000000

require daslib/debug
options debugger

require daslib/strings_boost
require daslib/fio
require dastest/testing_boost
require daslib/utf8_utils
require peg/peg


struct Email
    username: string
    domain: string


[export]
def main

    parse test

        // var email: Email

        // rule("{alnums}" as username, "@", "{domain}" as domain) <|
        //     print("{username}@{domain}\n")
        //     return [[Email username = username, domain = domain]]

        // var alnums: void? // Just a pattern to be interpreted later

        // rule(+set('0'..'9', 'a'..'z', 'A'..'Z')) <|
        //     return null

        // var domain: void?

        // rule(+subdomain, tld) <|
        //     return null

        // var tld: void?

        // rule("com") <|
        //     return null
        // rule("net") <|
        //     return null
        // rule("org") <|
        //     return null

        var subdomain: void?

        rule( set('0'..'9')) <|
            return null
        // rule( ".", "fewf", "wefwef" ) <|
        //     return null




    // var parser <- [[testParser]]

    // var input = "abc@mail.example.com"

    // for char in input
    //     parser.input |> push(char |> uint8())

    // print("{parser |> parse_subdomain}\n")


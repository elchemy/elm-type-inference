module TranslationTests exposing (errors, functions, lets, literals)

import Helpers exposing (..)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import Result exposing (..)
import Test exposing (..)


literals : Test
literals =
    describe "Literals translation"
        [ test "Int" <| code "1" <| Ok <| unconstrained Type.int
        , test "String" <| code "\"a\"" <| Ok <| unconstrained Type.string
        , test "Float" <| code "1.2" <| Ok <| unconstrained Type.float
        , test "Lambda" <| code "\\a -> a" <| Ok <| unconstrained (TArrow (TAny 0) (TAny 0))
        , test "List" <|
            codeWithContext listEnv
                "[1,2,3]"
            <|
                Ok <|
                    unconstrained (Type.list Type.int)
        , test "BinOp" <| code "\"a\" ++ \"b\"" <| Ok <| unconstrained Type.string
        ]


lets : Test
lets =
    describe "Lets translation"
        [ test "Int" <| code "let a = 1 in a" <| Ok <| unconstrained Type.int
        , test "String" <| code "let a = \"a\" in a" <| Ok <| unconstrained Type.string
        , test "Float" <| code "let a = 2.2 in a" <| Ok <| unconstrained Type.float
        , test "Rearranged" <| code "let a = b \n b = 1.2 in a" <| Ok <| unconstrained Type.float
        , test "Recursion" <|
            code
                "let a b c = a ( b ++ \"1\") (c ++ \"1\") ++ \"1\" in a"
            <|
                Ok <|
                    unconstrained (Type.string => Type.string => Type.string)
        , test "Lambda" <| code "let a b c = b in a" <| Ok <| unconstrained (TAny 0 => TAny 1 => TAny 0)
        , test "Mutual dependency" <|
            code
                """
            let
                f x = if x <= 0 then -1 else g x
                g x = if x > 0 then 1 else f x
            in f 1
          """
            <|
                Ok (unconstrained Type.int)
        ]


errors : Test
errors =
    describe "Errors"
        [ test "Too many args" <| code "(\\a -> a) 1 2" <| Err "Mismatch: (.Int) -> 2 and (.Int)"
        , test "List with different types" <|
            codeWithContext listEnv "[1, 2, 3, \"4\"]" <|
                Err "Mismatch: .Int and .String"
        ]


functions : Test
functions =
    let
        listSum =
            """
let f l = case l of
    [] -> 0
    x :: xs -> x + f xs
    in f
"""
    in
    describe "Functions"
        [ test "List sum" <|
            codeWithContext listEnv "let f = foldr (+) 0 in f" <|
                Ok <|
                    unconstrained (Type.list Type.int => Type.int)
        , test "Also list sum" <|
            codeWithContext listEnv listSum <|
                Ok <|
                    unconstrained (Type.list Type.int => Type.int)
        , test "Factorial" <|
            code "let f x = if x <= 0 then 1 else x * f (x - 1) in f" <|
                Ok <|
                    unconstrained (Type.int => Type.int)
        ]

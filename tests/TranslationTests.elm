module TranslationTests exposing (errors, functions, lets, literals)

import Ast
import Ast.Common exposing (Pattern(..))
import Ast.Statement as Statement
import Ast.Translate as Translate
import Dict
import Expect exposing (equal)
import Helpers exposing (minimizeTAny)
import Infer
import Infer.DefaultEnvironment exposing (defaultEnvironment)
import Infer.Expression as Expression exposing (Expression, MExp)
import Infer.Monad as Infer
import Infer.Scheme exposing (Environment)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import Result exposing (..)
import Test exposing (..)


literals : Test
literals =
    describe "Literals translation"
        [ test "Int" <| code "1" <| Ok Type.int
        , test "String" <| code "\"a\"" <| Ok Type.string
        , test "Float" <| code "1.2" <| Ok Type.float
        , test "Lambda" <| code "\\a -> a" <| Ok (TArrow (TAny 0) (TAny 0))
        , test "List" <|
            codeWithContext listEnv
                "[1,2,3]"
            <|
                Ok (Type.list Type.int)
        , test "BinOp" <| code "\"a\" ++ \"b\"" <| Ok Type.string
        ]


lets : Test
lets =
    describe "Lets translation"
        [ test "Int" <| code "let a = 1 in a" <| Ok Type.int
        , test "String" <| code "let a = \"a\" in a" <| Ok Type.string
        , test "Float" <| code "let a = 2.2 in a" <| Ok Type.float
        , test "Rearanged" <| code "let a = b \n b = 1.2 in a" <| Ok Type.float
        , test "Recursion" <|
            code
                "let a b c = a ( b ++ \"1\") (c ++ \"1\") ++ \"1\" in a"
            <|
                Ok (Type.string => Type.string => Type.string)
        , test "Lambda" <| code "let a b c = b in a" <| Ok (TAny 0 => TAny 1 => TAny 0)
        ]


errors : Test
errors =
    describe "Errors"
        [ test "Too many args" <| code "(\\a -> a) 1 2" <| Err "Mismatch: (.Int) -> 0 and (.Int)"
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
                Ok (Type.list Type.int => Type.int)

        -- , test "Also list sum" <|
        --     codeWithContext listEnv listSum <|
        --         Ok (Type.list Type.int => Type.int)
        , test "Factorial" <|
            code "let f x = if x <= 0 then 1 else x * f (x - 1) in f" <|
                Ok (Type.int => Type.int)
        ]



--- HELPERS ---


typeOf : Environment -> MExp -> Result String Type
typeOf env exp =
    Infer.typeOf env exp
        |> Infer.finalValue 0
        |> Result.map Tuple.first


codeWithContext : Infer.Scheme.Environment -> String -> Result String RawType -> (() -> Expect.Expectation)
codeWithContext env input typeOrError =
    Ast.parse ("a = " ++ input)
        |> Result.mapError (always "Parsing failed")
        |> Result.andThen
            (\res ->
                case res of
                    ( _, _, [ ( Statement.FunctionDeclaration ( PVariable "a", _ ) body, _ ) ] ) ->
                        Ok body

                    _ ->
                        Err "Imparsable code"
            )
        |> Result.map Translate.expression
        |> Result.andThen (typeOf env)
        |> Result.map (Tuple.mapSecond minimizeTAny)
        |> equal (Result.map unconstrained typeOrError)
        |> (\a () -> a)


code : String -> Result String RawType -> (() -> Expect.Expectation)
code =
    codeWithContext defaultEnvironment


listEnv : Environment
listEnv =
    Dict.union defaultEnvironment <|
        Dict.fromList
            [ ( "foldr"
              , ( [ 0, 1 ]
                , unconstrained <| (TAny 0 => TAny 1 => TAny 1) => TAny 1 => Type.list (TAny 0) => TAny 1
                )
              )
            ]

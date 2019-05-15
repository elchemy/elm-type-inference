module TranslationTests exposing (errors, lets, literals)

import Ast
import Ast.Statement as Statement
import Ast.Translate as Translate
import Dict
import Expect exposing (equal)
import Infer
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
        , test "List" <| codeWithContext listEnv "[1,2,3]" <| Ok (Type.list Type.int)
        , test "BinOp" <| codeWithContext stringEnv "\"a\" ++ \"b\"" <| Ok Type.string
        ]


lets : Test
lets =
    describe "Lets translation"
        [ test "Int" <| code "let a = 1 in a" <| Ok Type.int
        , test "String" <| code "let a = \"a\" in a" <| Ok Type.string
        , test "Float" <| code "let a = 2.2 in a" <| Ok Type.float
        , test "Rearanged" <| code "let a = b \n b = 1.2 in a" <| Ok Type.float
        , test "Recursion" <|
            codeWithContext stringEnv
                "let a b c = a ( b ++ \"1\") (c ++ \"1\") ++ \"1\" in a"
            <|
                Ok (Type.string => Type.string => Type.string)
        , test "Lambda" <| code "let a b c = b in a" <| Ok (TAny 4 => TAny 5 => TAny 4)
        ]


errors : Test
errors =
    describe "Errors"
        [ test "Too many args" <| code "(\\a -> a) 1 2" <| Err "Mismatch: (.Int) -> 0 and (.Int)"
        , test "List with different types" <|
            codeWithContext listEnv "[1, 2, 3, \"4\"]" <|
                Err "Mismatch: .Int and .String"
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
                    ( _, _, [ ( Statement.FunctionDeclaration "a" [] body, _ ) ] ) ->
                        Ok body

                    _ ->
                        Err "Imparsable code"
            )
        |> Result.map Translate.expression
        |> Result.andThen (typeOf env)
        |> equal (Result.map unconstrained typeOrError)
        |> (\a -> \() -> a)


code : String -> Result String RawType -> (() -> Expect.Expectation)
code =
    codeWithContext Dict.empty


listEnv : Environment
listEnv =
    Dict.singleton "(::)"
        ( [ 1 ]
        , unconstrained <| TAny 1 => Type.list (TAny 1) => Type.list (TAny 1)
        )


stringEnv : Environment
stringEnv =
    Dict.singleton "(++)"
        ( []
        , unconstrained <| Type.string => Type.string => Type.string
        )

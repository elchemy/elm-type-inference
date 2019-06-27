module Tests exposing (regressions, typeInference)

import Dict
import Expect
import Helpers exposing (..)
import Infer
import Infer.Monad as Infer
import Infer.Scheme exposing (Environment, generalize, instantiate)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import Test exposing (..)


typeInference : Test
typeInference =
    describe "Type inference"
        [ test "trivial inference" <|
            equal
                (typeOf Dict.empty (fakeMeta stringLiteral))
                (Ok <| unconstrained Type.string)
        , test "identity construction" <|
            equal
                (typeOf
                    (Dict.singleton "identity" ( [ 1 ], unconstrained <| TAny 1 => TAny 1 ))
                    (fakeMeta <| CallSM (NameSM "identity")
                        (CallSM (NameSM "identity")
                            stringLiteral
                        )
                    )
                )
            <|
                Ok (unconstrained Type.string)
        , test "string concat" <|
            equal
                (typeOf
                    (Dict.singleton "(++)" ( [ 1 ], unconstrained <| Type.string => Type.string => Type.string ))
                    (fakeMeta <| CallSM
                        (CallSM (NameSM "(++)")
                            stringLiteral
                        )
                        stringLiteral
                    )
                )
            <|
                Ok (unconstrained Type.string)
        , test "let binding" <|
            equal
                (typeOf
                    Dict.empty
                    (fakeMeta <| LetSM
                        [ ( PVariableSM "x", stringLiteral ) ]
                        (NameSM "x")
                    )
                )
            <|
                Ok (unconstrained Type.string)
        , test "recursion with let" <|
            equal
                (typeOf
                    testEnv
                    (fakeMeta <| LetSM
                        [ ( PVariableSM "f"
                          , LambdaSM (PVariableSM "x") <|
                                if_ (LiteralSM <| unconstrained Type.bool)
                                    (CallSM (NameSM "f") (CallSM (CallSM (NameSM "+") (NameSM "x")) (NameSM "x")))
                                    stringLiteral
                          )
                        ]
                        (CallSM (NameSM "f") intLiteral)
                    )
                )
                (Ok <| unconstrained Type.string)
        , test "mutual recursion with let" <|
            equal
                (typeOf
                    testEnv
                    (fakeMeta <| LetSM
                        [ ( PVariableSM "f"
                          , LambdaSM (PVariableSM "x") <|
                                if_ (LiteralSM <| unconstrained Type.bool)
                                    (CallSM (NameSM "g") (CallSM (CallSM (NameSM "+") (NameSM "x")) (NameSM "x")))
                                    stringLiteral
                          )
                        , ( PVariableSM "g"
                          , NameSM "f"
                          )
                        ]
                        (CallSM (NameSM "f") intLiteral)
                    )
                )
                (Ok <| unconstrained Type.string)
        , test "polymorphic let" <|
            equal
                (typeOf
                    testEnv
                    (fakeMeta <| LetSM
                        [ ( PVariableSM "id", LambdaSM (PVariableSM "x") <| NameSM "x" )
                        ]
                        (tuple
                            (CallSM (NameSM "id") intLiteral)
                            (CallSM (NameSM "id") stringLiteral)
                        )
                    )
                )
                (Ok <| unconstrained <| TOpaque "Tuple" [ Type.int, Type.string ])
        , test "polymorphic let2" <|
            equal
                (typeOf
                    testEnv
                    (fakeMeta <| LetSM
                        [ ( PVariableSM "id", LambdaSM (PVariableSM "x") <| NameSM "x" )
                        , ( PVariableSM "a", CallSM (NameSM "id") intLiteral )
                        , ( PVariableSM "b", CallSM (NameSM "id") stringLiteral )
                        ]
                        (tuple (NameSM "a") (NameSM "b"))
                    )
                )
                (Ok <| unconstrained <| TOpaque "Tuple" [ Type.int, Type.string ])
        , test "spies on lets should work" <|
            variablesDiffer
                (Infer.typeOf
                    (Dict.singleton "Just"
                        ( [ 1 ], unconstrained <| TAny 1 => TOpaque "Maybe" [ TAny 1 ] )
                    )
                    (fakeMeta <| LetSM [ ( PVariableSM "x", SpySM (NameSM "Just") 900 ) ] (NameSM "x"))
                    |> Infer.finalValue 0
                    |> Result.map Tuple.second
                    |> Result.toMaybe
                    |> Maybe.andThen (Dict.get 900)
                    |> Maybe.withDefault (unconstrained <| TAny 1)
                )
                (unconstrained (TAny 1 => TOpaque "Maybe" [ TAny 1 ]))
        , test "number should propagate" <|
            equal
                (Result.map minimizeTAny <| typeOf
                    (Dict.singleton "+"
                        ( [ 3 ], ( Dict.singleton 3 Number, TAny 3 => TAny 3 => TAny 3 ) )
                    )
                    (fakeMeta <| LambdaSM (PVariableSM "x") <| CallSM (CallSM (NameSM "+") (NameSM "x")) (NameSM "x"))
                )
                (Ok ( Dict.singleton 0 Number, TAny 0 => TAny 0 ))
        ]


regressions : Test
regressions =
    describe "Regression tests"
        [ test "recursive type error when there should be none" <|
            equal
                (typeOf
                    testEnv
                    (fakeMeta <| if_
                        (LiteralSM <| unconstrained Type.bool)
                        (NameSM "+")
                        (NameSM "+")
                    )
                    |> Result.andThen
                        (generalize Dict.empty
                            >> instantiate
                            >> Infer.finalValue 1
                        )
                )
            <|
                Ok (Tuple.second arith)
        , test "same type variable should have same constraints" <|
            \() ->
                let
                    env =
                        Dict.fromList
                            [ ( "<"
                              , ( [ 1 ]
                                , ( Dict.singleton 1 Comparable
                                  , TAny 1 => TAny 1 => Type.bool
                                  )
                                )
                              )
                            , ( "++"
                              , ( [ 1 ]
                                , ( Dict.singleton 1 Appendable
                                  , TAny 1 => TAny 1 => TAny 1
                                  )
                                )
                              )
                            ]

                    empty =
                        LiteralSM << unconstrained << TAny

                    exp =
                        fakeMeta <|
                            CallSM
                                (CallSM (NameSM "<") (CallSM (CallSM (NameSM "++") (SpySM (empty 1) 2)) (empty 3)))
                                (SpySM (empty 4) 5)
                in
                Infer.typeOf env exp
                    |> Infer.finalValue 100
                    |> Result.map
                        (\( _, subs ) ->
                            Expect.equal (Dict.get 2 subs) (Dict.get 5 subs)
                        )
                    |> Result.withDefault (Expect.fail "did not type")
        ]

module Tests exposing (regressions, typeInference)

import Dict
import Expect
import Helpers exposing (..)
import Infer
import Infer.Monad as Infer
import Infer.Scheme exposing (Environment, generalize, instantiate)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import Test exposing (..)


typeOf :  Environment -> ExpressionSansMeta -> Result String Type
typeOf env exp =
    Infer.typeOf env (fakeMeta exp)
        |> Infer.finalValue 0
        |> Result.map Tuple.first


equal : a -> a -> () -> Expect.Expectation
equal a b =
    \() -> Expect.equal a b


variablesDiffer a b =
    \() ->
        Expect.true "parts other than type variables differ"
            (Type.unify a b
                |> Result.map (Dict.values >> List.all (Tuple.second >> isTAny))
                |> Result.withDefault False
            )


isTAny x =
    case x of
        TAny _ ->
            True

        _ ->
            False


stringLiteral =
    LiteralSM <| unconstrained Type.string


intLiteral =
    LiteralSM <| unconstrained Type.int


typeInference : Test
typeInference =
    describe "Type inference"
        [ test "trivial inference" <|
            equal
                (typeOf Dict.empty stringLiteral)
                (Ok <| unconstrained Type.string)
        , test "identity construction" <|
            equal
                (typeOf
                    (Dict.singleton "identity" ( [ 1 ], unconstrained <| TAny 1 => TAny 1 ))
                    (CallSM (NameSM "identity")
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
                    (CallSM
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
                    (LetSM
                        [ ( "x", stringLiteral ) ]
                        (NameSM "x")
                    )
                )
            <|
                Ok (unconstrained Type.string)
        , test "recursion with let" <|
            equal
                (typeOf
                    testEnv
                    (LetSM
                        [ ( "f"
                          , LambdaSM "x" <|
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
                    (LetSM
                        [ ( "f"
                          , LambdaSM "x" <|
                                if_ (LiteralSM <| unconstrained Type.bool)
                                    (CallSM (NameSM "g") (CallSM (CallSM (NameSM "+") (NameSM "x")) (NameSM "x")))
                                    stringLiteral
                          )
                        , ( "g"
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
                    (LetSM
                        [ ( "id", LambdaSM "x" <| NameSM "x" )
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
                    (LetSM
                        [ ( "id", LambdaSM "x" <| NameSM "x" )
                        , ( "a", CallSM (NameSM "id") intLiteral )
                        , ( "b", CallSM (NameSM "id") stringLiteral )
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
                    (fakeMeta <| LetSM [ ( "x", SpySM (NameSM "Just") 900 ) ] (NameSM "x"))
                    |> Infer.finalValue 0
                    |> Result.map Tuple.second
                    |> Result.toMaybe
                    |> Maybe.andThen (Dict.get 900)
                    |> Maybe.withDefault (unconstrained <| TAny 1)
                )
                (unconstrained (TAny 1 => TOpaque "Maybe" [ TAny 1 ]))
        , test "number should propagate" <|
            equal
                (typeOf
                    (Dict.singleton "+"
                        ( [ 1 ], ( Dict.singleton 1 Number, TAny 1 => TAny 1 => TAny 1 ) )
                    )
                    (LambdaSM "x" <| CallSM (CallSM (NameSM "+") (NameSM "x")) (NameSM "x"))
                )
                (Ok ( Dict.singleton 1 Number, TAny 1 => TAny 1 ))
        ]


regressions : Test
regressions =
    describe "Regression tests"
        [ test "recursive type error when there should be none" <|
            equal
                (typeOf
                    testEnv
                    (if_
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
                        fakeMeta <| CallSM
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


if_ a b c =
    CallSM (CallSM (CallSM (NameSM "if") a) b) c


testEnv =
    Dict.fromList
        [ ( "if"
          , ( [ 1 ]
            , unconstrained <| Type.bool => TAny 1 => TAny 1 => TAny 1
            )
          )
        , ( "+", arith )
        , ( "tuple2"
          , ( [ 1, 2 ]
            , unconstrained <| TAny 1 => TAny 2 => TOpaque "Tuple" [ TAny 1, TAny 2 ]
            )
          )
        ]


tuple a b =
    CallSM (CallSM (NameSM "tuple2") a) b


arith =
    ( [ 1 ], unconstrained <| TAny 1 => TAny 1 => TAny 1 )

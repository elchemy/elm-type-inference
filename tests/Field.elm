module Field exposing (aaa)

import Helpers exposing (..)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import Test exposing (..)


aaa : Test
aaa =
    describe "AAAA"
        [ test "polymorphic let2" <|
            equal
                (typeOf
                    testEnv
                    (fakeMeta <|
                        LetSM
                            [ ( PVariableSM "id", LambdaSM (PVariableSM "x") <| NameSM "x" )
                            , ( PVariableSM "a", CallSM (NameSM "id") intLiteral )
                            , ( PVariableSM "b", CallSM (NameSM "id") stringLiteral )
                            ]
                            (tuple (NameSM "a") (NameSM "b"))
                        -- (tuple (CallSM (NameSM "id") (intLiteral)) (CallSM (NameSM "id") (stringLiteral)))
                    )
                )
                (Ok <| unconstrained <| TOpaque "Tuple" [ Type.int, Type.string ])
        ]

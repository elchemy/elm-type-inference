module Infer.DefaultEnvironment exposing (defaultEnvironment)

import Dict exposing (Dict)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import Infer.Scheme exposing (Environment)

defaultEnvironment : Environment
defaultEnvironment =
    Dict.fromList
        [ -- LIST
          ( "::"
          , ( [ 1 ]
            , unconstrained <| TAny 1 => Type.list (TAny 1) => Type.list (TAny 1)
            )
          )
        , ( "++"
          , ( []
            , unconstrained <| Type.string => Type.string => Type.string
            )
          )

        -- MATH
        , ( "+"
          , ( [ 1 ]
            , ( Dict.singleton 1 Number, TAny 1 => TAny 1 => TAny 1 )
            )
          )
        , ( "*"
          , ( [ 1 ]
            , ( Dict.singleton 1 Number, TAny 1 => TAny 1 => TAny 1 )
            )
          )
        , ( "-"
          , ( [ 1 ]
            , ( Dict.singleton 1 Number, TAny 1 => TAny 1 => TAny 1 )
            )
          )

        -- COMPARE
        , ( "=="
          , ( [ 1 ]
            , ( Dict.singleton 1 Comparable, TAny 1 => TAny 1 => Type.bool )
            )
          )
        , ( ">"
          , ( [ 1 ]
            , ( Dict.singleton 1 Comparable, TAny 1 => TAny 1 => Type.bool )
            )
          )
        , ( "<"
          , ( [ 1 ]
            , ( Dict.singleton 1 Comparable, TAny 1 => TAny 1 => Type.bool )
            )
          )
        , ( ">="
          , ( [ 1 ]
            , ( Dict.singleton 1 Comparable, TAny 1 => TAny 1 => Type.bool )
            )
          )
        , ( "<="
          , ( [ 1 ]
            , ( Dict.singleton 1 Comparable, TAny 1 => TAny 1 => Type.bool )
            )
          )

        -- CONTROL FLOW
        , ( "if"
          , ( [ 1 ]
            , unconstrained <| Type.bool => TAny 1 => TAny 1 => TAny 1
            )
          )
        , ( "case"
          , ( [ 1, 2 ]
            , unconstrained <| TAny 1 => Type.list (TAny 1) => Type.list (TAny 2) => Type.list (TAny 2)
            )
          )
        ]

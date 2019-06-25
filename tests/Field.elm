module Field exposing (aaa)

import Helpers exposing (..)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)

import Test exposing (..)


aaa : Test
aaa =
    describe "AAA"
        [ test "Rearranged" <| code "let a = b \n b = 1.2 in a" <| Ok Type.float
        ]

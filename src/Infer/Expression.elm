module Infer.Expression exposing
    ( Expression(..), MExp
    )

{-| #


# Types

@docs Expression, MExp

-}

import Ast.Common exposing (Column, Line, Name, WithMeta)
import Ast.Identifiers exposing (Identifier)
import Infer.Type exposing (Type)


{-| Translate your expressions to this type in order to be able to perform type inference on them.
The Spy variant has no effect on type inference, but can be used to find the type of a subexpression.
-}
type Expression
    = Literal Type
    | Lambda String MExp
    | Call MExp MExp
    | Let (List ( String, MExp )) MExp
    | Name String
    | Spy MExp Int


{-| Expression enhanced with metadata containing id, line and column
-}
type alias MExp =
    WithMeta Expression Identifier

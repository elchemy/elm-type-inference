module Infer.Expression exposing
    ( Expression(..), MExp, Pattern(..), MPattern
    )

{-| #


# Types

@docs Expression, MExp, Pattern, MPattern

-}

import Ast.Common exposing (Column, Line, Name, WithMeta)
import Ast.Identifiers exposing (Identifier)
import Infer.Type exposing (Type)


{-| Translate your expressions to this type in order to be able to perform type inference on them.
The Spy variant has no effect on type inference, but can be used to find the type of a subexpression.
-}
type Expression
    = Literal Type
    | Lambda MPattern MExp
    | Call MExp MExp
    | Let (List ( MPattern, MExp )) MExp
    | Case MExp (List (MPattern, MExp))
    | Name Name
    | Spy MExp Int


{-| Expression enhanced with metadata containing id, line and column in a form of (e, meta)
-}
type alias MExp =
    WithMeta Expression Identifier

{-| Pattern matching -}
type Pattern
    = PWild
    | PName Name
    | PLiteral Type
    | PTuple (List MPattern)
    | PCons MPattern MPattern
    | PList (List MPattern)
    | PRecord (List Name)
    | PAs MPattern Name
    | PApplication MPattern MPattern


{-| Pattern enhanced with metadata containing id, line and column in a form of (e, meta)
-}
type alias MPattern =
    WithMeta Pattern Identifier

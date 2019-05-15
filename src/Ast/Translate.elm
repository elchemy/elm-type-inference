module Ast.Translate exposing (expression)

import Ast.Common exposing (Name)
import Ast.Expression as AstExp exposing (..)
import Infer.Expression as InferExp exposing (AstExpression(..), AstMExp, generateIds)
import Infer.Type as Type exposing (Type, unconstrained)


type alias ExMeta =
    {}


expression : MExp -> InferExp.MExp
expression e =
    generateIds e |> expression_


expression_ : AstMExp -> InferExp.MExp
expression_ ( e, meta ) =
    case e of
        ELet bindingList body ->
            ( InferExp.Let (bindings bindingList) (expression_ body), meta )

        EVariable [ name ] ->
            ( InferExp.Name name, meta )

        EInteger _ ->
            ( literal Type.int, meta )

        EFloat _ ->
            ( literal Type.float, meta )

        EString _ ->
            ( literal Type.string, meta )

        EList elems ->
            elems
                |> List.foldr
                    (\( x, m ) acc ->
                        ( InferExp.Call
                            ( InferExp.Call
                                ( InferExp.Name "(::)", m )
                                ( expression_ ( x, m ) )
                            , m
                            )
                            acc
                        , m
                        )
                    )
                    ( literal <| Type.list (Type.TAny -1), meta )

        ELambda (( EVariable [ only ], _ ) :: []) body ->
            ( InferExp.Lambda only (expression_ body), meta )

        ELambda (( EVariable [ first ], vmeta ) :: rest) body ->
            ( InferExp.Lambda first (expression_ <| ( ELambda rest body, vmeta )), meta )

        -- Aplication
        EApplication l r ->
            ( InferExp.Call (expression_ l) (expression_ r), meta )

        _ ->
            Debug.crash "Not implemented"


bindings :
    List ( AstMExp, AstMExp )
    -> List ( Name, InferExp.MExp )
bindings =
    List.map
        (\( ( l, _ ), r ) ->
            case l of
                EVariable [ name ] ->
                    ( name, expression_ r )

                e ->
                    Debug.crash (toString e ++ " is not a supported variable definition yet")
        )


literal : Type.RawType -> InferExp.Expression
literal t =
    InferExp.Literal (unconstrained t)

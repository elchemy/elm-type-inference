module Ast.Translate exposing (expression)

import Ast.Common exposing (Literal(..), MPattern, Name)
import Ast.Expression as AstExp exposing (..)
import Ast.Identifiers exposing (AstExpression(..), AstMExp, generateExpressionIds)
import Infer.Expression as InferExp
import Infer.Type as Type exposing (Type, unconstrained)


type alias ExMeta =
    {}


expression : MExp -> InferExp.MExp
expression e =
    generateExpressionIds e |> expression_


expression_ : AstMExp -> InferExp.MExp
expression_ ( e, meta ) =
    case e of
        ELet bindingList body ->
            ( InferExp.Let (bindings bindingList) (expression_ body), meta )

        EVariable name ->
            ( InferExp.Name name, meta )

        ELiteral l ->
            case l of
                Integer _ ->
                    ( literal Type.int, meta )

                Float _ ->
                    ( literal Type.float, meta )

                String _ ->
                    ( literal Type.string, meta )

                Character _ ->
                    ( literal Type.char, meta )

        EList elems ->
            elems
                |> List.foldr
                    (\( x, m ) acc ->
                        ( InferExp.Call
                            ( InferExp.Call
                                ( InferExp.Name "::", m )
                                (expression_ ( x, m ))
                            , m
                            )
                            acc
                        , m
                        )
                    )
                    ( literal <| Type.list (Type.TAny -1), meta )

        ELambda (( EVariable only, _ ) :: []) body ->
            ( InferExp.Lambda only (expression_ body), meta )

        ELambda (( EVariable first, vmeta ) :: rest) body ->
            ( InferExp.Lambda first (expression_ <| ( ELambda rest body, vmeta )), meta )

        EApplication l r ->
            ( InferExp.Call (expression_ l) (expression_ r), meta )

        EBinOp ( EVariable opName, opMeta ) l r ->
            expression_
                ( EApplication
                    ( EApplication
                        ( EVariable opName, opMeta )
                        l
                    , opMeta
                    )
                    r
                , meta
                )

        EIf ( c, cm ) ( t, tm ) ( e, em ) ->
            ( InferExp.Call
                ( InferExp.Call
                    ( InferExp.Call
                        ( InferExp.Name "if", cm )
                        (expression_ ( c, cm ))
                    , tm
                    )
                    (expression_ ( t, tm ))
                , em
                )
                (expression_ ( e, em ))
            , meta
            )

        ECase ( c, cm ) li ->
            let
                ( lefts, rights ) =
                    List.unzip li
            in
            expression_
                ( EApplication
                    ( EApplication
                        ( EApplication ( EVariable "case", meta ) ( c, cm )
                        , meta
                        )
                        ( EList lefts, meta )
                    , meta
                    )
                    ( EList rights, meta )
                , meta
                )

        _ ->
            Debug.crash "Not implemented"


gatherArgs_ :
    ( AstExpression, a )
    -> ( Name, List AstMExp )
    -> ( Name, List AstMExp )
gatherArgs_ ( a, _ ) ( accName, accArgs ) =
    case a of
        EApplication ( EVariable bindingName, _ ) ( EVariable varName, varMeta ) ->
            ( bindingName, ( EVariable varName, varMeta ) :: accArgs )

        EApplication ( EApplication l r, appMeta ) ( EVariable varName, varMeta ) ->
            gatherArgs_ ( EApplication l r, appMeta ) ( accName, ( EVariable varName, varMeta ) :: accArgs )

        _ ->
            Debug.crash <| "Cannot gather args for " ++ toString a


gatherArgs : AstMExp -> ( Name, List AstMExp )
gatherArgs e =
    gatherArgs_ e ( "", [] )


bindings :
    List ( AstMExp, AstMExp )
    -> List ( Name, InferExp.MExp )
bindings =
    List.map
        (\( ( l, m ), r ) ->
            case l of
                EVariable name ->
                    ( name, expression_ r )

                EApplication _ _ ->
                    gatherArgs ( l, m )
                        |> (\( name, args ) ->
                                ( name, expression_ ( ELambda args r, m ) )
                           )

                e ->
                    Debug.crash (toString e ++ " is not a supported variable definition yet")
        )


literal : Type.RawType -> InferExp.Expression
literal t =
    InferExp.Literal (unconstrained t)

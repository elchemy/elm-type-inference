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
                                (expression_ ( x, m ))
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

        EApplication l r ->
            ( InferExp.Call (expression_ l) (expression_ r), meta )

        EBinOp ( EVariable [ opName ], opMeta ) l r ->
            expression_
                ( EApplication
                    ( EApplication
                        ( EVariable [ "(" ++ opName ++ ")" ], opMeta )
                        l
                    , opMeta
                    )
                    r
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
        EApplication ( EVariable [ bindingName ], _ ) ( EVariable [ varName ], varMeta ) ->
            ( bindingName, ( EVariable [ varName ], varMeta ) :: accArgs )

        EApplication ( EApplication l r, appMeta ) ( EVariable [ varName ], varMeta ) ->
            gatherArgs_ ( EApplication l r, appMeta ) ( accName, ( EVariable [ varName ], varMeta ) :: accArgs )

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
                EVariable [ name ] ->
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

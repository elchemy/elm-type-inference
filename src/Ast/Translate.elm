module Ast.Translate exposing (expression, pattern_)

import Ast.Common exposing (Literal(..), Name)
import Ast.Expression as AstExp exposing (..)
import Ast.Identifiers exposing (AstExpression(..), AstMExp, AstPattern(..), MPattern, generateExpressionIds)
import Infer.Expression as InferExp
import Infer.Type as Type exposing (Type, unconstrained)


pattern_ : MPattern -> InferExp.MPattern
pattern_ ( p, meta ) =
    case p of
        APWild ->
            ( InferExp.PWild, meta )

        APVariable n ->
            ( InferExp.PName n, meta )

        APConstructor n ->
            ( InferExp.PName n, meta )

        APLiteral l ->
            case l of
                Integer _ ->
                    ( literalPattern Type.int, meta )

                Float _ ->
                    ( literalPattern Type.float, meta )

                String _ ->
                    ( literalPattern Type.string, meta )

                Character _ ->
                    ( literalPattern Type.char, meta )

        APTuple elems ->
            ( InferExp.PTuple <| List.map pattern_ elems, meta )

        APCons head tail ->
            ( InferExp.PCons (pattern_ head) (pattern_ tail), meta )

        APList elems ->
            ( InferExp.PList <| List.map pattern_ elems, meta )

        APRecord names ->
            ( InferExp.PRecord (List.map Tuple.first names), meta )

        APAs body name ->
            ( InferExp.PAs (pattern_ body) name, meta )

        APApplication left right ->
            ( InferExp.PApplication (pattern_ left) (pattern_ right), meta )


expression : MExp -> InferExp.MExp
expression e =
    generateExpressionIds e |> expression_


expression_ : AstMExp -> InferExp.MExp
expression_ ( e, meta ) =
    case e of
        ELet bindingList body ->
            ( InferExp.Let (bindings bindingList) (expression_ body), meta )

        ECase exp bindingList ->
            ( InferExp.Case (expression_ exp) (bindings bindingList), meta )

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

        ELambda (only :: []) body ->
            ( InferExp.Lambda (pattern_ only) (expression_ body), meta )

        ELambda (first :: rest) body ->
            ( InferExp.Lambda (pattern_ first) (expression_ <| ( ELambda rest body, meta )), meta )

        EApplication l r ->
            ( InferExp.Call (expression_ l) (expression_ r), meta )

        EBinOp (( _, opMeta ) as op) l r ->
            expression_ ( EApplication ( EApplication op l, opMeta ) r, meta )

        EIf c t e ->
            List.foldl
                (\( part, partMeta ) acc ->
                    ( InferExp.Call acc (expression_ ( part, partMeta )), partMeta )
                )
                ( InferExp.Name "if", meta )
                [ c, t, e ]

        _ ->
            Debug.crash "Not implemented"


literal : Type.RawType -> InferExp.Expression
literal t =
    InferExp.Literal (unconstrained t)


literalPattern : Type.RawType -> InferExp.Pattern
literalPattern t =
    InferExp.PLiteral (unconstrained t)


bindings : List ( MPattern, AstMExp ) -> List ( InferExp.MPattern, InferExp.MExp )
bindings =
    List.map (\( p, e ) -> ( pattern_ p, expression_ e ))

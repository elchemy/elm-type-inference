module Helpers exposing (ExpressionSansMeta(..), checkLetCase, checkRecordsIds, dropMeta, expressionHasUniqueIds, expressionHasUniqueIds_, fakeMeta, hasUniqueId_, listHasUniqueIds, listHasUniqueIds_, patternHasUniqueIds_, statementHasUniqueIds, statementHasUniqueIds_, statementsHaveUniqueIds)

import Ast.Common exposing (WithMeta)
import Ast.Identifiers exposing (..)
import Infer.Expression exposing (..)
import Infer.Type exposing (Type)
import Set exposing (Set)


type ExpressionSansMeta
    = LiteralSM Type
    | LambdaSM String ExpressionSansMeta
    | CallSM ExpressionSansMeta ExpressionSansMeta
    | LetSM (List ( String, ExpressionSansMeta )) ExpressionSansMeta
    | NameSM String
    | SpySM ExpressionSansMeta Int


dropMeta : MExp -> ExpressionSansMeta
dropMeta ( e, _ ) =
    case e of
        Literal t ->
            LiteralSM t

        Lambda s exp ->
            LambdaSM s (dropMeta exp)

        Call e1 e2 ->
            CallSM (dropMeta e1) (dropMeta e2)

        Let list expression ->
            LetSM
                (List.map (\( s, exp ) -> ( s, dropMeta exp )) list)
                (dropMeta expression)

        Name s ->
            NameSM s

        Spy exp i ->
            SpySM (dropMeta exp) i


fakeMeta : ExpressionSansMeta -> MExp
fakeMeta e =
    let
        addMeta x =
            ( x, { id = -1, line = -1, column = -1 } )
    in
    case e of
        LiteralSM t ->
            addMeta <| Literal t

        LambdaSM s exp ->
            addMeta <| Lambda s (fakeMeta exp)

        CallSM e1 e2 ->
            addMeta <| Call (fakeMeta e1) (fakeMeta e2)

        LetSM list expression ->
            addMeta <| Let (List.map (\( s, exp ) -> ( s, fakeMeta exp )) list) (fakeMeta expression)

        NameSM s ->
            addMeta <| Name s

        SpySM exp i ->
            addMeta <| Spy (fakeMeta exp) i


checkRecordsIds : List ( MName, AstMExp ) -> Set Id -> Maybe (Set Id)
checkRecordsIds records ids =
    List.unzip records
        |> (\( names, exps ) ->
                listHasUniqueIds_ hasUniqueId_ names ids
                    |> Maybe.andThen
                        (listHasUniqueIds_ expressionHasUniqueIds_ exps)
           )


checkLetCase : List ( MPattern, AstMExp ) -> AstMExp -> Set Id -> Maybe (Set Id)
checkLetCase li exp ids =
    let
        ( patterns, exps ) =
            List.unzip li
    in
    expressionHasUniqueIds_ exp ids
        |> Maybe.andThen (listHasUniqueIds_ patternHasUniqueIds_ patterns)
        |> Maybe.andThen (listHasUniqueIds_ expressionHasUniqueIds_ exps)


expressionHasUniqueIds_ : AstMExp -> Set Id -> Maybe (Set Id)
expressionHasUniqueIds_ (( e, { id } ) as whole) ids =
    hasUniqueId_ whole ids
        |> (Maybe.andThen <|
                \newIds ->
                    case e of
                        EList li ->
                            listHasUniqueIds_ expressionHasUniqueIds_ li ids

                        ETuple li ->
                            listHasUniqueIds_ expressionHasUniqueIds_ li ids

                        EAccess exp li ->
                            expressionHasUniqueIds_ exp ids |> Maybe.andThen (listHasUniqueIds_ hasUniqueId_ li)

                        ERecord records ->
                            checkRecordsIds records ids

                        ERecordUpdate n records ->
                            hasUniqueId_ n ids
                                |> Maybe.andThen (checkRecordsIds records)

                        EIf e1 e2 e3 ->
                            expressionHasUniqueIds_ e1 ids
                                |> Maybe.andThen (expressionHasUniqueIds_ e2)
                                |> Maybe.andThen (expressionHasUniqueIds_ e3)

                        ELet li exp ->
                            checkLetCase li exp ids

                        ECase exp li ->
                            checkLetCase li exp ids

                        ELambda li exp ->
                            expressionHasUniqueIds_ exp ids |> Maybe.andThen (listHasUniqueIds_ patternHasUniqueIds_ li)

                        EApplication e1 e2 ->
                            expressionHasUniqueIds_ e1 ids
                                |> Maybe.andThen (expressionHasUniqueIds_ e2)

                        EBinOp e1 e2 e3 ->
                            expressionHasUniqueIds_ e1 ids
                                |> Maybe.andThen (expressionHasUniqueIds_ e2)
                                |> Maybe.andThen (expressionHasUniqueIds_ e3)

                        EExternal _ exp ->
                            expressionHasUniqueIds_ exp ids

                        _ ->
                            Just newIds
           )


listHasUniqueIds_ :
    (WithMeta a Identifier -> Set Id -> Maybe (Set Id))
    -> List (WithMeta a Identifier)
    -> Set Id
    -> Maybe (Set Id)
listHasUniqueIds_ checker list ids =
    case list of
        [] ->
            Just ids

        exp :: rest ->
            case checker exp ids of
                Nothing ->
                    Nothing

                Just newIds ->
                    listHasUniqueIds_ checker rest newIds


listHasUniqueIds : (WithMeta a Identifier -> Set Id -> Maybe (Set Id)) -> List (WithMeta a Identifier) -> Bool
listHasUniqueIds checker l =
    case listHasUniqueIds_ checker l Set.empty of
        Nothing ->
            False

        _ ->
            True


expressionHasUniqueIds : AstMExp -> Bool
expressionHasUniqueIds exp =
    case expressionHasUniqueIds_ exp Set.empty of
        Nothing ->
            False

        _ ->
            True


hasUniqueId_ : WithMeta a Identifier -> Set Id -> Maybe (Set Id)
hasUniqueId_ ( _, { id } ) ids =
    if Set.member id ids then
        Nothing

    else
        Just (Set.insert id ids)


patternHasUniqueIds_ : MPattern -> Set Id -> Maybe (Set Id)
patternHasUniqueIds_ (( p, { id } ) as whole) ids =
    hasUniqueId_ whole ids
        |> (Maybe.andThen <|
                \newIds ->
                    case p of
                        APTuple li ->
                            listHasUniqueIds_ patternHasUniqueIds_ li newIds

                        APCons head tail ->
                            patternHasUniqueIds_ head newIds

                        APList li ->
                            listHasUniqueIds_ patternHasUniqueIds_ li newIds

                        APRecord names ->
                            listHasUniqueIds_ hasUniqueId_ names newIds

                        APAs pattern _ ->
                            patternHasUniqueIds_ pattern newIds

                        APApplication left right ->
                            patternHasUniqueIds_ left newIds |> Maybe.andThen (patternHasUniqueIds_ right)

                        _ ->
                            Just <| Set.insert id ids
           )


statementHasUniqueIds_ :
    ( AstStatement, Ast.Common.Located Identifier )
    -> Set Id
    -> Maybe (Set Id)
statementHasUniqueIds_ (( s, { id } ) as whole) ids =
    hasUniqueId_ whole ids
        |> (Maybe.andThen <|
                \newIds ->
                    case s of
                        SPortDeclaration _ _ exp ->
                            expressionHasUniqueIds_ exp newIds

                        SFunctionDeclaration pattern exp ->
                            patternHasUniqueIds_ pattern newIds
                                |> Maybe.andThen (expressionHasUniqueIds_ exp)

                        _ ->
                            Just newIds
           )


statementHasUniqueIds : MStatement -> Bool
statementHasUniqueIds s =
    case statementHasUniqueIds_ s Set.empty of
        Nothing ->
            False

        _ ->
            True


statementsHaveUniqueIds : List MStatement -> Bool
statementsHaveUniqueIds =
    listHasUniqueIds statementHasUniqueIds_

module Infer.Expression exposing
    ( Expression(..), MExp, AstMExp, AstExpression(..), Id, MName
    , generateIds
    , generateListIds
    )

{-| #


# Types

@docs Expression, MExp, AstMExp, AstExpression, Id, MName


# functions

@docs generateIds, generateListIds

-}

import Ast.Expression
import Ast.Common exposing (Column, Line, Name, WithMeta)
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


{-| Unique identifier for an expression
-}
type alias Id =
    Int


type alias Identified x =
    { x | id : Id }


type alias Identifier =
    Identified {}


{-| Expression enhanced with metadata containing id, line and column
-}
type alias MExp =
    WithMeta Expression Identifier


{-| Ast.Expression.MExp with an identifier
-}
type alias AstMExp =
    WithMeta AstExpression Identifier


{-| A name with an identifier
-}
type alias MName =
    WithMeta Name Identifier


{-| Ast.Expression.Expression analogue containing AstMExp
-}
type AstExpression
    = ECharacter Char
    | EString String
    | EInteger Int
    | EFloat Float
    | EVariable (List Name)
    | EList (List AstMExp)
    | ETuple (List AstMExp)
    | EAccess AstMExp (List MName)
    | EAccessFunction Name
    | ERecord (List ( MName, AstMExp ))
    | ERecordUpdate MName (List ( MName, AstMExp ))
    | EIf AstMExp AstMExp AstMExp
    | ELet (List ( AstMExp, AstMExp )) AstMExp
    | ECase AstMExp (List ( AstMExp, AstMExp ))
    | ELambda (List AstMExp) AstMExp
    | EApplication AstMExp AstMExp
    | EBinOp AstMExp AstMExp AstMExp


{-| Extract Id from an expression enhanced with metadata
-}
getId : WithMeta x (Identified y) -> Id
getId ( _, { id } ) =
    id


genNameListIds : Id -> List Ast.Common.MName -> ( Id, List MName )
genNameListIds newId =
    List.foldr (\( n, { line, column } ) ( accId, acc ) -> ( accId + 1, ( n, { id = accId, line = line, column = column } ) :: acc )) ( newId + 1, [] )


genListIds : Id -> List Ast.Expression.MExp -> ( Id, List AstMExp )
genListIds newId =
    List.foldr (\x ( accId, acc ) -> generateIds_ accId x |> (\( maxId, exp ) -> ( maxId, exp :: acc ))) ( newId + 1, [] )


genCoupleIds : Id -> ( Ast.Expression.MExp, Ast.Expression.MExp ) -> ( Id, AstMExp, AstMExp )
genCoupleIds newId ( e1, e2 ) =
    let
        ( newerId, newE1 ) =
            generateIds_ newId e1

        ( maxId, newE2 ) =
            generateIds_ newerId e2
    in
    ( maxId, newE1, newE2 )


genTripleIds :
    Id
    -> ( Ast.Expression.MExp, Ast.Expression.MExp, Ast.Expression.MExp )
    -> ( Id, AstMExp, AstMExp, AstMExp )
genTripleIds newId ( e1, e2, e3 ) =
    let
        ( newerId, newE1, newE2 ) =
            genCoupleIds newId ( e1, e2 )

        ( maxId, newE3 ) =
            generateIds_ newerId e3
    in
    ( maxId, newE1, newE2, newE3 )


genRecordsIds : Id -> List ( Ast.Common.MName, Ast.Expression.MExp ) -> ( Id, List ( MName, AstMExp ) )
genRecordsIds newId records =
    let
        ( names, exps ) =
            List.unzip records

        ( namesId, newNames ) =
            genNameListIds newId names

        ( expsId, newExps ) =
            genListIds namesId exps
    in
    ( expsId, List.map2 (,) newNames newExps )


genLetCase : Id -> List ( Ast.Expression.MExp, Ast.Expression.MExp ) -> Ast.Expression.MExp -> ( Id, List ( AstMExp, AstMExp ), AstMExp )
genLetCase newId li exp =
    let
        ( newerId, newExp ) =
            generateIds_ newId exp

        ( li1, li2 ) =
            List.unzip li

        ( li1Id, newLi1 ) =
            genListIds newerId li1

        ( li2Id, newLi2 ) =
            genListIds li1Id li2
    in
    ( li2Id, List.map2 (\x y -> ( x, y )) newLi1 newLi2, newExp )


generateIds_ : Int -> Ast.Expression.MExp -> ( Int, AstMExp )
generateIds_ newId ( e, { line, column } ) =
    case e of
        Ast.Expression.Character c ->
            ( newId + 1, ( ECharacter c, { id = newId, line = line, column = column } ) )

        Ast.Expression.String s ->
            ( newId + 1, ( EString s, { id = newId, line = line, column = column } ) )

        Ast.Expression.Integer i ->
            ( newId + 1, ( EInteger i, { id = newId, line = line, column = column } ) )

        Ast.Expression.Float f ->
            ( newId + 1, ( EFloat f, { id = newId, line = line, column = column } ) )

        Ast.Expression.Variable v ->
            ( newId + 1, ( EVariable v, { id = newId, line = line, column = column } ) )

        Ast.Expression.List li ->
            let
                ( maxId, exp ) =
                    genListIds (newId + 1) li
            in
            ( maxId, ( EList exp, { id = newId, line = line, column = column } ) )

        Ast.Expression.Tuple li ->
            let
                ( maxId, exp ) =
                    genListIds (newId + 1) li
            in
            ( maxId, ( ETuple exp, { id = newId, line = line, column = column } ) )

        Ast.Expression.Access exp li ->
            let
                ( listId, newLi ) =
                    genNameListIds (newId + 1) li

                ( maxId, newExp ) =
                    generateIds_ listId exp
            in
            ( maxId, ( EAccess newExp newLi, { id = newId, line = line, column = column } ) )

        Ast.Expression.AccessFunction f ->
            ( newId + 1, ( EAccessFunction f, { id = newId, line = line, column = column } ) )

        Ast.Expression.Record records ->
            let
                ( maxId, newRecords ) =
                    genRecordsIds (newId + 1) records
            in
            ( maxId, ( ERecord newRecords, { id = newId, line = line, column = column } ) )

        Ast.Expression.RecordUpdate name records ->
            let
                ( recordsId, newRecords ) =
                    genRecordsIds (newId + 1) records

                ( nameN, nameMeta ) =
                    name

                newName =
                    ( nameN, { line = nameMeta.line, column = nameMeta.column, id = recordsId } )

                maxId =
                    recordsId + 1
            in
            ( maxId, ( ERecordUpdate newName newRecords, { id = newId, line = line, column = column } ) )

        Ast.Expression.If e1 e2 e3 ->
            let
                ( maxId, newE1, newE2, newE3 ) =
                    genTripleIds (newId + 1) ( e1, e2, e3 )
            in
            ( maxId, ( EIf newE1 newE2 newE3, { id = newId, line = line, column = column } ) )

        Ast.Expression.Let li exp ->
            let
                ( maxId, newLi, newExp ) =
                    genLetCase (newId + 1) li exp
            in
            ( maxId, ( ELet newLi newExp, { id = newId, line = line, column = column } ) )

        Ast.Expression.Case exp li ->
            let
                ( maxId, newLi, newExp ) =
                    genLetCase (newId + 1) li exp
            in
            ( maxId, ( ECase newExp newLi, { id = newId, line = line, column = column } ) )

        Ast.Expression.Lambda li exp ->
            let
                ( newerId, newExp ) =
                    generateIds_ (newId + 1) exp

                ( maxId, newLi ) =
                    genListIds newerId li
            in
            ( maxId, ( ELambda newLi newExp, { id = newId, line = line, column = column } ) )

        Ast.Expression.Application e1 e2 ->
            let
                ( maxId, newE1, newE2 ) =
                    genCoupleIds (newId + 1) ( e1, e2 )
            in
            ( maxId, ( EApplication newE1 newE2, { id = newId, line = line, column = column } ) )

        Ast.Expression.BinOp e1 e2 e3 ->
            let
                ( maxId, newE1, newE2, newE3 ) =
                    genTripleIds (newId + 1) ( e1, e2, e3 )
            in
            ( maxId, ( EBinOp newE1 newE2 newE3, { id = newId, line = line, column = column } ) )


{-| Generates Ids for nodes in MExp
which are unique within the resulting tree
-}
generateIds : Ast.Expression.MExp -> AstMExp
generateIds =
    Tuple.second << generateIds_ 0


{-| Generates unique Ids for a list of expressions
-}
generateListIds : List Ast.Expression.MExp -> List AstMExp
generateListIds =
    Tuple.second
        << List.foldr
            (\x ( maxId, acc ) ->
                generateIds_ maxId x
                    |> (\( newMaxId, e ) -> ( newMaxId, e :: acc ))
            )
            ( 0, [] )

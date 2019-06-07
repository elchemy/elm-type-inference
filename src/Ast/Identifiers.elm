module Ast.Identifiers exposing
    ( AstExpression(..)
    , AstMExp
    , AstPattern(..)
    , AstStatement(..)
    , Id
    , Identified
    , Identifier
    , MName
    , MPattern
    , MStatement
    , generateExpressionIds
    , generateExpressionIds_
    , generateListIds
    , generateNameId
    , generatePatternId
    , generateStatementId
    , generateStatementsIds
    , getId
    )

import Ast.BinOp exposing (Assoc)
import Ast.Common as Ast
import Ast.Expression exposing (..)
import Ast.Statement exposing (ExportSet, Statement, StatementBase(..), Type)


{-| Unique identifier for an expression
-}
type alias Id =
    Int


type alias Identified x =
    { x | id : Id }


type alias Identifier =
    Identified {}


{-| Ast.Expression.MExp with an identifier
-}
type alias AstMExp =
    Ast.WithMeta AstExpression Identifier


{-| A name with an identifier
-}
type alias MName =
    Ast.WithMeta Ast.Name Identifier


{-| Pattern with an identifier
-}
type alias MPattern =
    Ast.WithMeta AstPattern Identifier


{-| Statement with an identifier
-}
type alias MStatement =
    Ast.WithMeta AstStatement Identifier


{-| Ast.Common.Pattern analague containing MPattern
-}
type AstPattern
    = APWild
    | APVariable Ast.Name
    | APConstructor Ast.Name
    | APLiteral Ast.Literal
    | APTuple (List MPattern)
    | APCons MPattern MPattern
    | APList (List MPattern)
    | APRecord (List MName)
    | APAs MPattern Ast.Name
    | APApplication MPattern MPattern


{-| Ast.Expression.Expression analogue containing AstMExp
-}
type AstExpression
    = ELiteral Ast.Literal
    | EVariable Ast.Name
    | EConstructor Ast.Name
    | EExternal (List Ast.Name) AstMExp
    | EList (List AstMExp)
    | ETuple (List AstMExp)
    | EAccess AstMExp (List MName)
    | EAccessFunction Ast.Name
    | ERecord (List ( MName, AstMExp ))
    | ERecordUpdate MName (List ( MName, AstMExp ))
    | EIf AstMExp AstMExp AstMExp
    | ELet (List ( MPattern, AstMExp )) AstMExp
    | ECase AstMExp (List ( MPattern, AstMExp ))
    | ELambda (List MPattern) AstMExp
    | EApplication AstMExp AstMExp
    | EBinOp AstMExp AstMExp AstMExp


{-| Ast.Statement.Statement analogue containing MStatement
-}
type AstStatement
    = SModuleDeclaration Ast.ModuleName ExportSet
    | SPortModuleDeclaration Ast.ModuleName ExportSet
    | SEffectModuleDeclaration Ast.ModuleName (List ( Ast.Name, Ast.Name )) ExportSet
    | SImportStatement Ast.ModuleName (Maybe Ast.Alias) (Maybe ExportSet)
    | STypeAliasDeclaration Type Type
    | STypeDeclaration Type (List Type)
    | SPortTypeDeclaration Ast.Name Type
    | SPortDeclaration Ast.Name (List Ast.Name) AstMExp
    | SFunctionTypeDeclaration Ast.Name Type
    | SFunctionDeclaration MPattern AstMExp
    | SInfixDeclaration Assoc Int Ast.Name
    | SComment String


{-| Extract Id from an expression enhanced with metadata
-}
getId : Ast.WithMeta x (Identified y) -> Id
getId ( _, { id } ) =
    id


generateNameId : Id -> Ast.MName -> ( Id, MName )
generateNameId newId ( name, { line, column } ) =
    ( newId + 1, ( name, { id = newId, line = line, column = column } ) )


generateListIds : (Id -> Ast.WithMeta a {} -> ( Id, Ast.WithMeta b Identifier )) -> Id -> List (Ast.WithMeta a {}) -> ( Id, List (Ast.WithMeta b Identifier) )
generateListIds generator newId =
    List.foldr (\x ( accId, acc ) -> generator accId x |> (\( maxId, exp ) -> ( maxId, exp :: acc )))
        ( newId + 1, [] )


generateCoupleIds : Id -> ( MExp, MExp ) -> ( Id, AstMExp, AstMExp )
generateCoupleIds newId ( e1, e2 ) =
    let
        ( newerId, newE1 ) =
            generateExpressionIds_ newId e1

        ( maxId, newE2 ) =
            generateExpressionIds_ newerId e2
    in
    ( maxId, newE1, newE2 )


genTripleIds :
    Id
    -> ( MExp, MExp, MExp )
    -> ( Id, AstMExp, AstMExp, AstMExp )
genTripleIds newId ( e1, e2, e3 ) =
    let
        ( newerId, newE1, newE2 ) =
            generateCoupleIds newId ( e1, e2 )

        ( maxId, newE3 ) =
            generateExpressionIds_ newerId e3
    in
    ( maxId, newE1, newE2, newE3 )


genRecordsIds : Id -> List ( Ast.MName, MExp ) -> ( Id, List ( MName, AstMExp ) )
genRecordsIds newId records =
    let
        ( names, exps ) =
            List.unzip records

        ( namesId, newNames ) =
            generateListIds generateNameId newId names

        ( expsId, newExps ) =
            generateListIds generateExpressionIds_ namesId exps
    in
    ( expsId, List.map2 (,) newNames newExps )


genLetCase : Id -> List ( Ast.MPattern, MExp ) -> MExp -> ( Id, List ( MPattern, AstMExp ), AstMExp )
genLetCase newId li exp =
    let
        ( patterns, exps ) =
            List.unzip li

        ( expId, newExp ) =
            generateExpressionIds_ newId exp

        ( patternsId, newPatterns ) =
            generateListIds generatePatternId expId patterns

        ( maxId, newExps ) =
            generateListIds generateExpressionIds_ patternsId exps
    in
    ( maxId, List.map2 (,) newPatterns newExps, newExp )


generatePatternId : Int -> Ast.MPattern -> ( Int, MPattern )
generatePatternId newId ( pattern, { line, column } ) =
    case pattern of
        Ast.PWild ->
            ( newId + 1, ( APWild, { id = newId, line = line, column = column } ) )

        Ast.PVariable n ->
            ( newId + 1, ( APVariable n, { id = newId, line = line, column = column } ) )

        Ast.PConstructor n ->
            ( newId + 1, ( APConstructor n, { id = newId, line = line, column = column } ) )

        Ast.PLiteral l ->
            ( newId + 1, ( APLiteral l, { id = newId, line = line, column = column } ) )

        Ast.PTuple elements ->
            let
                ( maxId, newElements ) =
                    generateListIds generatePatternId (newId + 1) elements
            in
            ( maxId, ( APTuple newElements, { id = newId, line = line, column = column } ) )

        Ast.PCons head tail ->
            let
                ( headId, newHead ) =
                    generatePatternId (newId + 1) head

                ( tailId, newTail ) =
                    generatePatternId headId tail
            in
            ( tailId, ( APCons newHead newTail, { id = newId, line = line, column = column } ) )

        Ast.PList elements ->
            let
                ( maxId, newElements ) =
                    generateListIds generatePatternId (newId + 1) elements
            in
            ( maxId, ( APList newElements, { id = newId, line = line, column = column } ) )

        Ast.PRecord names ->
            let
                ( namesId, newNames ) =
                    generateListIds generateNameId (newId + 1) names
            in
            ( namesId, ( APRecord newNames, { id = newId, line = line, column = column } ) )

        Ast.PAs pattern name ->
            let
                ( maxId, newPattern ) =
                    generatePatternId (newId + 1) pattern
            in
            ( maxId, ( APAs newPattern name, { id = newId, line = line, column = column } ) )

        Ast.PApplication left right ->
            let
                ( leftId, newLeft ) =
                    generatePatternId (newId + 1) left

                ( rightId, newRight ) =
                    generatePatternId leftId right
            in
            ( rightId, ( APApplication newLeft newRight, { id = newId, line = line, column = column } ) )


generateExpressionIds_ : Int -> MExp -> ( Int, AstMExp )
generateExpressionIds_ newId ( e, { line, column } ) =
    case e of
        Literal l ->
            ( newId + 1, ( ELiteral l, { id = newId, line = line, column = column } ) )

        Variable v ->
            ( newId + 1, ( EVariable v, { id = newId, line = line, column = column } ) )

        List li ->
            let
                ( maxId, exp ) =
                    generateListIds generateExpressionIds_ (newId + 1) li
            in
            ( maxId, ( EList exp, { id = newId, line = line, column = column } ) )

        Tuple li ->
            let
                ( maxId, exp ) =
                    generateListIds generateExpressionIds_ (newId + 1) li
            in
            ( maxId, ( ETuple exp, { id = newId, line = line, column = column } ) )

        Access exp li ->
            let
                ( listId, newLi ) =
                    generateListIds generateNameId (newId + 1) li

                ( maxId, newExp ) =
                    generateExpressionIds_ listId exp
            in
            ( maxId, ( EAccess newExp newLi, { id = newId, line = line, column = column } ) )

        AccessFunction f ->
            ( newId + 1, ( EAccessFunction f, { id = newId, line = line, column = column } ) )

        Record records ->
            let
                ( maxId, newRecords ) =
                    genRecordsIds (newId + 1) records
            in
            ( maxId, ( ERecord newRecords, { id = newId, line = line, column = column } ) )

        RecordUpdate name records ->
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

        If e1 e2 e3 ->
            let
                ( maxId, newE1, newE2, newE3 ) =
                    genTripleIds (newId + 1) ( e1, e2, e3 )
            in
            ( maxId, ( EIf newE1 newE2 newE3, { id = newId, line = line, column = column } ) )

        Let li exp ->
            let
                ( maxId, newLi, newExp ) =
                    genLetCase (newId + 1) li exp
            in
            ( maxId, ( ELet newLi newExp, { id = newId, line = line, column = column } ) )

        Case exp li ->
            let
                ( maxId, newLi, newExp ) =
                    genLetCase (newId + 1) li exp
            in
            ( maxId, ( ECase newExp newLi, { id = newId, line = line, column = column } ) )

        Lambda args exp ->
            let
                ( expId, newExp ) =
                    generateExpressionIds_ (newId + 1) exp

                ( maxId, newArgs ) =
                    generateListIds generatePatternId expId args
            in
            ( maxId, ( ELambda newArgs newExp, { id = newId, line = line, column = column } ) )

        Application e1 e2 ->
            let
                ( maxId, newE1, newE2 ) =
                    generateCoupleIds (newId + 1) ( e1, e2 )
            in
            ( maxId, ( EApplication newE1 newE2, { id = newId, line = line, column = column } ) )

        BinOp e1 e2 e3 ->
            let
                ( maxId, newE1, newE2, newE3 ) =
                    genTripleIds (newId + 1) ( e1, e2, e3 )
            in
            ( maxId, ( EBinOp newE1 newE2 newE3, { id = newId, line = line, column = column } ) )

        Constructor n ->
            ( newId + 1, ( EConstructor n, { id = newId, line = line, column = column } ) )

        External li exp ->
            let
                ( expId, newExp ) =
                    generateExpressionIds_ (newId + 1) exp
            in
            ( expId, ( EExternal li newExp, { id = newId, line = line, column = column } ) )


{-| Generates Ids for nodes in MExp
which are unique within the resulting tree
-}
generateExpressionIds : MExp -> AstMExp
generateExpressionIds =
    Tuple.second << generateExpressionIds_ 0


generateStatementId : Id -> Statement -> ( Id, MStatement )
generateStatementId newId ( statement, { line, column } ) =
    case statement of
        ModuleDeclaration n s ->
            ( newId + 1, ( SModuleDeclaration n s, { id = newId, line = line, column = column } ) )

        PortModuleDeclaration n s ->
            ( newId + 1, ( SPortModuleDeclaration n s, { id = newId, line = line, column = column } ) )

        EffectModuleDeclaration n li s ->
            ( newId + 1, ( SEffectModuleDeclaration n li s, { id = newId, line = line, column = column } ) )

        ImportStatement n a s ->
            ( newId + 1, ( SImportStatement n a s, { id = newId, line = line, column = column } ) )

        TypeAliasDeclaration n a ->
            ( newId + 1, ( STypeAliasDeclaration n a, { id = newId, line = line, column = column } ) )

        TypeDeclaration n li ->
            ( newId + 1, ( STypeDeclaration n li, { id = newId, line = line, column = column } ) )

        PortTypeDeclaration n t ->
            ( newId + 1, ( SPortTypeDeclaration n t, { id = newId, line = line, column = column } ) )

        PortDeclaration n li exp ->
            let
                ( maxId, newExp ) =
                    generateExpressionIds_ (newId + 1) exp
            in
            ( maxId, ( SPortDeclaration n li newExp, { id = newId, line = line, column = column } ) )

        FunctionTypeDeclaration n t ->
            ( newId + 1, ( SFunctionTypeDeclaration n t, { id = newId, line = line, column = column } ) )

        FunctionDeclaration pattern exp ->
            let
                ( patternId, newPattern ) =
                    generatePatternId (newId + 1) pattern

                ( maxId, newExp ) =
                    generateExpressionIds_ patternId exp
            in
            ( maxId, ( SFunctionDeclaration newPattern newExp, { id = newId, line = line, column = column } ) )

        InfixDeclaration a i n ->
            ( newId + 1, ( SInfixDeclaration a i n, { id = newId, line = line, column = column } ) )

        Comment s ->
            ( newId + 1, ( SComment s, { id = newId, line = line, column = column } ) )


{-| Generate Ids for a single statement which are unique in resulting structure
-}
generateStatementsIds : List Statement -> List MStatement
generateStatementsIds =
    Tuple.second << generateListIds generateStatementId 0

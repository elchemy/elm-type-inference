module Helpers exposing (ExpressionSansMeta(..), PatternSansMeta(..), addFakeMeta, arith, checkLetCase, checkRecordsIds, code, codeWithContext, dropMeta, dropPatternMeta, equal, expressionHasUniqueIds, expressionHasUniqueIds_, fakeMeta, fakePatternMeta, hasUniqueId_, if_, intLiteral, isTAny, listEnv, listHasUniqueIds, listHasUniqueIds_, minimizeTAny, patternHasUniqueIds_, statementHasUniqueIds, statementHasUniqueIds_, statementsHaveUniqueIds, stringLiteral, testEnv, tuple, typeOf, variablesDiffer)

import Ast
import Ast.Common exposing (Name, Pattern(..), WithMeta)
import Ast.Identifiers as Ast exposing (..)
import Ast.Statement as Statement
import Ast.Translate as Translate
import Dict
import Expect
import Infer
import Infer.DefaultEnvironment exposing (defaultEnvironment)
import Infer.Expression as Infer exposing (..)
import Infer.Monad as Infer
import Infer.Scheme exposing (Environment, generalize, instantiate)
import Infer.Type as Type exposing ((=>), Constraint(..), RawType(..), Type, unconstrained)
import List.Extra as List
import Set exposing (Set)


type PatternSansMeta
    = PWildSM
    | PNameSM Name
    | PLiteralSM Type
    | PTupleSM (List PatternSansMeta)
    | PConsSM PatternSansMeta PatternSansMeta
    | PListSM (List PatternSansMeta)
    | PRecordSM (List Name)
    | PAsSM PatternSansMeta Name
    | PApplicationSM PatternSansMeta PatternSansMeta


type ExpressionSansMeta
    = LiteralSM Type
    | LambdaSM PatternSansMeta ExpressionSansMeta
    | CallSM ExpressionSansMeta ExpressionSansMeta
    | LetSM (List ( PatternSansMeta, ExpressionSansMeta )) ExpressionSansMeta
    | CaseSM ExpressionSansMeta (List ( PatternSansMeta, ExpressionSansMeta ))
    | NameSM String
    | SpySM ExpressionSansMeta Int


dropMeta : MExp -> ExpressionSansMeta
dropMeta ( e, _ ) =
    case e of
        Literal t ->
            LiteralSM t

        Lambda s exp ->
            LambdaSM (dropPatternMeta s) (dropMeta exp)

        Call e1 e2 ->
            CallSM (dropMeta e1) (dropMeta e2)

        Let list expression ->
            LetSM
                (List.map (\( s, exp ) -> ( dropPatternMeta s, dropMeta exp )) list)
                (dropMeta expression)

        Case expression list ->
            CaseSM
                (dropMeta expression)
                (List.map (\( s, exp ) -> ( dropPatternMeta s, dropMeta exp )) list)

        Name s ->
            NameSM s

        Spy exp i ->
            SpySM (dropMeta exp) i


dropPatternMeta : Infer.MPattern -> PatternSansMeta
dropPatternMeta ( pattern, _ ) =
    case pattern of
        Infer.PWild ->
            PWildSM

        Infer.PName n ->
            PNameSM n

        Infer.PLiteral t ->
            PLiteralSM t

        Infer.PTuple li ->
            PTupleSM (List.map dropPatternMeta li)

        Infer.PCons head tail ->
            PConsSM (dropPatternMeta head) (dropPatternMeta tail)

        Infer.PList li ->
            PListSM (List.map dropPatternMeta li)

        Infer.PRecord names ->
            PRecordSM names

        Infer.PAs p n ->
            PAsSM (dropPatternMeta p) n

        Infer.PApplication left right ->
            PApplicationSM (dropPatternMeta left) (dropPatternMeta right)


addFakeMeta : a -> WithMeta a Identifier
addFakeMeta x =
    ( x, { id = -1, line = -1, column = -1 } )


fakePatternMeta : PatternSansMeta -> Infer.MPattern
fakePatternMeta p =
    case p of
        PWildSM ->
            addFakeMeta Infer.PWild

        PNameSM n ->
            addFakeMeta <| Infer.PName n

        PLiteralSM t ->
            addFakeMeta <| Infer.PLiteral t

        PTupleSM li ->
            addFakeMeta <| Infer.PTuple (List.map fakePatternMeta li)

        PConsSM head tail ->
            addFakeMeta <| Infer.PCons (fakePatternMeta head) (fakePatternMeta tail)

        PListSM li ->
            addFakeMeta <| Infer.PList (List.map fakePatternMeta li)

        PRecordSM names ->
            addFakeMeta <| Infer.PRecord names

        PAsSM p n ->
            addFakeMeta <| Infer.PAs (fakePatternMeta p) n

        PApplicationSM left right ->
            addFakeMeta <| Infer.PApplication (fakePatternMeta left) (fakePatternMeta right)


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
            addMeta <| Lambda (fakePatternMeta s) (fakeMeta exp)

        CallSM e1 e2 ->
            addMeta <| Call (fakeMeta e1) (fakeMeta e2)

        LetSM list expression ->
            addMeta <|
                Let
                    (List.map (\( s, exp ) -> ( fakePatternMeta s, fakeMeta exp )) list)
                    (fakeMeta expression)

        CaseSM expression list ->
            addMeta <|
                Case
                    (fakeMeta expression)
                    (List.map (\( s, exp ) -> ( fakePatternMeta s, fakeMeta exp )) list)

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


checkLetCase : List ( Ast.MPattern, AstMExp ) -> AstMExp -> Set Id -> Maybe (Set Id)
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


patternHasUniqueIds_ : Ast.MPattern -> Set Id -> Maybe (Set Id)
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


equal : a -> a -> () -> Expect.Expectation
equal a b =
    \() -> Expect.equal a b


variablesDiffer : Type -> Type -> () -> Expect.Expectation
variablesDiffer a b =
    \() ->
        Expect.true "parts other than type variables differ"
            (Type.unify a b
                |> Result.map (Dict.values >> List.all (Tuple.second >> isTAny))
                |> Result.withDefault False
            )


isTAny : RawType -> Bool
isTAny x =
    case x of
        TAny _ ->
            True

        _ ->
            False


stringLiteral : ExpressionSansMeta
stringLiteral =
    LiteralSM <| unconstrained Type.string


intLiteral : ExpressionSansMeta
intLiteral =
    LiteralSM <| unconstrained Type.int


if_ :
    ExpressionSansMeta
    -> ExpressionSansMeta
    -> ExpressionSansMeta
    -> ExpressionSansMeta
if_ a b c =
    CallSM (CallSM (CallSM (NameSM "if") a) b) c


testEnv : Environment
testEnv =
    Dict.fromList
        [ ( "if"
          , ( [ 1 ]
            , unconstrained <| Type.bool => TAny 1 => TAny 1 => TAny 1
            )
          )
        , ( "+", arith )
        , ( "tuple2"
          , ( [ 1, 2 ]
            , unconstrained <| TAny 1 => TAny 2 => TOpaque "Tuple" [ TAny 1, TAny 2 ]
            )
          )
        ]


tuple : ExpressionSansMeta -> ExpressionSansMeta -> ExpressionSansMeta
tuple a b =
    CallSM (CallSM (NameSM "tuple2") a) b


arith : ( List number, Type )
arith =
    ( [ 1 ], unconstrained <| TAny 1 => TAny 1 => TAny 1 )


minimizeTAny : RawType -> RawType
minimizeTAny t =
    let
        arrowToList a =
            case a of
                TArrow left right ->
                    left :: arrowToList right

                _ ->
                    [ a ]

        listToArrow l =
            case l of
                [] ->
                    Debug.crash "No empty lists"

                x :: [] ->
                    x

                x :: y :: [] ->
                    TArrow x y

                x :: y :: z ->
                    TArrow x (listToArrow (y :: z))

        typesList =
            arrowToList t

        minimizedIds =
            List.filterMap
                (\el ->
                    case el of
                        TAny id ->
                            Just id

                        _ ->
                            Nothing
                )
                typesList
                |> List.unique
                |> List.sort
                |> List.indexedMap (flip (,))
                |> Dict.fromList
    in
    typesList
        |> List.map
            (\el ->
                case el of
                    TAny id ->
                        case Dict.get id minimizedIds of
                            Nothing ->
                                el

                            Just newId ->
                                TAny newId

                    _ ->
                        el
            )
        |> listToArrow


typeOf : Environment -> MExp -> Result String Type
typeOf env exp =
    Infer.typeOf env exp
        |> Infer.finalValue 0
        |> Result.map Tuple.first


codeWithContext : Infer.Scheme.Environment -> String -> Result String RawType -> (() -> Expect.Expectation)
codeWithContext env input typeOrError =
    Ast.parse ("a = " ++ input)
        |> Result.mapError (always "Parsing failed")
        |> Result.andThen
            (\res ->
                case res of
                    ( _, _, [ ( Statement.FunctionDeclaration ( PVariable "a", _ ) body, _ ) ] ) ->
                        Ok body

                    _ ->
                        Err "Imparsable code"
            )
        |> Result.map Translate.expression
        |> Result.andThen (typeOf env)
        |> Result.map (Tuple.mapSecond minimizeTAny)
        |> equal (Result.map unconstrained typeOrError)


code : String -> Result String RawType -> (() -> Expect.Expectation)
code =
    codeWithContext defaultEnvironment


listEnv : Environment
listEnv =
    Dict.union defaultEnvironment <|
        Dict.fromList
            [ ( "foldr"
              , ( [ 0, 1 ]
                , unconstrained <| (TAny 0 => TAny 1 => TAny 1) => TAny 1 => Type.list (TAny 0) => TAny 1
                )
              )
            ]

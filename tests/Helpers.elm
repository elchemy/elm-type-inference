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
import State exposing (State)


type PatternSansMeta
    = PWildSM
    | PConstructorSM Name
    | PVariableSM Name
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

        Infer.PVariable n ->
            PVariableSM n

        Infer.PConstructor n ->
            PConstructorSM n

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


addFakeMeta : a -> Int -> WithMeta a Identifier
addFakeMeta x id =
    ( x, { id = id, line = -1, column = -1 } )


fakePatternMeta : PatternSansMeta -> State Int Infer.MPattern
fakePatternMeta p =
    case p of
        PWildSM ->
            freshInt |> State.map (addFakeMeta Infer.PWild)

        PVariableSM n ->
            freshInt |> State.map (addFakeMeta <| Infer.PVariable n)

        PConstructorSM n ->
            freshInt |> State.map (addFakeMeta <| Infer.PConstructor n)

        PLiteralSM t ->
            freshInt |> State.map (addFakeMeta <| Infer.PLiteral t)

        PTupleSM li ->
            let
                listMeta =
                    List.map fakePatternMeta li |> State.combine
            in
            State.map2 (\fresh newList -> addFakeMeta (Infer.PTuple newList) fresh) freshInt listMeta

        PConsSM head tail ->
            let
                headMeta =
                    fakePatternMeta head

                tailMeta =
                    fakePatternMeta tail
            in
            State.map3 (\fresh newHead newTail -> addFakeMeta (Infer.PCons newHead newTail) fresh) freshInt headMeta tailMeta

        PListSM li ->
            let
                listMeta =
                    List.map fakePatternMeta li |> State.combine
            in
            State.map2 (\fresh newList -> addFakeMeta (Infer.PList newList) fresh) freshInt listMeta

        PRecordSM names ->
            freshInt |> State.map (addFakeMeta <| Infer.PRecord names)

        PAsSM p n ->
            let
                patternMeta =
                    fakePatternMeta p
            in
            State.map2 (\fresh pattern -> addFakeMeta (Infer.PAs pattern n) fresh) freshInt patternMeta

        PApplicationSM left right ->
            let
                leftMeta =
                    fakePatternMeta left

                rightMeta =
                    fakePatternMeta right
            in
            State.map3 (\fresh newLeft newRight -> addFakeMeta (Infer.PApplication newLeft newRight) fresh) freshInt leftMeta rightMeta


freshInt : State Int Int
freshInt =
    State.advance (\state -> ( state, state + 1 ))


fakeMeta : ExpressionSansMeta -> MExp
fakeMeta =
    State.finalValue 0 << fakeMeta_


fakeMeta_ : ExpressionSansMeta -> State Int MExp
fakeMeta_ e =
    case e of
        LiteralSM t ->
            freshInt |> State.andThen (State.state << addFakeMeta (Literal t))

        LambdaSM s exp ->
            let
                expMeta =
                    fakeMeta_ exp

                patternMeta =
                    fakePatternMeta s
            in
            State.map3
                (\fresh pat newExp ->
                    addFakeMeta (Lambda pat newExp) fresh
                )
                freshInt
                patternMeta
                expMeta

        CallSM e1 e2 ->
            let
                e1Meta =
                    fakeMeta_ e1

                e2Meta =
                    fakeMeta_ e2
            in
            State.map3
                (\fresh newE1 newE2 ->
                    addFakeMeta (Call newE1 newE2) fresh
                )
                freshInt
                e1Meta
                e2Meta

        LetSM list expression ->
            let
                ( patterns, expressions ) =
                    List.map (\( p, exp ) -> ( fakePatternMeta p, fakeMeta_ exp )) list
                        |> List.unzip
                        |> (\( pats, exps ) -> ( State.combine pats, State.combine exps ))

                expMeta =
                    fakeMeta_ expression
            in
            State.map3 (\pats exps exp -> addFakeMeta (Let (List.map2 (,) pats exps) exp))
                patterns
                expressions
                expMeta
                |> State.andMap freshInt

        CaseSM expression list ->
            let
                ( patterns, expressions ) =
                    List.map (\( p, exp ) -> ( fakePatternMeta p, fakeMeta_ exp )) list
                        |> List.unzip
                        |> (\( pats, exps ) -> ( State.combine pats, State.combine exps ))

                expMeta =
                    fakeMeta_ expression
            in
            State.map3 (\pats exps exp -> addFakeMeta (Case exp (List.map2 (,) pats exps)))
                patterns
                expressions
                expMeta
                |> State.andMap freshInt

        NameSM s ->
            freshInt |> State.map (addFakeMeta <| Name s)

        SpySM exp i ->
            let
                expMeta =
                    fakeMeta_ exp
            in
            State.map2 (\fresh newExp -> addFakeMeta (Spy newExp i) fresh) freshInt expMeta


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


typesEqual : Type -> Type -> () -> Expect.Expectation
typesEqual ( constr1, t1 ) ( constr2, t2 ) =
    let
        usedTypeVars1 =
            extractTypeVariableIds <| arrowToList t1

        usedTypeVars2 =
            extractTypeVariableIds <| arrowToList t2

        newConstr1 =
            Dict.filter (\k _ -> List.member k usedTypeVars1) constr1

        newConstr2 =
            Dict.filter (\k _ -> List.member k usedTypeVars2) constr2
    in
    \() -> Expect.equal ( newConstr1, t1 ) ( newConstr2, t2 )


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
        , ("id", ([0], unconstrained <| TAny 0 => TAny 0))
        ]


tuple : ExpressionSansMeta -> ExpressionSansMeta -> ExpressionSansMeta
tuple a b =
    CallSM (CallSM (NameSM "tuple2") a) b


arith : ( List number, Type )
arith =
    ( [ 1 ], unconstrained <| TAny 1 => TAny 1 => TAny 1 )


arrowToList : RawType -> List RawType
arrowToList a =
    case a of
        TArrow left right ->
            left :: arrowToList right

        _ ->
            [ a ]


listToArrow : List RawType -> RawType
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


extractTypeVariableIds : List RawType -> List Int
extractTypeVariableIds =
    List.filterMap
        (\el ->
            case el of
                TAny id ->
                    Just id

                _ ->
                    Nothing
        )


minimizeTAny : Type -> Type
minimizeTAny ( constr, t ) =
    let
        typesList =
            arrowToList t

        minimizedIds =
            extractTypeVariableIds typesList
                |> List.unique
                |> List.sort
                |> List.indexedMap (flip (,))
                |> Dict.fromList

        newConstr =
            Dict.foldl (\k v acc -> Dict.insert (Dict.get k minimizedIds |> Maybe.withDefault -1) v acc) Dict.empty constr
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
        |> (,) newConstr


typeOf : Environment -> MExp -> Result String Type
typeOf env exp =
    Infer.typeOf env exp
        |> Infer.finalValue 0
        |> Result.map Tuple.first


codeWithContext : Infer.Scheme.Environment -> String -> Result String Type -> (() -> Expect.Expectation)
codeWithContext env input typeOrError =
    Ast.parse ("a = " ++ input)
        |> Result.mapError (always "Parsing failed")
        |> Result.andThen
            (\res ->
                case res of
                    ( _, _, [ ( Statement.FunctionDeclaration ( Ast.Common.PVariable "a", _ ) body, _ ) ] ) ->
                        Ok body

                    _ ->
                        Err "Imparsable code"
            )
        |> Result.map Translate.expression
        |> Result.andThen (typeOf env)
        |> Result.map minimizeTAny
        |> (\r ->
                case ( r, typeOrError ) of
                    ( Ok t1, Ok t2 ) ->
                        typesEqual t1 t2

                    _ ->
                        equal r typeOrError
           )


code : String -> Result String Type -> (() -> Expect.Expectation)
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

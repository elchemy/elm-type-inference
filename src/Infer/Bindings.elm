module Infer.Bindings exposing (Binding, Variable(..), group)

import Graph exposing (AcyclicGraph, Edge, Graph, Node)
import Infer.Expression exposing (Expression(..), MExp, MPattern, Pattern(..))
import List.Extra as List
import Result exposing (Result(..))
import Set exposing (Set)
import Utils exposing (..)


type alias Binding =
    ( MPattern, MExp )


type Variable
    = Value String Int
    | Function String (List MPattern) Int


getPatternId : MPattern -> Int
getPatternId ( _, { id } ) =
    id


getVariablePatternId : Variable -> Int
getVariablePatternId v =
    case v of
        Value _ id ->
            id

        Function _ _ id ->
            id


{-| Create groups of mutually dependent free variables and sort those groups so that dependencies come last
-}
group : List Binding -> List (List ( MPattern, MExp ))
group bindings =
    let
        ( patterns, expressions ) =
            List.unzip bindings

        boundList =
            List.map boundVariables patterns

        boundNamesList =
            boundList |> List.map (List.map variableName >> Set.fromList)

        boundNames =
            arbitraryUnion boundNamesList

        areUnique =
            List.foldr (Result.andThen << disjointUnion)
                (Ok Set.empty)
                boundNamesList

        labels =
            List.concat boundList

        nodes =
            List.map (\(( ( _, { id } ), _ ) as binding) -> Node id binding) bindings

        neighbourPatternIds exp =
            let
                freeVars =
                    freeVariables exp
            in
            List.filterMap
                (\label ->
                    if not <| Set.member (variableName label) freeVars then
                        Nothing

                    else
                        Just (getVariablePatternId label)
                )
                labels
                |> List.unique

        edges =
            List.map
                (\( ( _, { id } ), exp ) ->
                    List.map (\neighbourId -> Edge id neighbourId ()) (neighbourPatternIds exp)
                )
                bindings
                |> List.concat

    in
    case areUnique of
        Ok _ ->
            Graph.fromNodesAndEdges nodes edges
                |> stronglyConnectedComponentsDAG
                |> Graph.topologicalSort
                |> List.map (.node >> .label)

        Err s ->
            Debug.crash <| "Repeated use of variables: " ++ toString (Set.toList s)


{-| Get a set of variables bound by a pattern
-}
boundVariables : MPattern -> List Variable
boundVariables (( p, { id } ) as pattern) =
    case p of
        PWild ->
            []

        PVariable n ->
            [ Value n id ]

        PConstructor n ->
            []

        PLiteral _ ->
            []

        PTuple elems ->
            List.map boundVariables elems |> List.concat

        PCons head tail ->
            boundVariables head ++ boundVariables tail

        PList elems ->
            List.map boundVariables elems |> List.concat

        PRecord names ->
            List.map (\n -> Value n id) names

        PAs body name ->
            Value name id :: boundVariables body

        PApplication (( leftBody, _ ) as left) right ->
            let
                ( ( name, _ ), args ) =
                    splitApplication pattern
            in
            case name of
                PConstructor _ ->
                    List.map boundVariables args |> List.concat

                PVariable n ->
                    [ Function n args id ]

                _ ->
                    Debug.crash "Can only use a constructor or a function name here"


variableName : Variable -> String
variableName v =
    case v of
        Value n _ ->
            n

        Function n _ _ ->
            n


compareVariables : Variable -> Variable -> Bool
compareVariables a b =
    variableName a == variableName b


splitApplication : MPattern -> ( MPattern, List MPattern )
splitApplication (( app, _ ) as whole) =
    case app of
        PApplication left right ->
            Tuple.mapSecond (flip (++) [ right ]) (splitApplication left)

        _ ->
            ( whole, [] )


boundVariablesNames : MPattern -> Set String
boundVariablesNames =
    Set.fromList << List.map variableName << boundVariables


{-| Get a set of free variables occurring in an expression
-}
freeVariables : MExp -> Set String
freeVariables ( e, _ ) =
    case e of
        Name x ->
            Set.singleton x

        Lambda arg exp ->
            let
                argVars =
                    boundVariables arg |> List.map variableName |> Set.fromList
            in
            Set.diff (freeVariables exp) argVars

        Let bindings exp ->
            List.unzip bindings
                |> Tuple.mapFirst
                    (arbitraryUnion << List.map boundVariablesNames)
                |> Tuple.mapSecond
                    (Set.union (freeVariables exp)
                        << (arbitraryUnion << List.map freeVariables)
                    )
                |> (\( bound, free ) -> Set.diff free bound)

        Case exp bindings ->
            List.unzip bindings
                |> Tuple.mapFirst (arbitraryUnion << List.map boundVariablesNames)
                |> Tuple.mapSecond
                    (Set.union (freeVariables exp)
                        << (arbitraryUnion << List.map freeVariables)
                    )
                |> (\( bound, free ) -> Set.diff free bound)

        Call e1 e2 ->
            Set.union (freeVariables e1) (freeVariables e2)

        Literal _ ->
            Set.empty

        Spy exp _ ->
            freeVariables exp

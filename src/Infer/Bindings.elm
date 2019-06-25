module Infer.Bindings exposing (group)

import Dict exposing (Dict)
import Graph exposing (AcyclicGraph, Edge, Graph, Node)
import Infer.Expression exposing (Expression(..), MExp, MPattern, Pattern(..))
import List.Extra as List
import Result exposing (Result(..))
import Set exposing (Set)
import Utils exposing (..)


{-| Create groups of mutually dependent free variables and sort those groups so that dependencies come last
-}
group : List ( MPattern, MExp ) -> List (List ( MPattern, MExp ))
group bindings_ =
    let
        ( patterns, expressions ) =
            List.unzip bindings_

        boundList =
            List.map boundVariables patterns

        numberedMatches =
            List.indexedMap (,) bindings_ |> Dict.fromList

        varsToMatchIds =
            List.map2 (\vars pattern -> List.map (flip (,) pattern) <| Set.toList vars) boundList (Dict.keys numberedMatches)
                |> List.concat
                |> Dict.fromList

        areUnique =
            List.foldr (Result.andThen << disjointUnion) (Ok Set.empty) boundList

        bindings =
            List.map2 (\exp -> Set.foldr (\x acc -> ( x, exp ) :: acc) []) expressions boundList
                |> List.concat
                |> Dict.fromList

        bound =
            arbitraryUnion boundList

        neighbours =
            Dict.map
                (\v exp ->
                    freeVariables exp
                        |> (\free ->
                                Set.intersect free bound
                           )
                        |> Set.toList
                )
                bindings

        findPatterns vars =
            List.map (flip getOrCrash varsToMatchIds) vars
                |> List.unique
                |> List.map (flip getOrCrash numberedMatches)

        labels =
            List.concatMap Set.toList boundList

        asd = Debug.log "labels" labels
        gdj = Debug.log "neighbours" neighbours
    in
    case areUnique of
        Ok _ ->
            graphFromLabelsAndNeighbours labels neighbours
                |> stronglyConnectedComponentsDAG
                |> Graph.topologicalSort
                |> List.map (.node >> .label )
                |> Debug.log "sorted"
                |> List.map findPatterns
                |> \a -> Debug.log "patterns" (List.map (List.map Tuple.first) a) |> \_ -> a

        Err s ->
            Debug.crash <| "Repeated use of variables: " ++ toString (Set.toList s)


{-| Get a set of variables bound by a pattern
-}
boundVariables : MPattern -> Set String
boundVariables ( p, _ ) =
    case p of
        PWild ->
            Set.empty

        PName n ->
            Set.singleton n

        PLiteral _ ->
            Set.empty

        PTuple elems ->
            List.map boundVariables elems |> List.foldl Set.union Set.empty

        PCons head tail ->
            Set.union (boundVariables head) (boundVariables tail)

        PList elems ->
            List.map boundVariables elems |> List.foldl Set.union Set.empty

        PRecord names ->
            Set.fromList names

        PAs body name ->
            Set.union (boundVariables body) (Set.singleton name)

        PApplication (( leftBody, _ ) as left) right ->
            case leftBody of
                PApplication _ _ ->
                    Set.union (boundVariables left) (boundVariables right)

                _ ->
                    boundVariables right


{-| Get a set of free variables occurring in an expression
-}
freeVariables : MExp -> Set String
freeVariables ( e, _ ) =
    case e of
        Name x ->
            Set.singleton x

        Lambda arg exp ->
            Set.diff (freeVariables exp) (boundVariables arg)

        Let bindings exp ->
            List.unzip bindings
                |> Tuple.mapFirst (arbitraryUnion << List.map boundVariables)
                |> Tuple.mapSecond
                    (Set.union (freeVariables exp)
                        << (arbitraryUnion << List.map freeVariables)
                    )
                |> (\( bound, free ) -> Set.diff free bound)

        Case exp bindings ->
            List.unzip bindings
                |> Tuple.mapFirst (arbitraryUnion << List.map boundVariables)
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

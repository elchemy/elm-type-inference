module Utils exposing (arbitraryUnion, disjointUnion, getComponentNeighbours, getOrCrash, graphToLabelsList, stronglyConnectedComponentsDAG)

import Dict exposing (Dict)
import Graph exposing (AcyclicGraph, Graph, stronglyConnectedComponents)
import IntDict
import List.Extra as List
import Result exposing (Result(..))
import Set exposing (Set)


{-| Returns the positions of neighbours of given component
in the list passed as first argument
-}
getComponentNeighbours : List (Graph n e) -> Graph n e -> List Int
getComponentNeighbours components component =
    let
        isInComponent x =
            List.member x (Graph.nodeIds component)
    in
    Graph.fold (\ctx acc -> IntDict.keys ctx.outgoing ++ acc) [] component
        |> List.filter (not << isInComponent)
        |> List.map
            (\neighbourId ->
                case List.findIndex (Graph.member neighbourId) components of
                    Nothing ->
                        Debug.crash "This should never happen"

                    Just neighbour ->
                        neighbour
            )
        |> List.unique


{-| Create an acyclic graph of strongly connected components of given graph
-}
stronglyConnectedComponentsDAG : Graph n e -> AcyclicGraph (List n) ()
stronglyConnectedComponentsDAG g =
    let
        result =
            case stronglyConnectedComponents g of
                Err components ->
                    let
                        edges =
                            components
                                |> List.map (getComponentNeighbours components)
                                |> List.indexedMap (List.map << (,))
                                |> List.concat

                        labels =
                            List.map graphToLabelsList components
                    in
                    Graph.fromNodeLabelsAndEdgePairs labels edges

                Ok acyclic ->
                    Graph.mapNodes List.singleton g
                        |> Graph.mapEdges (always ())
    in
    case Graph.checkAcyclic result of
        Ok acyclic ->
            acyclic

        Err _ ->
            Debug.crash "Strongly connected components always form a DAG, so this should never happen"


getOrCrash : comparable -> Dict comparable a -> a
getOrCrash x d =
    case Dict.get x d of
        Just v ->
            v

        _ ->
            Debug.crash <| "Could not find " ++ toString x ++ " in " ++ toString d


disjointUnion : Set comparable -> Set comparable -> Result (Set comparable) (Set comparable)
disjointUnion a b =
    let
        section =
            Set.intersect a b
    in
    if Set.isEmpty section then
        Ok <| Set.union a b

    else
        Err <| section


arbitraryUnion : List (Set comparable) -> Set comparable
arbitraryUnion =
    List.foldr Set.union Set.empty


graphToLabelsList : Graph n e -> List n
graphToLabelsList =
    Graph.nodes >> List.map .label

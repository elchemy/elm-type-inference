module Infer.Bindings exposing (group)

import Dict exposing (Dict)
import Infer.Expression exposing (Expression(..), MExp)
import List.Extra as List exposing (dropWhile, unique)
import Set exposing (Set)


group : List ( String, MExp ) -> List (List ( String, MExp ))
group bindings_ =
    let
        bindings =
            Dict.fromList bindings_

        nodes =
            Dict.keys bindings

        neighbors =
            Dict.map
                (always (freeVariables >> Set.filter (\x -> List.member x nodes)))
                bindings
    in
    stronglyConnected nodes neighbors
        |> sortGroups neighbors
        |> List.map
            (List.map
                (\name ->
                    ( name
                    , Dict.get name bindings
                        |> Maybe.withDefault ( Name "error", { id = -1, column = -1, line = -1 } )
                    )
                )
            )


sortGroups : Dict comparable (Set comparable) -> List (List comparable) -> List (List comparable)
sortGroups neighborDict groups =
    let
        groupNeighbors group =
            List.map neighbors group
                |> List.foldl Set.union Set.empty
                |> Set.map groupContaining
                |> Set.remove group
                |> Set.toList

        neighbors x =
            Dict.get x neighborDict
                |> Maybe.withDefault Set.empty

        groupContaining x =
            List.find (List.member x) groups
                -- this should be impossible, as the groups do not overlap
                |> Maybe.withDefault []
    in
    depsFirst groups groupNeighbors


{-| Returns the nodes of a directed acyclic graph (a tree) in an order where
all children of a node come before the node
-}
depsFirst : List comparable -> (comparable -> List comparable) -> List comparable
depsFirst nodes neighbors =
    let
        dependencies node =
            (neighbors node
                |> List.concatMap dependencies
                |> unique
            )
                ++ [ node ]
    in
    List.concatMap dependencies nodes
        |> unique


freeVariables : MExp -> Set String
freeVariables ( e, _ ) =
    case e of
        Name x ->
            Set.singleton x

        Lambda arg exp ->
            freeVariables exp
                |> Set.remove arg

        Let bindings exp ->
            List.map Tuple.first bindings
                |> Set.fromList
                |> Set.diff (freeVariables exp)

        Call e1 e2 ->
            Set.union (freeVariables e1) (freeVariables e2)

        Literal _ ->
            Set.empty

        Spy exp _ ->
            freeVariables exp


stronglyConnected : List comparable -> Dict comparable (Set comparable) -> List (List comparable)
stronglyConnected nodes neighbors =
    let
        component n =
            Set.intersect
                (connected n neighbors)
                (connected n (reverseDict neighbors))

        ( components, _ ) =
            List.foldl
                (\node ( components, used ) ->
                    if not <| Set.member node used then
                        let
                            new =
                                component node
                        in
                        ( new :: components, Set.union new used )

                    else
                        ( components, used )
                )
                ( [], Set.empty )
                nodes
    in
    components
        |> List.map Set.toList


connected : comparable -> Dict comparable (Set comparable) -> Set comparable
connected node neighbors =
    let
        connected_ node visited =
            if Set.member node visited then
                visited

            else
                Dict.get node neighbors
                    |> Maybe.withDefault Set.empty
                    |> Set.foldl connected_ (Set.insert node visited)
    in
    connected_ node Set.empty


reverseDict : Dict comparable (Set comparable) -> Dict comparable (Set comparable)
reverseDict dict =
    let
        addEntry ( k, v ) =
            Dict.update k (Maybe.withDefault Set.empty >> Set.insert v >> Just)
    in
    Dict.toList dict
        |> List.concatMap (\( k, vs ) -> List.map (\v -> ( v, k )) <| Set.toList vs)
        |> List.foldl addEntry Dict.empty

module Infer.Scheme exposing
    ( Scheme, freeVariables
    , Environment
    , freshInt, instantiate, generalize
    )

{-| #

@docs Scheme, freeVariables
@docs Environment
@docs freshInt, instantiate, generalize

-}

import Dict exposing (Dict)
import Infer.Monad as Infer
import Infer.Type as Type exposing (RawType(..), Type)
import Set exposing (Set)
import State


{-| Generates an int one greater than the last.
-}
freshInt : Infer.Monad Int
freshInt =
    State.advance (\state -> ( Ok state, state + 1 ))


{-| A type scheme represents a variable definition, for example a named function.
When the variable is used, the scheme must be converted into a concrete type.
The listed type variables are the ones that the type is generic over. It may
contain others that represent for example types of things defined higher up.
-}
type alias Scheme =
    ( List Int, Type )


{-| Converts a scheme into a concrete type by swapping the generic type
variables for fresh ones.
-}
instantiate : Scheme -> Infer.Monad Type
instantiate ( vars, ( constraints, _ ) as t ) =
    List.map
        (\var ->
            Infer.map
                (\x ->
                    ( var
                    , ( Dict.get var constraints
                            |> Maybe.map (Dict.singleton x)
                            |> Maybe.withDefault Dict.empty
                      , TAny x
                      )
                    )
                )
                freshInt
        )
        vars
        |> Infer.combine
        |> Infer.map Dict.fromList
        |> Infer.map (\sub -> Type.substitute sub t)


{-| Holds all names defined in outer scopes.
-}
type alias Environment =
    Dict String Scheme



{- Applies a substitution on a type scheme without touching the generic type vars
   substitute : Type.Substitution -> Scheme -> Scheme
   substitute s ( vars, t ) =
   ( vars, Type.substitute (List.foldl Dict.remove s vars) t )
-}


{-| Converts a type into a type scheme that is generic over all the type variables
in the type not coming from the environment.
-}
generalize : Environment -> Type -> Scheme
generalize env t =
    let
        inEnv =
            List.map freeVariables (Dict.values env)
                |> List.foldl Set.union Set.empty

        inType =
            Type.variables <| Tuple.second t

        generic =
            Set.diff inType inEnv
    in
    ( Set.toList generic, t )


{-| Variables that are not bound by the type scheme.
-}
freeVariables : Scheme -> Set Int
freeVariables ( generic, ( _, t ) ) =
    Set.diff (Type.variables t) (Set.fromList generic)

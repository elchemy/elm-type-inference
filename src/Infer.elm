module Infer exposing (typeOf)

{-| This is the module implementing type inference. You'll also need at least `Infer.Expression`.

@docs typeOf

-}

import Dict
import Infer.Bindings as Bindings
import Infer.ConstraintGen exposing (..)
import Infer.Expression exposing (Expression(..), MExp)
import Infer.InternalMonad exposing (..)
import Infer.Monad as External
import Infer.Scheme exposing (Environment, Scheme, generalize)
import Infer.Type as Type exposing (($), (=>), RawType(..), Substitution, Type, substitute)


{-| Returns a computation that yields the type of the input expression
with the specified environment.
-}
typeOf : Environment -> MExp -> External.Monad ( Type, Substitution )
typeOf env exp =
    generateConstraints env exp
        |> andThen
            (\( t, cs ) ->
                solve Dict.empty cs
                    |> Result.map (\s -> ( Type.substitute s t, s ))
                    |> External.fromResult
            )


solve : Substitution -> List Constraint -> Result String Substitution
solve substitution constraints =
    case constraints of
        [] ->
            Ok substitution

        ( t1, t2 ) :: tail ->
            Type.unify t1 t2
                |> Result.andThen
                    (\new ->
                        solve
                            (new $ substitution)
                            (List.map (substituteConstraint new) tail)
                    )


substituteConstraint : Substitution -> Constraint -> Constraint
substituteConstraint substitution ( l, r ) =
    let
        f =
            Type.substitute substitution
    in
    ( f l, f r )


freshTypevar : Monad RawType
freshTypevar =
    Infer.Scheme.freshInt
        |> fromExternal
        |> map TAny


generateConstraints : Environment -> MExp -> Monad ( Type, List Constraint )
generateConstraints environment ( exp, _ ) =
    case exp of
        Name name ->
            variable environment name
                |> map (\x -> ( x, [] ))

        Literal t ->
            pure ( t, [] )

        Call function argument ->
            map3
                (\this ( f, fc ) ( ( aTC, a ), ac ) ->
                    ( ( Dict.empty, this )
                    , fc ++ ac ++ [ ( f, ( aTC, a => this ) ) ]
                    )
                )
                freshTypevar
                (generateConstraints environment function)
                (generateConstraints environment argument)

        Lambda argument body ->
            freshTypevar
                |> andThen
                    (\argType ->
                        generateConstraints (extend environment argument ( Dict.empty, argType )) body
                            |> map
                                (\( ( bodyTC, bodyType ), bodyCons ) ->
                                    ( ( bodyTC, argType => bodyType ), bodyCons )
                                )
                    )

        Let bindings body ->
            Bindings.group bindings
                |> List.foldl (addBindingGroupToEnv >> andThen) (pure environment)
                |> andThen
                    (\env -> generateConstraints env body)


        Spy exp tag ->
            generateConstraints environment exp
                |> map
                    (\( typ, constraints ) ->
                        ( typ, constraints ++ [ ( ( Dict.empty, TAny tag ), typ ) ] )
                    )


addBindingGroupToEnv : List ( String, MExp ) -> Environment -> Monad Environment
addBindingGroupToEnv bindings origEnv =
    let
        bindings_ =
            List.map (\( n, e ) -> map (\tv -> ( n, e, ( Dict.empty, tv ) )) freshTypevar) bindings
                |> combine

        extendedEnv =
            map (List.foldl (\( n, _, tv ) env -> extend env n tv) origEnv) bindings_

        typesAndConstraints =
            map2
                (\bin env ->
                    bin
                        |> List.map
                            (\( _, e, tv ) ->
                                map (\( t, cs ) -> ( t, ( tv, t ) :: cs )) <|
                                    generateConstraints env e
                            )
                        |> combine
                )
                bindings_
                extendedEnv
                |> andThen identity

        subs =
            List.map Tuple.second
                >> List.concat
                >> solve Dict.empty
                >> fromResult
    in
    typesAndConstraints
        |> andThen
            (\tcs ->
                subs tcs
                    |> andThen
                        (\subs ->
                            List.map Tuple.first tcs
                                |> List.map (substitute subs >> generalize origEnv)
                                |> List.map2 (,) (List.map Tuple.first bindings)
                                |> Dict.fromList
                                |> (\new -> Dict.union new origEnv)
                                |> pure
                                |> addSubstitution subs
                        )
            )

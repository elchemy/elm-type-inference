module Infer exposing (typeOf)

{-| This is the module implementing type inference. You'll also need at least `Infer.Expression`.

@docs typeOf

-}

import Dict
import Graph
import Graph.Tree
import Infer.Bindings as Bindings
import Infer.ConstraintGen exposing (..)
import Infer.Expression exposing (Expression(..), MExp, MPattern, Pattern(..))
import Infer.InternalMonad exposing (..)
import Infer.Monad as External
import Infer.Scheme exposing (Environment, Scheme, generalize)
import Infer.Type as Type exposing (($), (=>), RawType(..), Substitution, Type, Unification, sameTypeUnifications, substitute, unconstrained)
import List.Extra as List


{-| Returns a computation that yields the type of the input expression
with the specified environment.
-}
typeOf : Environment -> MExp -> External.Monad ( Type, Substitution )
typeOf env exp =
    generateConstraints env exp
        |> andThen
            (\( t, cs, _ ) ->
                solve Dict.empty cs
                    |> Result.map (\s -> ( Type.substitute s t, s ))
                    |> External.fromResult
            )


solve : Substitution -> List Unification -> Result String Substitution
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


substituteConstraint : Substitution -> Unification -> Unification
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


listConstraints : (Environment -> a -> Monad ( b, List Unification, Environment )) -> Environment -> List a -> Monad ( List b, List Unification, Environment )
listConstraints generator env li =
    let
        generateElem elem ( types, unifications, newEnv ) =
            generator newEnv elem
                |> map
                    (\( elemType, elemUnifications, elemEnv ) ->
                        ( elemType :: types, elemUnifications ++ unifications, elemEnv )
                    )
    in
    List.foldr (andThen << generateElem) (pure ( [], [], env )) li


generatePatternConstraints : Environment -> MPattern -> Monad ( Type, List Unification, Environment )
generatePatternConstraints env ( p, _ ) =
    case p of
        PWild ->
            map (\tv -> ( unconstrained tv, [], env )) freshTypevar

        PConstructor n ->
            map (\tv -> ( unconstrained tv, [], extend env n (unconstrained tv) )) freshTypevar

        PVariable n ->
            map (\tv -> ( unconstrained tv, [], extend env n (unconstrained tv) )) freshTypevar

        PLiteral t ->
            pure ( t, [], env )

        PTuple li ->
            listConstraints generatePatternConstraints env li
                |> map
                    (\( types, unifications, newEnv ) ->
                        ( Type.makeTuple types
                        , unifications
                        , newEnv
                        )
                    )

        PCons head tail ->
            generatePatternConstraints env head
                |> andThen
                    (\(( ht, hu, hEnv ) as hg) ->
                        map ((,) hg) (generatePatternConstraints hEnv tail)
                    )
                |> map
                    (\( headGen, tailGen ) ->
                        let
                            ( ( headTC, headRawType ), headUnifications, _ ) =
                                headGen

                            ( tailType, tailUnifications, newEnv ) =
                                tailGen

                            -- Type of the whole expression is a list of head type
                            wholeType =
                                ( headTC, Type.list headRawType )

                            -- And it must be the same as tail type
                            uniformityUnification =
                                ( wholeType, tailType )
                        in
                        ( wholeType, uniformityUnification :: (headUnifications ++ tailUnifications), newEnv )
                    )

        PList li ->
            map2
                (\( types, unifications, newEnv ) freshTVar ->
                    Type.makeList types freshTVar
                        |> (\( listType, listUnifications ) ->
                                ( listType, listUnifications ++ unifications, newEnv )
                           )
                )
                (listConstraints generatePatternConstraints env li)
                freshTypevar

        PRecord names ->
            -- create new type variable for each name
            List.map (always freshTypevar) names
                |> combine
                |> map
                    (\typeVars ->
                        let
                            namesWithTypes =
                                List.map2 (,) names typeVars
                        in
                        ( unconstrained <|
                            TRecord (Dict.fromList namesWithTypes)
                        , []
                          -- save types for variables in the environment
                        , List.foldr (\( name, typeVar ) acc -> extend acc name (unconstrained typeVar)) env namesWithTypes
                        )
                    )

        PAs pattern name ->
            generatePatternConstraints env pattern
                |> map
                    (\( pType, unifications, newEnv ) ->
                        ( pType, unifications, extend newEnv name pType )
                    )

        PApplication left right ->
            generatePatternConstraints env left
                |> andThen
                    (\( lType, lUni, lEnv ) ->
                        map ((,) ( lType, lUni )) (generatePatternConstraints lEnv right)
                    )
                |> map2
                    (\typeVar ( ( leftType, leftUnifications ), ( ( rightTC, rawRightType ), rightUnifications, newEnv ) ) ->
                        ( unconstrained typeVar
                        , ( leftType, ( rightTC, rawRightType => typeVar ) )
                            :: (leftUnifications ++ rightUnifications)
                        , newEnv
                        )
                    )
                    freshTypevar


generateBindingConstraints :
    Environment
    -> ( MPattern, MExp )
    -> Monad ( Type, List Unification, Environment )
generateBindingConstraints env ( pat, exp ) =
    generatePatternConstraints env pat
        |> andThen
            (\( patType, patUnifications, patEnv ) ->
                generateConstraints patEnv exp
                    |> map
                        (\( expType, expUnifications, expEnv ) ->
                            ( expType
                            , ( expType, patType ) :: patUnifications ++ expUnifications
                            , expEnv
                            )
                        )
            )


generateCircularConstraints : Environment -> List ( MPattern, MExp ) -> Monad ( List ( Type, Type ), List Unification, Environment )
generateCircularConstraints environment li =
    let
        ( patterns, expressions ) =
            List.unzip li

        patternConstraints =
            -- add all variables to environment
            listConstraints generatePatternConstraints environment patterns

        expressionConstraints =
            patternConstraints
                |> andThen
                    (\( patternTypes, patternUnifications, patternEnv ) ->
                        listConstraints generateConstraints patternEnv expressions
                            |> map
                                (\( expressionTypes, expressionUnifications, expressionEnv ) ->
                                    -- match patterns with corresponding expression
                                    ( List.map2 (,) patternTypes expressionTypes, patternUnifications ++ expressionUnifications, expressionEnv )
                                )
                    )
    in
    expressionConstraints
        |> map
            (\( pairs, unifications, newEnv ) ->
                ( pairs
                , -- enforce pattern is the same type as the  corresponding expression
                  unifications ++ pairs
                , newEnv
                )
            )



resolvePolytypes : ( List ( Type, Type ), List Unification, Environment ) -> ( List ( Type, Type ), List Unification, Environment )
resolvePolytypes ( types, unifications, env ) =
    let
        ( patternTypes, expTypes ) =
            List.unzip types

        labels =
            List.unzip unifications
                |> (\( a, b ) -> a ++ b)
                |> List.uniqueBy toString

        -- TODO: handle errors properly
        getLabelId label =
            List.elemIndex label labels |> Maybe.withDefault -1

        edges =
            unifications
                |> List.map
                    (\( t1, t2 ) ->
                        let
                            t1Index =
                                getLabelId t1

                            t2Index =
                                getLabelId t2
                        in
                        [ ( t1Index, t2Index ), ( t2Index, t1Index ) ]
                    )
                |> List.concat

        graph =
            Graph.fromNodeLabelsAndEdgePairs labels edges

        patternLabelIds =
            List.map getLabelId patternTypes

        polytypes =
            Graph.dfsForest patternLabelIds graph
                |> List.map (Graph.Tree.preOrderList >> List.map (.node >> .label))


        resolve pt acc =
            case pt of
                [] ->
                    Nothing

                _ :: [] ->
                    Nothing

                -- TODO: above should not happen, handle it properly
                baseType :: a :: other ->
                    let
                        nextAcc =
                            ( baseType, a ) :: acc
                        kurwa = Debug.log "\naa" (baseType, a, (solve ( Dict.fromList [(0, (Dict.fromList [],TArrow (TAny 1) (TAny 1)))] ) nextAcc))
                    in
                    case solve Dict.empty nextAcc of
                        Err _ ->
                            Nothing

                        Ok _ ->
                            case other of
                                [] ->
                                    Just nextAcc

                                _ ->
                                    resolve (baseType :: other) nextAcc

        actualUnifications =
            List.map2 (\pt t -> resolve pt [] |> Maybe.withDefault [ t ]) polytypes types
                |> List.concat
    in
    ( types, actualUnifications, env )


generateConstraints : Environment -> MExp -> Monad ( Type, List Unification, Environment )
generateConstraints environment ( exp, _ ) =
    case exp of
        Name name ->
            variable environment name
                |> map (\x -> ( x, [], environment ))

        Literal t ->
            pure ( t, [], environment )

        -- App rule
        -- e0 : t0, e1 : t1, t' = freshVar, unify(t0, t1 -> t')
        -- => e0 (e1) : t'
        Call function argument ->
            generateConstraints environment function
                |> andThen
                    (\( funType, funUnifications, funEnv ) ->
                        map ((,) ( funType, funUnifications )) <|
                            generateConstraints funEnv argument
                    )
                |> andThen
                    (\( fun, ( argType, argUnifications, argEnv ) ) ->
                        map
                            (\fresh ->
                                ( fun
                                , ( argType, argUnifications )
                                , argEnv
                                , fresh
                                )
                            )
                            freshTypevar
                    )
                |> map
                    (\( fun, arg, env, this ) ->
                        let
                            ( funType, funUnifications ) =
                                fun

                            ( ( argTC, argRawType ), argUnifications ) =
                                arg
                        in
                        -- infer that e0 (e1) : t'
                        ( unconstrained this
                          -- propagate constraints
                        , funUnifications
                            ++ argUnifications
                            -- Demand that unify(t0, t1 -> t')
                            ++ [ ( funType, ( argTC, argRawType => this ) ) ]
                        , env
                        )
                    )

        -- Abs rule
        -- t = freshVar, x: t => e : t'
        -- => \x -> e : t -> t'
        Lambda argument body ->
            generatePatternConstraints environment argument
                |> andThen
                    (\( ( argTC, argType ), patternUnifications, argEnv ) ->
                        generateConstraints argEnv body
                            |> map
                                (\( ( bodyTC, bodyType ), bodyUnifications, bodyEnv ) ->
                                    ( ( Dict.union argTC bodyTC, argType => bodyType )
                                    , patternUnifications ++ bodyUnifications
                                    , bodyEnv
                                    )
                                )
                    )

        Let bindings body ->
            let
                patternsOrder =
                    Bindings.group bindings
            in
            patternsOrder
                |> listConstraints generateCircularConstraints environment
                |> map (\( t, u, e ) -> resolvePolytypes ( List.concat t, u, e ))
                |> andThen
                    (\( _, bindingsUnifications, bindingsEnv ) ->
                        generateConstraints bindingsEnv body
                            |> map
                                (\( bodyType, bodyUnifications, newEnv ) ->
                                    ( bodyType, bodyUnifications ++ bindingsUnifications, newEnv )
                                )
                    )

        Case expression matches ->
            let
                ( patterns, results ) =
                    List.unzip matches
            in
            generateConstraints environment expression
                |> andThen
                    (\( expType, expUnifications, expEnv ) ->
                        listConstraints generatePatternConstraints expEnv patterns
                            |> map
                                (\( patsTypes, patsUnifications, patsEnv ) ->
                                    ( ( expType, expUnifications ), ( patsTypes, patsUnifications ), patsEnv )
                                )
                    )
                |> andThen
                    (\( expC, patsC, patsEnv ) ->
                        listConstraints generateConstraints patsEnv results
                            |> map (\( resTypes, resUnifications, resEnv ) -> ( expC, patsC, ( resTypes, resUnifications ), resEnv ))
                    )
                |> map
                    (\( expC, patsC, resC, newEnv ) ->
                        let
                            ( expType, expUnifications ) =
                                expC

                            ( patsTypes, patsUnifications ) =
                                patsC

                            ( resTypes, resUnifications ) =
                                resC

                            resultsConsistency =
                                Type.sameTypeUnifications resTypes

                            patternsConsistency =
                                Type.sameTypeUnifications <| expType :: patsTypes

                            unifications =
                                expUnifications
                                    ++ patsUnifications
                                    ++ resUnifications
                                    ++ resultsConsistency
                                    ++ patternsConsistency
                        in
                        case resTypes of
                            x :: _ ->
                                ( x, unifications, newEnv )

                            _ ->
                                Debug.crash "Need at least one pattern in case"
                    )

        Spy exp tag ->
            generateConstraints environment exp
                |> map
                    (\( typ, constraints, newEnv ) ->
                        ( typ, constraints ++ [ ( ( Dict.empty, TAny tag ), typ ) ], newEnv )
                    )

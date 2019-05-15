module Infer.Type exposing
    ( Type, RawType(..), (=>), Constraint(..), unconstrained
    , string, char, bool, int, float, list
    , toString
    , Substitution, substitute, ($)
    , unify
    , variables
    )

{-| #

@docs Type, RawType, (=>), Constraint, unconstrained


# Constructors for common primitive types

@docs string, char, bool, int, float, list

@docs toString

@docs Substitution, substitute, ($)

@docs unify

@docs variables

-}

import Dict exposing (Dict)
import Set exposing (Set)


{-| Type bundled with constraints like number, comparable
-}
type alias Type =
    ( Dict Int Constraint, RawType )


{-| Convenience function for building types unconstrained by the built-in typeclasses.
-}
unconstrained : RawType -> Type
unconstrained t =
    ( Dict.empty, t )


{-| Represents Elm types. TAny is for type variables.
-}
type RawType
    = TArrow RawType RawType
    | TRecord (Dict String RawType)
    | TOpaque String (List RawType)
    | TAny Int


{-| The fat arrow is convenient as an infix version of TArrow.
-}
(=>) : RawType -> RawType -> RawType
(=>) =
    TArrow


infixr 9 =>


isTAnyWithId : Int -> RawType -> Bool
isTAnyWithId id x =
    case x of
        TAny id2 ->
            id == id2

        _ ->
            False


isTAnyWithConstraint : Constraint -> Type -> Bool
isTAnyWithConstraint r ( cs, x ) =
    case x of
        TAny id ->
            Dict.get id cs
                |> Maybe.map ((==) r)
                |> Maybe.withDefault False

        _ ->
            False


{-| The built-in Elm typeclasses.
-}
type Constraint
    = Number
    | Comparable
    | Appendable
    | CompAppend


unifyConstraints : Constraint -> Constraint -> Result String Constraint
unifyConstraints a b =
    let
        unordered x y =
            a == x && b == y || a == y && b == x
    in
    if a == b then
        Ok a

    else if unordered Number Comparable then
        Ok Number

    else if unordered Appendable Comparable then
        Ok CompAppend

    else
        Err "failed to unify constraints"


satisfies : RawType -> Constraint -> Bool
satisfies t c =
    case c of
        Number ->
            t == float || t == int

        Comparable ->
            isComparable t

        Appendable ->
            isAppendable t

        CompAppend ->
            isComparable t && isAppendable t


isAppendable : RawType -> Bool
isAppendable t =
    t == string || isList t


isList : RawType -> Bool
isList t =
    case t of
        TOpaque name _ ->
            name == listName

        _ ->
            False


isComparable : RawType -> Bool
isComparable t =
    List.member t [ int, float, char, string ]
        || isComparableCollection t


isComparableCollection : RawType -> Bool
isComparableCollection t =
    case t of
        TOpaque name args ->
            (name == listName || name == tupleName)
                && List.all isComparable args

        _ ->
            False


listName : String
listName =
    ".List"


tupleName : String
tupleName =
    ".Tuple"


{-| String
-}
string : RawType
string =
    TOpaque ".String" []


{-| Char
-}
char : RawType
char =
    TOpaque ".Char" []


{-| Bool
-}
bool : RawType
bool =
    TOpaque ".Bool" []


{-| Int
-}
int : RawType
int =
    TOpaque ".Int" []


{-| Float
-}
float : RawType
float =
    TOpaque ".Float" []


{-| List
-}
list : RawType -> RawType
list t =
    TOpaque ".List" [ t ]


{-| Textual representation of a type
-}
toString : Dict Int Constraint -> RawType -> String
toString cs =
    let
        toString_ t =
            case t of
                TOpaque "Tuple" types ->
                    List.map toString_ types
                        |> String.join ","
                        |> brace

                TOpaque name args ->
                    name
                        :: List.map toString_ args
                        |> String.join " "
                        |> brace

                TArrow l r ->
                    toString_ l ++ " -> " ++ toString_ r

                TAny x ->
                    constraintName (Dict.get x cs) ++ Basics.toString x

                TRecord d ->
                    Dict.toList d
                        |> List.map (\( n, t ) -> n ++ " : " ++ toString_ t)
                        |> String.join ", "
                        |> (\x -> "{" ++ x ++ "}")
    in
    toString_


constraintName : Maybe Constraint -> String
constraintName mr =
    case mr of
        Just r ->
            case r of
                Number ->
                    "number"

                Comparable ->
                    "comparable"

                Appendable ->
                    "appendable"

                CompAppend ->
                    "compappend"

        Nothing ->
            ""


brace : String -> String
brace x =
    "(" ++ x ++ ")"


{-| Returns the (free) type variables of the type.
-}
variables : RawType -> Set Int
variables t =
    case t of
        TAny x ->
            Set.singleton x

        TArrow l r ->
            Set.union (variables l) (variables r)

        TRecord d ->
            Dict.values d
                |> variablesFromList

        TOpaque _ args ->
            variablesFromList args


variablesFromList : List RawType -> Set Int
variablesFromList =
    List.map variables
        >> List.foldl Set.union Set.empty


{-| Returns the substitutions necessary to transform either type
into their lowest common denominator.
Returns an error if not possible.
-}
unify : Type -> Type -> Result String Substitution
unify ( acs, at ) ( bcs, bt ) =
    let
        unify_ : RawType -> RawType -> Result String Substitution
        unify_ at bt =
            case ( at, bt ) of
                ( TOpaque a at, TOpaque b bt ) ->
                    if a == b then
                        unifyMany
                            (List.map ((,) acs) at)
                            (List.map ((,) bcs) bt)

                    else
                        mismatch a b

                ( TArrow head1 tail1, TArrow head2 tail2 ) ->
                    unify_ head1 head2
                        |> Result.andThen
                            (\sub1 ->
                                unify (substitute sub1 ( acs, tail1 )) (substitute sub1 ( bcs, tail2 ))
                                    |> Result.map (\sub2 -> sub2 $ sub1)
                            )

                ( TAny id, TAny id2 ) ->
                    if id == id2 then
                        Ok Dict.empty

                    else
                        (case ( Dict.get id acs, Dict.get id2 bcs ) of
                            ( Just a, Just b ) ->
                                unifyConstraints a b
                                    |> Result.map (Dict.singleton id2)

                            ( Just a, Nothing ) ->
                                Ok <| Dict.singleton id2 a

                            ( Nothing, Just b ) ->
                                Ok <| Dict.singleton id2 b

                            ( Nothing, Nothing ) ->
                                Ok Dict.empty
                        )
                            |> Result.map
                                (\c ->
                                    Dict.fromList
                                        [ ( id, ( c, TAny id2 ) )
                                        , ( id2, ( c, TAny id2 ) )
                                        ]
                                )

                ( TAny id, x ) ->
                    bind id x

                ( x, TAny id ) ->
                    bind id x

                _ ->
                    mismatch (toString_ bt) (toString_ at)

        bind id x =
            if
                Dict.get id constraints
                    |> Maybe.map (not << satisfies x)
                    |> Maybe.withDefault False
            then
                Err "mismatched constraints"

            else if Set.member id (variables x) then
                Err ("recursive type " ++ Basics.toString id ++ " " ++ toString_ x)

            else
                -- TODO: drop unnecessary constraints here
                Ok <| Dict.singleton id ( constraints, x )

        toString_ =
            toString constraints

        constraints =
            Dict.union acs bcs
    in
    unify_ at bt


unifyMany : List Type -> List Type -> Result String Substitution
unifyMany context content =
    if List.length context /= List.length content then
        Err "different amounts of arguments"

    else
        List.map2 (,) context content
            |> List.foldl
                (\( a, b ) ->
                    Result.andThen
                        (\s ->
                            unify (substitute s a) (substitute s b)
                                |> Result.map (\res -> res $ s)
                        )
                )
                (Ok Dict.empty)


mismatch : String -> String -> Result String a
mismatch a b =
    Err <| "Mismatch: " ++ a ++ " and " ++ b


{-| Applies one substitution to another
-}
($) : Substitution -> Substitution -> Substitution
($) a b =
    Dict.union (Dict.map (always <| substitute a) b) a


infixl 9 $


{-| Tells what values type variables get.
-}
type alias Substitution =
    Dict Int Type


{-| Swap out type variables according to substitution
-}
substitute : Substitution -> Type -> Type
substitute subs ( cs, t ) =
    let
        substitute_ t =
            case t of
                (TAny x) as original ->
                    Dict.get x subs
                        |> Maybe.withDefault
                            ( Dict.get x cs
                                |> Maybe.map (Dict.singleton x)
                                |> Maybe.withDefault Dict.empty
                            , original
                            )

                TArrow h t ->
                    let
                        ( csh, th ) =
                            substitute_ h

                        ( cst, tt ) =
                            substitute_ t
                    in
                    ( Dict.union csh cst, TArrow th tt )

                TOpaque name types ->
                    let
                        res =
                            List.map substitute_ types
                    in
                    ( List.foldl (Tuple.first >> Dict.union) Dict.empty res
                    , TOpaque name (List.map Tuple.second res)
                    )

                TRecord fields ->
                    let
                        res =
                            Dict.map (always substitute_) fields
                    in
                    ( Dict.foldl (always (Tuple.first >> Dict.union)) Dict.empty res
                    , TRecord (Dict.map (always Tuple.second) res)
                    )
    in
    substitute_ t

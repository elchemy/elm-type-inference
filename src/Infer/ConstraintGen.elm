module Infer.ConstraintGen exposing (extend, extendGeneralized, variable)

import Dict exposing (Dict)
import Infer.InternalMonad exposing (..)
import Infer.Monad as External
import Infer.Scheme exposing (Environment, Scheme, generalize, instantiate)
import Infer.Type as Type exposing (($), Type)


variable : Environment -> String -> Monad Type
variable env name =
    Dict.get name env
        |> Result.fromMaybe ("variable " ++ name ++ " not found")
        |> External.fromResult
        |> External.andThen instantiate
        |> fromExternal


extendGeneralized : Environment -> String -> Type -> Environment
extendGeneralized environment name t =
    Dict.insert name (generalize environment t) environment


extend : Environment -> String -> Type -> Environment
extend environment name t =
    Dict.insert name ( [], t ) environment

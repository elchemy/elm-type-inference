module Meta exposing (idGeneration)

import Ast
import Ast.Identifiers exposing (generateStatementsIds)
import Expect exposing (..)
import Helpers exposing (..)
import Test exposing (Test, describe, test)


idGeneration : Test
idGeneration =
    let
        trivialCases =
            [ "a = 'a'", "a = 12", "a = 5.6", "a = \"hello\"" ]

        complexCase =
            """
        f = let
          x = [1,2,3]
          y = (1,2,3)
          z = {a = 1, b = 2, c = 3}
          f = List.map (\\a -> a + 1)
          w = Just 5
          n = {z | c = 5}
        in
          if
            1 < 2
          then
            3
          else
            case w of
              Nothing -> n.c
              Just v -> f x
        """

        mediumCase =
            """
f = let
  f x = x + 1
  g x = x + 1
in
  f 4
"""

        testGeneratedIds =
            \i () ->
                case Ast.parse i of
                    Ok ( _, _, s ) ->
                        let
                            statements =
                                generateStatementsIds s
                        in
                        if statementsHaveUniqueIds statements then
                            Expect.pass

                        else
                            Expect.fail "Ids are not unique"

                    Err _ ->
                        Expect.fail "Cannot parse"
    in
    describe "Trivial id generation" <|
        List.map (\i -> test ("Trivial: " ++ i) (testGeneratedIds i)) trivialCases
            ++ [ test "Complex" (testGeneratedIds complexCase)
               ]

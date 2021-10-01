module LogicUS.AUX.AuxiliarFunctions exposing (cleanSpaces, fromListToTableLatex, fromListToTableString, powerset, replaceBySubscript, replaceBySuperscript, subscriptLetters, uniqueConcatList)

import Dict exposing (Dict)
import List.Extra as LE
import String.Extra as SE



-- It concatenates two lists avoiding elements from second list that are in the first one.


uniqueConcatList : List a -> List a -> List a
uniqueConcatList xs ys =
    List.foldl
        (\x ac ->
            if List.member x ac then
                ac

            else
                ac ++ [ x ]
        )
        xs
        ys



-- It generates all possible sublists of a list of elements


powerset : List a -> List (List a)
powerset =
    List.foldr (\x acc -> acc ++ List.map ((::) x) acc) [ [] ]



-- It removes the spaces of a string


cleanSpaces : String -> String
cleanSpaces x =
    String.join "" <| String.split " " <| SE.clean x



-- It replaces numbers in a string by the proper subscript.


replaceBySubscript : String -> String
replaceBySubscript s =
    let
        dictSubscripts =
            Dict.fromList [ ( '0', '₀' ), ( '1', '₁' ), ( '2', '₂' ), ( '3', '₃' ), ( '4', '₄' ), ( '5', '₅' ), ( '6', '₆' ), ( '7', '₇' ), ( '8', '₈' ), ( '9', '₉' ), ( ',', ' ' ) ]
    in
    String.fromList <| List.map (\x -> Maybe.withDefault x <| Dict.get x dictSubscripts) <| String.toList s


replaceBySuperscript : String -> String
replaceBySuperscript s =
    let
        dictSuperscripts =
            Dict.fromList [ ( '0', '⁰' ), ( '1', '¹' ), ( '2', '²' ), ( '3', '³' ), ( '4', '⁴' ), ( '5', '⁵' ), ( '6', '⁶' ), ( '7', '⁷' ), ( '8', '⁸' ), ( '9', '⁹' ) ]
    in
    String.fromList <| List.map (\x -> Maybe.withDefault x <| Dict.get x dictSuperscripts) <| String.toList s


subscriptLetters : Dict Char Char
subscriptLetters =
    Dict.fromList <| LE.zip [ 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'r', 's', 't', 'u', 'v', 'w', 'x' ] [ 'ₕ', 'ᵢ', 'ⱼ', 'ₖ', 'ₗ', 'ₘ', 'ₙ', 'ₒ', 'ₚ', 'ᵣ', 'ₛ', 'ₜ', 'ᵤ', 'ᵥ', 'ᵥ', 'ᵥ', 'ₓ' ]



-- It generates the string of a list of string lists in csv format.


fromListToTableString : List (List String) -> String
fromListToTableString xss =
    String.join " \n" <| List.map (\xs -> String.join " ; " xs) xss



-- It generates the string of a list of string lists as an array environment in Latex.


fromListToTableLatex : String -> List (List String) -> List (List String) -> List (List String) -> String
fromListToTableLatex cols head body foot =
    let
        thead =
            if List.isEmpty head then
                ""

            else
                (String.join " \n" <| List.map (\xs -> String.join " & " (List.map (\x -> "\\mathbf{" ++ x ++ "}") xs) ++ " \\\\") head) ++ "\\hline \n"

        tbody =
            if List.isEmpty body then
                ""

            else
                (String.join " \n" <| List.map (\xs -> String.join " & " xs ++ " \\\\") body) ++ "\\hline \n"

        tfoot =
            if List.isEmpty foot then
                ""

            else
                (String.join " \n" <| List.map (\xs -> String.join " & " (List.map (\x -> "\\color{grey}{" ++ x ++ "}") xs) ++ "\\\\") foot) ++ "\\hline \n"
    in
    "\\begin{array}{" ++ cols ++ "}\\hline \n" ++ thead ++ tbody ++ tfoot ++ "\\end{array}"

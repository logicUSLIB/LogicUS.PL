module LogicUS.PL.SemanticTableaux exposing
    ( FormulaPLType, PLSemanticTableau
    , fplType, fplComponents
    , splAllLiterals, splRemoveTaut, splSearchContradiction, splSearchDN, splSearchAlpha, splSearchBeta, splExpandDN, splExpandAlpha, splExpandBeta
    , semanticTableau, semanticTableauRelevantLeaves, semanticTableauOpenLeaves, semanticTableauModels
    , semanticTableauToString, semanticTableauToDOT, semanticTableauToJSON, semanticTableauToDOTwithStyles
    )

{-| The module provides the elementary tools for building the semantic tableau of a set of PL formulas.


# Definition Types

@docs FormulaPLType, PLSemanticTableau


# Formulas types and components

@docs fplType, fplComponents


# Semantic Tableau operations

@docs splAllLiterals, splRemoveTaut, splSearchContradiction, splSearchDN, splSearchAlpha, splSearchBeta, splExpandDN, splExpandAlpha, splExpandBeta


# Semantic Tableau algorithm and models

@docs semanticTableau, semanticTableauRelevantLeaves, semanticTableauOpenLeaves, semanticTableauModels


# Fuctions for representation

@docs semanticTableauToString, semanticTableauToDOT, semanticTableauToJSON, semanticTableauToDOTwithStyles

-}

--===========--
--  IMPORTS  --
--===========--

import Graph.Tree as GTree exposing (Tree)
import Json.Encode as JSONE exposing (Value)
import List.Extra as LE
import LogicUS.PL.AuxiliarFunctions exposing (uniqueConcatList)
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), Interpretation, SetPL)



--===========--
--   TYPES   --
--===========--


{-|

    It defines the type of a PL formula which can be a *Literal*, *Double Negation*, *Alpha*, *Beta*, *Insat* or *Taut*

-}
type FormulaPLType
    = L
    | DN
    | A
    | B
    | I
    | T


type STRule
    = INITR
    | DNR
    | AR
    | BR
    | IR
    | TR


{-| Defines the PL Semantic Tableau type as a Graph whose node labels are pairs of an integer (0: internal node, 1: open leaf, -1: closed leaf) and the PL set considered in the corresponding node; and the edge labels are defined as pairs of the applied rule (A, B, DN, L, I, T) and the list of indexes of the formulas on which the rule is applied.
-}
type alias PLSemanticTableau =
    Tree { id : Int, fs : SetPL, parents : List Int, rule : STRule }



--===========--
-- FUNCTIONS --
--===========--
-----------------------
--   Calc functions   -
-----------------------


{-| It gives the type of a PL formula. Atoms and their negations are literals, double negation are typed as DN, conjunction, equivalence are classified as ALPHA, as well as disjunction and implications are classified as BETA. The negation of an alpha formula is a beta and vice versa.

    f1 : FormulaPL
    f1 = Atom "a"

    f2 : FormulaPL
    f2 = Atom "b"

    fplType f1 == L
    fplType (Neg f1) == L
    fplType (Neg (Neg f1)) == DN
    fplType (Conj f1 f2) == A
    fplType (Disj f1 f2) == B
    fplType (Impl f1 f2) == B
    fplType (Equi f1 f2) == A
    fplType (Neg (Conj f1 f2)) == B
    fplType (Neg (Disj f1 f2)) == A
    fplType (Neg (Impl f1 f2)) == A
    fplType (Neg (Equi f1 f2)) == B

-}
fplType : FormulaPL -> FormulaPLType
fplType f =
    case f of
        Atom _ ->
            L

        Neg (Atom _) ->
            L

        Neg (Neg _) ->
            DN

        Neg (Conj _ _) ->
            B

        Neg (Disj _ _) ->
            A

        Neg (Impl _ _) ->
            A

        Neg (Equi _ _) ->
            B

        Neg Insat ->
            T

        Neg Taut ->
            I

        Conj _ _ ->
            A

        Disj _ _ ->
            B

        Impl _ _ ->
            B

        Equi _ _ ->
            A

        Insat ->
            I

        Taut ->
            T


{-| It gives the components of a formula for using them in the semantic board

    fplComponents f1 == [ Atom "a" ]

    fplComponents (Neg f1) == [ Neg (Atom "a") ]

    fplComponents (Neg (Neg f1)) == [ Atom "a" ]

    fplComponents (Conj f1 f2) == [ Atom "a", Atom "b" ]

    fplComponents (Disj f1 f2) == [ Atom "a", Atom "b" ]

    fplComponents (Impl f1 f2) == [ Neg (Atom "a"), Atom "b" ]

    fplComponents (Equi f1 f2) == [ Impl (Atom "a") (Atom "b"), Impl (Atom "b") (Atom "a") ]

    fplComponents (Neg (Conj f1 f2)) == [ Neg (Atom "a"), Neg (Atom "b") ]

    fplComponents (Neg (Disj f1 f2)) == [ Neg (Atom "a"), Neg (Atom "b") ]

    fplComponents (Neg (Impl f1 f2)) == [ Atom "a", Neg (Atom "b") ]

    fplComponents (Neg (Equi f1 f2)) == [ Neg (Impl (Atom "a") (Atom "b")), Neg (Impl (Atom "b") (Atom "a")) ]

-}
fplComponents : FormulaPL -> List FormulaPL
fplComponents f =
    case f of
        Atom psymb ->
            [ Atom psymb ]

        Neg (Atom psymb) ->
            [ Neg (Atom psymb) ]

        Neg (Neg p) ->
            [ p ]

        Conj p q ->
            [ p, q ]

        Neg (Impl p q) ->
            [ p, PL_SS.fplNegation q ]

        Neg (Disj p q) ->
            [ PL_SS.fplNegation p, PL_SS.fplNegation q ]

        Neg Insat ->
            [ Taut ]

        Neg Taut ->
            [ Insat ]

        Disj p q ->
            [ p, q ]

        Impl p q ->
            [ PL_SS.fplNegation p, q ]

        Neg (Conj p q) ->
            [ PL_SS.fplNegation p, PL_SS.fplNegation q ]

        Equi p q ->
            [ Impl p q, Impl q p ]

        Neg (Equi p q) ->
            [ PL_SS.fplNegation (Impl p q), PL_SS.fplNegation (Impl q p) ]

        Insat ->
            [ Insat ]

        Taut ->
            [ Taut ]


{-| It gives if all formulas in a Set of PL formulas are literals.

    fs1  = [f1, Neg f2]
    fs2 = [f1, Neg f2, Conj f1 f2, Disj f1 f2, Neg (Impl f1 f2), Neg (Equi f1 f2)]
    splAllLiterals fs1 == True
    splAllLiterals fs2 == False

-}
splAllLiterals : SetPL -> Bool
splAllLiterals fs =
    List.all (\x -> fplType x == L) fs


{-| It removes all Tautological formulas from a set.
-}
splRemoveTaut : SetPL -> SetPL
splRemoveTaut fs =
    List.filter (\x -> fplType x /= T) fs


{-| It gives if one set of PL formulas contains a formula and its negation or contains the Insat formula (the set is unsatisfiable). If it finds them they return the formulas indices in the set (it is actually a list).

    splSearchContradiction fs1 == Nothing
    splSearchContradiction fs2 == Nothing

    -- If we expand ( Conj f1 f2 ) as [f1, f2] (note that f1 is repeated so we keep only one of its instances)
    fs3 = [f1, Neg f2, f2, Disj f1 f2, Neg (Impl f1 f2), Neg (Equi f1 f2)]
    splSearchContradiction fs3 == Just [1,2]

-}
splSearchContradiction : SetPL -> Maybe (List Int)
splSearchContradiction fs =
    let
        res =
            List.head <| List.filter (\( _, x ) -> List.member (PL_SS.fplNegation x) fs || fplType x == I) <| List.indexedMap Tuple.pair fs

        p ( i, f ) =
            if fplType f == I then
                Just [ i ]

            else
                let
                    j =
                        Maybe.withDefault -1 <| LE.findIndex (\x -> x == PL_SS.fplNegation f) fs
                in
                Just [ i, j ]
    in
    Maybe.andThen p res


{-| It searches a DN formula in the set. If it gets it they return a tuple with the index and the formula, if not Nothing is returned

    splSearchDN fs2 == Nothing

    -- If we expand Neg(Impl f1 f2) as [(Neg (Neg f1)), (Neg f2)] (note that (Neg f2) is repeated so we keep only one of its instances)
    fs4 = [f1, Neg f2, Conj f1 f2, Disj f1 f2, f1, Neg (Equi f1 f2)]
    splSearchDN fs4 == Just (4, (Atom "a"))

-}
splSearchDN : SetPL -> Maybe ( Int, FormulaPL )
splSearchDN fs =
    List.head <| List.filter (\( _, x ) -> fplType x == DN) <| List.indexedMap Tuple.pair fs


{-| It searches an Alpha formula in the set. If it gets it they return a tuple with the index and the formula, if not Nothing is returned

    splSearchAlpha fs1 == Nothing

    splSearchAlpha fs2 == Just ( 2, Conj (Atom "a") (Atom "b") )

-}
splSearchAlpha : SetPL -> Maybe ( Int, FormulaPL )
splSearchAlpha fs =
    List.head <| List.filter (\( _, x ) -> fplType x == A) <| List.indexedMap Tuple.pair fs


{-| It searches an Beta formula in the set. If it gets it they return a tuple with the index and the formula, if not Nothing is returned

    splSearchBeta fs1 == Nothing

    splSearchBeta fs2 == Just ( 3, Disj (Atom "a") (Atom "b") )

-}
splSearchBeta : SetPL -> Maybe ( Int, FormulaPL )
splSearchBeta fs =
    List.head <| List.filter (\( _, x ) -> fplType x == B) <| List.indexedMap Tuple.pair fs


{-| It gives a set of formulas with changing a DN formula by its expansion. If formula is not DN the original set is returned.

    splExpandDN fs4 (Neg (Neg f2)) == [ Atom "a", Neg (Atom "b"), Conj (Atom "a") (Atom "b"), Disj (Atom "a") (Atom "b"), Atom "a", Neg (Equi (Atom "a") (Atom "b")), Atom "b" ]

-}
splExpandDN : SetPL -> FormulaPL -> SetPL
splExpandDN fs f =
    if fplType f /= DN then
        fs

    else
        splRemoveTaut <| uniqueConcatList (List.filter (\x -> x /= f) fs) (fplComponents f)


{-| It gives a set of formulas with changing an Alpha formula by its expansion. If formula is not Alpha the original set is returned.

    splExpandAlpha fs2 (Conj (Atom "a") (Atom "b")) == [ Atom "a", Neg (Atom "b"), Disj (Atom "a") (Atom "b"), Neg (Impl (Atom "a") (Atom "b")), Neg (Equi (Atom "a") (Atom "b")), Atom "b" ]

-}
splExpandAlpha : SetPL -> FormulaPL -> SetPL
splExpandAlpha fs f =
    if fplType f /= A then
        fs

    else
        splRemoveTaut <| uniqueConcatList (List.filter (\x -> x /= f) fs) (fplComponents f)


{-| It gives a tuple of two sets of formulas with changing a Beta formula by its expansion. If formula is not Beta original set is returned in both sets.

    splExpandBeta fs2 (Disj (Atom "a") (Atom "b")) == ( [ Atom "a", Neg (Atom "b"), Conj (Atom "a") (Atom "b"), Neg (Impl (Atom "a") (Atom "b")), Neg (Equi (Atom "a") (Atom "b")) ], [ Atom "a", Neg (Atom "b"), Conj (Atom "a") (Atom "b"), Neg (Impl (Atom "a") (Atom "b")), Neg (Equi (Atom "a") (Atom "b")), Atom "b" ] )

-}
splExpandBeta : SetPL -> FormulaPL -> ( SetPL, SetPL )
splExpandBeta fs f =
    if fplType f /= B then
        ( fs, fs )

    else
        let
            newfs =
                List.filter (\x -> x /= f) fs

            fcomponents =
                fplComponents f
        in
        ( splRemoveTaut <| uniqueConcatList newfs (List.take 1 fcomponents), splRemoveTaut <| uniqueConcatList newfs (List.drop 1 fcomponents) )


{-| It generates the complete SemanticTableaux as a Tree, which is renderizable with representations methods.
-}
semanticTableau : SetPL -> PLSemanticTableau
semanticTableau fs =
    splSemanticTableauBuilder (uniqueConcatList [] fs) 0 INITR -1


splSemanticTableauBuilder : SetPL -> Int -> STRule -> Int -> PLSemanticTableau
splSemanticTableauBuilder xs nid rule parent =
    case splSearchContradiction xs of
        Just incons ->
            GTree.inner { id = nid, fs = xs, parents = [ parent ], rule = rule } [ GTree.leaf { id = nid + 1, fs = [ Insat ], parents = List.map (\x -> 1 + x) incons, rule = IR } ]

        Nothing ->
            case splSearchDN xs of
                Just ( i, f ) ->
                    let
                        newxs =
                            splExpandDN xs f
                    in
                    let
                        child =
                            splSemanticTableauBuilder newxs (nid + 1) DNR (i + 1)
                    in
                    GTree.inner { id = nid, fs = xs, parents = [ parent ], rule = rule } [ child ]

                Nothing ->
                    case splSearchAlpha xs of
                        Just ( i, f ) ->
                            let
                                newxs =
                                    splExpandAlpha xs f
                            in
                            let
                                child =
                                    splSemanticTableauBuilder newxs (nid + 1) AR (i + 1)
                            in
                            GTree.inner { id = nid, fs = xs, parents = [ parent ], rule = rule } [ child ]

                        Nothing ->
                            case splSearchBeta xs of
                                Just ( i, f ) ->
                                    let
                                        ( newxs1, newxs2 ) =
                                            splExpandBeta xs f
                                    in
                                    let
                                        child1 =
                                            splSemanticTableauBuilder newxs1 (nid + 1) BR (i + 1)

                                        child2 =
                                            splSemanticTableauBuilder newxs2 (nid + 1) BR (i + 1)
                                    in
                                    GTree.inner { id = nid, fs = xs, parents = [ parent ], rule = rule } [ child1, child2 ]

                                Nothing ->
                                    GTree.inner { id = nid, fs = xs, parents = [ parent ], rule = rule } [ GTree.leaf { id = nid + 1, fs = xs, parents = [], rule = TR } ]


{-| It extracts all the leaves removing duplicates.
-}
semanticTableauOpenLeaves : PLSemanticTableau -> List SetPL
semanticTableauOpenLeaves st =
    case GTree.root st of
        Just ( label, [] ) ->
            if label.rule == TR then
                [ label.fs ]

            else
                []

        Just ( _, children ) ->
            LE.unique <| List.concat <| List.map semanticTableauOpenLeaves children

        Nothing ->
            []


{-| It extracts all the leaves applying subsumption for simplification.
-}
semanticTableauRelevantLeaves : PLSemanticTableau -> List SetPL
semanticTableauRelevantLeaves st =
    let
        subsumes l1 l2 =
            List.all (\x -> List.member x l2) l1

        subsumedBy l1 l2 =
            List.all (\x -> List.member x l1) l2
    in
    List.foldr
        (\x ac ->
            if not <| List.any (subsumedBy x) ac then
                x :: List.filter (not << subsumes x) ac

            else
                ac
        )
        []
    <|
        semanticTableauOpenLeaves st


{-| It extracts all the models from a semantic tableau.

    splSemanticTableau fs4 |> plSemanticTableauModels == []

    fs5 = [Disj f1 f2, Neg(Equi f1 f2)]
    splSemanticTableau fs5 |> plSemanticTableauModels == [["a"],["b"]]

-}
semanticTableauModels : PLSemanticTableau -> List Interpretation
semanticTableauModels st =
    case GTree.root st of
        Nothing ->
            []

        Just ( l, _ ) ->
            let
                symbs =
                    l.fs |> PL_SS.splSymbols
            in
            List.sort <|
                LE.unique <|
                    List.concat <|
                        List.map (\ls -> PL_SS.interpretationsFromSymbolsAndLiterals symbs ls) <|
                            semanticTableauRelevantLeaves st



-----------------------
--   Repr functions   -
-----------------------


{-| It gives the String representation of a tableau.

    splSemanticTableau fs4 |> semanticTableauToString == "Graph [Node 0 ({a, ¬ b, ( a ∧ b ), ( a ∨ b ), ¬ ( a ↔ b )}), Node 1 ({a, ¬ b, ( a ∨ b ), ¬ ( a ↔ b ), b}), Node 2 (×)] [Edge 1->2 (I (2, 5)), Edge 0->1 (α (3))]"

-}
semanticTableauToString : PLSemanticTableau -> String
semanticTableauToString =
    tableauToStringAux 0


tableauToStringAux : Int -> PLSemanticTableau -> String
tableauToStringAux indent t =
    case GTree.root t of
        Just ( l, ch ) ->
            String.repeat indent "   " ++ tableauNodeToString l ++ (String.join "" <| List.map (tableauToStringAux (indent + 1)) ch)

        Nothing ->
            ""


tableauNodeToString : { id : Int, fs : SetPL, parents : List Int, rule : STRule } -> String
tableauNodeToString ni =
    case ni.rule of
        AR ->
            String.fromInt ni.id
                ++ ":  "
                ++ PL_SS.splToString ni.fs
                ++ "     ["
                ++ "𝛼("
                ++ (String.join "," <|
                        List.map String.fromInt ni.parents
                   )
                ++ ")]\n\n"

        BR ->
            String.fromInt ni.id
                ++ ":  "
                ++ PL_SS.splToString ni.fs
                ++ "     ["
                ++ "𝛽("
                ++ (String.join "," <|
                        List.map String.fromInt ni.parents
                   )
                ++ ")]\n\n"

        DNR ->
            String.fromInt ni.id
                ++ ":  "
                ++ PL_SS.splToString ni.fs
                ++ "     ["
                ++ "𝒹𝒩("
                ++ (String.join "," <|
                        List.map String.fromInt ni.parents
                   )
                ++ ")]\n\n"

        IR ->
            PL_SS.splToString ni.fs
                ++ "     ["
                ++ "→←("
                ++ (String.join "," <|
                        List.map String.fromInt ni.parents
                   )
                ++ ")]\n\n"

        TR ->
            "◯     []\n\n"

        INITR ->
            String.fromInt ni.id
                ++ ":  "
                ++ PL_SS.splToString ni.fs
                ++ "     [initial]\n\n"


{-| It gives a JSON object with the content of the tableau.
-}
semanticTableauToJSON : PLSemanticTableau -> Value
semanticTableauToJSON t =
    case GTree.root t of
        Just ( l, ch ) ->
            let
                children =
                    JSONE.list semanticTableauToJSON ch
            in
            semanticTableauNodeToJSON l children

        Nothing ->
            JSONE.null


semanticTableauNodeToJSON : { id : Int, fs : SetPL, parents : List Int, rule : STRule } -> Value -> Value
semanticTableauNodeToJSON ni children =
    case ni.rule of
        AR ->
            JSONE.object
                [ ( "name", JSONE.int ni.id )
                , ( "label", JSONE.string <| PL_SS.splToString ni.fs )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝛼("
                            ++ (String.join "," <|
                                    List.map String.fromInt ni.parents
                               )
                            ++ ")"
                  )
                , ( "children", children )
                ]

        BR ->
            JSONE.object
                [ ( "name", JSONE.int ni.id )
                , ( "label", JSONE.string <| PL_SS.splToString ni.fs )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝛽("
                            ++ (String.join "," <|
                                    List.map String.fromInt ni.parents
                               )
                            ++ ")"
                  )
                , ( "children", children )
                ]

        DNR ->
            JSONE.object
                [ ( "name", JSONE.int ni.id )
                , ( "label", JSONE.string <| PL_SS.splToString ni.fs )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝒹𝒩("
                            ++ (String.join "," <|
                                    List.map String.fromInt ni.parents
                               )
                            ++ ")"
                  )
                , ( "children", children )
                ]

        IR ->
            JSONE.object
                [ ( "name", JSONE.int ni.id )
                , ( "label", JSONE.string <| PL_SS.fplToString Insat )
                , ( "xlabel"
                  , JSONE.string <|
                        "("
                            ++ (String.join "," <|
                                    List.map String.fromInt ni.parents
                               )
                            ++ ")"
                  )
                , ( "children", children )
                ]

        TR ->
            JSONE.object
                [ ( "name", JSONE.int ni.id )
                , ( "label", JSONE.string "◯" )
                , ( "xlabel", JSONE.string "" )
                , ( "children", children )
                ]

        INITR ->
            JSONE.object
                [ ( "name", JSONE.int ni.id )
                , ( "label", JSONE.string <| PL_SS.splToString ni.fs )
                , ( "xlabel", JSONE.string "initial" )
                , ( "children", children )
                ]


{-| It gives a DOT representation for the tableau.
-}
semanticTableauToDOT : PLSemanticTableau -> String
semanticTableauToDOT t =
    "digraph{" ++ (Tuple.first <| semanticTableauNodeToDOTAux 0 -1 t) ++ "}"


semanticTableauNodeToDOTAux : Int -> Int -> PLSemanticTableau -> ( String, Int )
semanticTableauNodeToDOTAux gid p t =
    case GTree.root t of
        Just ( l, ch ) ->
            semanticTableauNodeToDOTAux2 gid p l ch

        Nothing ->
            ( "", -1 )


semanticTableauNodeToDOTAux2 : Int -> Int -> { id : Int, fs : SetPL, parents : List Int, rule : STRule } -> List (Tree { id : Int, fs : SetPL, parents : List Int, rule : STRule }) -> ( String, Int )
semanticTableauNodeToDOTAux2 gid p ni children =
    case children of
        [ c ] ->
            let
                ( res, lgid ) =
                    semanticTableauNodeToDOTAux (gid + 1) gid c
            in
            case ni.rule of
                AR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛼(" ++ (String.join "," <| List.map String.fromInt ni.parents) ++ ")") ++ "\"];") ++ res, lgid )

                BR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛽(" ++ (String.join "," <| List.map String.fromInt ni.parents) ++ ")") ++ "\"];") ++ res, lgid )

                DNR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝒹𝒩(" ++ (String.join "," <| List.map String.fromInt ni.parents) ++ ")") ++ "\"];") ++ res, lgid )

                INITR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ res, lgid )

                _ ->
                    ( "", -2 )

        [ c1, c2 ] ->
            let
                ( res1, lgid1 ) =
                    semanticTableauNodeToDOTAux (gid + 1) gid c1
            in
            let
                ( res2, lgid2 ) =
                    semanticTableauNodeToDOTAux (lgid1 + 1) gid c2
            in
            case ni.rule of
                AR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛼(" ++ (String.join "," <| List.map String.fromInt ni.parents) ++ ")") ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                BR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛽(" ++ (String.join "," <| List.map String.fromInt ni.parents) ++ ")") ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                DNR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝒹𝒩(" ++ (String.join "," <| List.map String.fromInt ni.parents) ++ ")") ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                INITR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.splToString ni.fs ++ "\"];\n" ++ res1 ++ "\n" ++ res2, lgid2 )

                _ ->
                    ( "", -2 )

        _ ->
            case ni.rule of
                IR ->
                    ( String.fromInt gid ++ " [label=\"" ++ PL_SS.fplToString Insat ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ (String.join "→←" <| List.map String.fromInt ni.parents) ++ "\"];"), gid )

                TR ->
                    ( String.fromInt gid ++ " [label=\"◯\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid), gid )

                _ ->
                    ( "", -2 )


{-| It gives a DOT representation for the tableau. It allows defining some styles for nodes (node[nodesS]) and edges. 
    
        semanticTableauToDOTwithStyles t "node [shape=box, color=blue, style=\"rounded, filled\"] \n edge [color=\"aquamarine4\"]"
-}
semanticTableauToDOTwithStyles : PLSemanticTableau -> String -> String
semanticTableauToDOTwithStyles t styles =
    "digraph{ \n\n"
     ++ styles
     ++ "\n\n" ++ (Tuple.first <| semanticTableauNodeToDOTAux 0 -1 t) ++ "}"

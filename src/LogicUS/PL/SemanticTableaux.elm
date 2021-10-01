module LogicUS.PL.SemanticTableaux exposing
    ( FormulaPLType, PLSemanticTableau
    , fplType, fplComponents
    , splAllLiterals, splRemoveTaut, splSearchContradiction, splSearchDN, splSearchAlpha, splSearchBeta, splExpandDN, splExpandAlpha, splExpandBeta
    , semanticTableau, semanticTableauModels
    , semanticTableauToString, semanticTableauToDOT
    )

{-| The module provides the elementary tools for building the semantic tableau of a set of PL formulas.


# Definition Types

@docs FormulaPLType, PLSemanticTableau


# Formulas types and components

@docs fplType, fplComponents


# Semantic Tableau operations

@docs splAllLiterals, splRemoveTaut, splSearchContradiction, splSearchDN, splSearchAlpha, splSearchBeta, splExpandDN, splExpandAlpha, splExpandBeta


# Semantic Tableau algorithm and models

@docs semanticTableau, semanticTableauModels


# Fuctions for representation

@docs semanticTableauToString, semanticTableauToDOT

-}

--===========--
--  IMPORTS  --
--===========--

import Graph exposing (Graph, Node)
import Graph.DOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.AUX.AuxiliarFunctions exposing (uniqueConcatList)
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


{-| Defines the PL Semantic Tableau type as a Graph whose node labels are pairs of an integer (0: internal node, 1: open leaf, -1: closed leaf) and the PL set considered in the corresponding node; and the edge labels are defined as pairs of the applied rule (A, B, DN, L, I, T) and the list of indexes of the formulas on which the rule is applied.
-}
type alias PLSemanticTableau =
    Graph ( Int, SetPL ) ( FormulaPLType, List Int )



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


{-| It generates the complete SemanticTableaux as a Graph, which is renderizable with representations methods.

    splSemanticTableau fs4 == Graph (Inner { left = Leaf { key = 0, value = { incoming = Empty, node = { id = 0, label = ( 0, [ Atom "a", Neg (Atom "b"), Conj (Atom "a") (Atom "b"), Disj (Atom "a") (Atom "b"), Neg (Equi (Atom "a") (Atom "b")) ] ) }, outgoing = Leaf { key = 1, value = ( A, [ 2 ] ) } } }, prefix = { branchingBit = 1, prefixBits = 0 }, right = Leaf { key = 1, value = { incoming = Leaf { key = 0, value = ( A, [ 2 ] ) }, node = { id = 1, label = ( -1, [ Atom "a", Neg (Atom "b"), Disj (Atom "a") (Atom "b"), Neg (Equi (Atom "a") (Atom "b")), Atom "b" ] ) }, outgoing = Empty } }, size = 2 })

-}
semanticTableau : SetPL -> PLSemanticTableau
semanticTableau fs =
    let
        splSemanticTableauBuilder xs nid =
            case splSearchContradiction xs of
                Just _ ->
                    ( [ Graph.Node nid ( -1, xs ) ], [] )

                Nothing ->
                    let
                        currentNode =
                            Graph.Node nid ( 0, xs )
                    in
                    case splSearchDN xs of
                        Just ( i, f ) ->
                            let
                                ( nodes, edges ) =
                                    splSemanticTableauBuilder (splExpandDN xs f) (nid + 1)
                            in
                            ( currentNode :: nodes, Graph.Edge nid (nid + 1) ( DN, [ i ] ) :: edges )

                        Nothing ->
                            case splSearchAlpha xs of
                                Just ( i, f ) ->
                                    let
                                        ( nodes, edges ) =
                                            splSemanticTableauBuilder (splExpandAlpha xs f) (nid + 1)
                                    in
                                    ( currentNode :: nodes, Graph.Edge nid (nid + 1) ( A, [ i ] ) :: edges )

                                Nothing ->
                                    case splSearchBeta xs of
                                        Just ( i, f ) ->
                                            let
                                                expansion =
                                                    splExpandBeta xs f
                                            in
                                            let
                                                alt1 =
                                                    Tuple.first expansion

                                                alt2 =
                                                    Tuple.second expansion
                                            in
                                            let
                                                ( nodes1, edges1 ) =
                                                    splSemanticTableauBuilder alt1 (nid + 1)
                                            in
                                            let
                                                nextid =
                                                    nid + List.length nodes1 + 1
                                            in
                                            let
                                                ( nodes2, edges2 ) =
                                                    splSemanticTableauBuilder alt2 nextid
                                            in
                                            ( currentNode :: (nodes1 ++ nodes2), [ Graph.Edge nid (nid + 1) ( B, [ i ] ), Graph.Edge nid nextid ( B, [ i ] ) ] ++ edges1 ++ edges2 )

                                        Nothing ->
                                            ( [ Graph.Node nid ( 1, xs ) ], [] )
    in
    let
        ( ns, es ) =
            splSemanticTableauBuilder (uniqueConcatList [] fs) 0
    in
    Graph.fromNodesAndEdges ns es


{-| It extracts all the models from a semantic tableau.

    splSemanticTableau fs4 |> plSemanticTableauModels == []

    fs5 = [Disj f1 f2, Neg(Equi f1 f2)]
    splSemanticTableau fs5 |> plSemanticTableauModels == [["a"],["b"]]

-}
semanticTableauModels : PLSemanticTableau -> List Interpretation
semanticTableauModels st =
    let
        symbs =
            (Maybe.withDefault (Node 0 ( 0, [] )) <| List.head <| Graph.nodes st).label |> Tuple.second |> PL_SS.splSymbols

        openLeaves =
            List.foldr
                (\x ac ->
                    if Tuple.first x.label == 1 then
                        Tuple.second x.label :: ac

                    else
                        ac
                )
                []
            <|
                Graph.nodes st
    in
    List.sort <| LE.unique <| List.concat <| List.map (\ls -> PL_SS.interpretationsFromSymbolsAndLiterals symbs ls) openLeaves



-----------------------
--   Repr functions   -
-----------------------


{-| It gives the String representation of a tableau.

    splSemanticTableau fs4 |> splSemanticTableauToString == "Graph [Node 0 ({a, ¬ b, ( a ∧ b ), ( a ∨ b ), ¬ ( a ↔ b )}), Node 1 ({a, ¬ b, ( a ∨ b ), ¬ ( a ↔ b ), b}), Node 2 (×)] [Edge 1->2 (I (2, 5)), Edge 0->1 (α (3))]"

-}
semanticTableauToString : PLSemanticTableau -> String
semanticTableauToString t =
    let
        toStringNode =
            \( i, fs2 ) ->
                Just
                    (if i == -2 then
                        "×"

                     else if i == 2 then
                        "◯"

                     else
                        PL_SS.splToString fs2
                    )

        toStringEdge =
            \( ftype, is ) ->
                Just
                    (case ftype of
                        L ->
                            "L"

                        DN ->
                            "dN (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        A ->
                            "α (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        B ->
                            "β (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        I ->
                            "I (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        T ->
                            "T"
                    )
    in
    let
        newLeaves =
            List.indexedMap
                (\j n ->
                    let
                        nid =
                            n.id

                        ( i, fs2 ) =
                            n.label
                    in
                    ( Graph.Node (Graph.size t + j) ( 2 * i, [] )
                    , Graph.Edge nid
                        (Graph.size t + j)
                        (if i == 1 then
                            ( L, [] )

                         else
                            ( I, Maybe.withDefault [] (splSearchContradiction fs2) )
                        )
                    )
                )
                (List.filter (\n -> Tuple.first n.label /= 0) <| Graph.nodes t)
    in
    Graph.toString toStringNode toStringEdge <| Graph.fromNodesAndEdges (Graph.nodes t ++ List.map Tuple.first newLeaves) (Graph.edges t ++ List.map Tuple.second newLeaves)


{-| It gives a String representation of a Tabbleau using DOT notation, which is renderizable with a GraphViz viewer.

    splSemanticTableau fs4 |> splSemanticTableauToDOT == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  0 -> 1 [label=\"α (3)\"]\n  1 -> 2 [label=\"I (2, 5)\"]\n\n  0 [label=\"{a, ¬ b, ( a ∧ b ), ( a ∨ b ), ¬ ( a ↔ b )}\"]\n  1 [label=\"{a, ¬ b, ( a ∨ b ), ¬ ( a ↔ b ), b}\"]\n  2 [label=\"×\"]\n}"

-}
semanticTableauToDOT : PLSemanticTableau -> String
semanticTableauToDOT t =
    let
        toStringNode =
            \( i, fs2 ) ->
                Just <|
                    if i == -2 then
                        "🗴"

                    else if i == 2 then
                        "⭘"

                    else
                        PL_SS.splToString fs2

        toStringEdge =
            \( ftype, is ) ->
                Just <|
                    case ftype of
                        L ->
                            "L"

                        DN ->
                            "dN (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        A ->
                            "α (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        B ->
                            "β (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        I ->
                            "I (" ++ String.join ", " (List.map (\i -> String.fromInt (i + 1)) is) ++ ")"

                        T ->
                            "T"

        myStyles =
            { defaultStyles | node = "shape=box, color=white, fontcolor=black", edge = "dir=none, color=blue, fontcolor=blue" }
    in
    let
        newLeaves =
            List.indexedMap
                (\j n ->
                    let
                        nid =
                            n.id

                        ( i, fs2 ) =
                            n.label
                    in
                    ( Graph.Node (Graph.size t + j) ( 2 * i, [] )
                    , Graph.Edge nid
                        (Graph.size t + j)
                        (if i == 1 then
                            ( L, [] )

                         else
                            ( I, Maybe.withDefault [] (splSearchContradiction fs2) )
                        )
                    )
                )
                (List.filter (\n -> Tuple.first n.label /= 0) <| Graph.nodes t)
    in
    String.replace "\n" "" <| String.replace "\"" ">" <| String.replace "=\"" "=<" <| Graph.DOT.outputWithStyles myStyles toStringNode toStringEdge <| Graph.fromNodesAndEdges (Graph.nodes t ++ List.map Tuple.first newLeaves) (Graph.edges t ++ List.map Tuple.second newLeaves)

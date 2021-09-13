module LogicUS.PL.DPLL exposing
    ( DPLLTableau
    , dpll, dpllTableauModels
    , dpllTableauToString, dpllTableauToDOT
    )

{-| The module provides the tools for applying the DPLL algorithm to solve the fesibility of a set of propositional clauses and calculates its models if they exist.


# DPLL TABLEAU

@docs DPLLTableau


# DPLL Algorithm

@docs dpll, dpllTableauModels


# Representation

@docs dpllTableauToString, dpllTableauToDOT

-}

--===========--
--  IMPORTS  --
--===========--

import Graph exposing (Edge, Graph, Node)
import Graph.DOT exposing (defaultStyles)
import IntDict
import List.Extra as LE
import LogicUS.PL.Clauses as PL_CL exposing (ClausePL, ClausePLLiteral)
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), Interpretation, PSymb)


{-| Defines the DPLL Tableau type as a Graph whose node labels are pairs of an integer (0: internal node, 1: open leaf, -1: closed leaf) and the set of PL clauses considered in the corresponding node; and a edge label is just the literal which is propagated.
-}
type alias DPLLTableau =
    Graph ( Int, List ClausePL ) ClausePLLiteral


{-| It computes DPLL algorithm given the result and the process as a DPLL Tableau

    cs1 =
        [ [ ( "r", False ), ( "p", True ), ( "q", True ) ], [ ( "p", False ), ( "r", True ) ], [ ( "q", False ), ( "r", True ) ], [ ( "s", False ), ( "p", True ) ], [ ( "s", True ), ( "r", True ), ( "t", True ) ], [ ( "p", False ) ], [ ( "q", False ) ], [ ( "t", False ) ] ]

    t1 =
        dpll cs1

    cs2 =
        [ [ ( "r", False ), ( "p", True ), ( "q", True ) ], [ ( "p", False ), ( "r", True ) ], [ ( "q", False ), ( "r", True ) ], [ ( "s", False ), ( "p", True ) ], [ ( "s", True ), ( "r", True ), ( "t", True ) ], [ ( "p", False ) ] ]

    t2 =
        dpll cs2

-}
dpll : List ClausePL -> DPLLTableau
dpll cs =
    let
        dpllAux clauses nid =
            let
                propagation ( lsymb, lsign ) =
                    List.foldl
                        (\x ac ->
                            if List.member ( lsymb, lsign ) x then
                                ac

                            else
                                ac ++ [ List.filter (\( ysymb, _ ) -> ysymb /= lsymb) x ]
                        )
                        []
                        clauses
                        |> PL_CL.csplRemoveSubsumedClauses
            in
            if List.isEmpty clauses then
                ( [ Node nid ( 1, clauses ) ], [] )

            else if List.any (\c -> List.isEmpty c) clauses then
                ( [ Node nid ( -1, clauses ) ], [] )

            else
                case List.head <| List.filter (\x -> List.length x == 1) clauses of
                    Just [ l ] ->
                        let
                            new_clauses =
                                propagation l
                        in
                        let
                            ( nodes, edges ) =
                                dpllAux new_clauses (nid + 1)
                        in
                        ( Node nid ( 0, clauses ) :: nodes, Edge nid (nid + 1) l :: edges )

                    _ ->
                        let
                            psymbsOcurrFreq =
                                List.concat clauses
                                    |> LE.gatherEqualsBy Tuple.first
                                    |> List.map (\( x, xs ) -> ( Tuple.first x, List.length xs ))
                        in
                        case LE.maximumBy Tuple.second psymbsOcurrFreq of
                            Just ( lsymb, _ ) ->
                                let
                                    new_clauses1 =
                                        propagation ( lsymb, True )

                                    new_clauses2 =
                                        propagation ( lsymb, False )
                                in
                                let
                                    ( nodes1, edges1 ) =
                                        dpllAux new_clauses1 (nid + 1)
                                in
                                let
                                    next_id =
                                        nid + List.length nodes1 + 1
                                in
                                let
                                    ( nodes2, edges2 ) =
                                        dpllAux new_clauses2 next_id
                                in
                                ( Node nid ( 0, clauses ) :: (nodes1 ++ nodes2), [ Edge nid (nid + 1) ( lsymb, True ), Edge nid next_id ( lsymb, False ) ] ++ edges1 ++ edges2 )

                            Nothing ->
                                ( [ Node nid ( -1, clauses ) ], [] )

        new_cs =
            PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            dpllAux new_cs 0
    in
    Graph.fromNodesAndEdges nodes edges


{-| Gets the Tableau DPLL models. It requires a set of reference symbols that are added to those present in the tableau since in the transformation to clauses some symbols may have disappeared.

    dpllTableauModels [] t1 == []

    dpllTableauModels [] t2 == [ [ "q", "r" ], [ "q", "r", "t" ], [ "t" ] ]

-}
dpllTableauModels : List PSymb -> DPLLTableau -> List Interpretation
dpllTableauModels refSymbs dt =
    let
        openLeaf =
            List.foldl
                (\x ac ->
                    if Tuple.first x.label == 1 then
                        ac ++ [ x.id ]

                    else
                        ac
                )
                []
            <|
                Graph.nodes dt

        predecessors =
            IntDict.fromList <| List.map (\x -> ( x.to, ( x.from, x.label ) )) <| Graph.edges dt

        symbs =
            LE.unique <|
                ((Maybe.withDefault (Node 0 ( 0, [] )) <| List.head <| Graph.nodes dt).label |> Tuple.second |> PL_CL.csplSymbols)
                    ++ refSymbs
    in
    let
        getDPLLPathToWithpredecessors nid =
            case IntDict.get nid predecessors of
                Nothing ->
                    []

                Just ( anid, l ) ->
                    getDPLLPathToWithpredecessors anid ++ [ PL_CL.clauseLitToLiteral l ]
    in
    List.sort <| LE.unique <| List.concat <| List.map (\nid -> PL_SS.interpretationsFromSymbolsAndLiterals symbs <| getDPLLPathToWithpredecessors nid) openLeaf


{-| Express a DPLL Tableau as a string.

    dpllTableauToString t1 == "Graph [Node 0 ({¬ r, p, q}, {¬ s, p}, {s, r, t}, {¬ p}, {¬ q}, {¬ t}), Node 1 ({¬ r, q}, {¬ s}, {s, r, t}, {¬ q}, {¬ t}), Node 2 ({¬ r, q}, {r, t}, {¬ q}, {¬ t}), Node 3 ({¬ r}, {r, t}, {¬ t}), Node 4 ({t}, {¬ t}), Node 5 (□)] [Edge 4->5 (t), Edge 3->4 (¬ r), Edge 2->3 (¬ q), Edge 1->2 (¬ s), Edge 0->1 (¬ p)]"

    dpllTableauToString t2 == "Graph [Node 0 ({¬ r, p, q}, {¬ q, r}, {¬ s, p}, {s, r, t}, {¬ p}), Node 1 ({¬ r, q}, {¬ q, r}, {¬ s}, {s, r, t}), Node 2 ({¬ r, q}, {¬ q, r}, {r, t}), Node 3 ({q}), Node 4 (◯), Node 5 ({¬ q}, {t}), Node 6 ({t}), Node 7 (◯)] [Edge 6->7 (t), Edge 5->6 (¬ q), Edge 3->4 (q), Edge 2->5 (¬ r), Edge 2->3 (r), Edge 1->2 (¬ s), Edge 0->1 (¬ p)]"

-}
dpllTableauToString : DPLLTableau -> String
dpllTableauToString g =
    let
        toStringNode =
            \( i, cs ) ->
                case i of
                    0 ->
                        Just <| String.join ", " <| List.map PL_CL.cplToString cs

                    1 ->
                        Just "◯"

                    _ ->
                        Just "□"

        toStringEdge =
            \l -> (Just << PL_SS.fplToString << PL_CL.clauseLitToLiteral) l
    in
    Graph.toString toStringNode toStringEdge g


{-| Express a DPLL Tableau as a string in DOT format that is viewable with a GraphViz Render.

**Note:** If you are using elm repl, before introducing the code you must replace _\\n_ by _\\n_ and _\\"_ by _"_ in a simple text editor.

    dpllTableauToDOT t1 == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  0 -> 1 [label=\"¬ p\"]\n  1 -> 2 [label=\"¬ s\"]\n  2 -> 3 [label=\"¬ q\"]\n  3 -> 4 [label=\"¬ r\"]\n  4 -> 5 [label=\"t\"]\n\n  0 [label=\"{¬ r, p, q}, {¬ s, p}, {s, r, t}, {¬ p}, {¬ q}, {¬ t}\"]\n  1 [label=\"{¬ r, q}, {¬ s}, {s, r, t}, {¬ q}, {¬ t}\"]\n  2 [label=\"{¬ r, q}, {r, t}, {¬ q}, {¬ t}\"]\n  3 [label=\"{¬ r}, {r, t}, {¬ t}\"]\n  4 [label=\"{t}, {¬ t}\"]\n  5 [label=\"□\"]\n}"

    dpllTableauToDOT t2 = "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  0 -> 1 [label=\"¬ p\"]\n  1 -> 2 [label=\"¬ s\"]\n  2 -> 3 [label=\"r\"]\n  2 -> 5 [label=\"¬ r\"]\n  3 -> 4 [label=\"q\"]\n  5 -> 6 [label=\"¬ q\"]\n  6 -> 7 [label=\"t\"]\n\n  0 [label=\"{¬ r, p, q}, {¬ q, r}, {¬ s, p}, {s, r, t}, {¬ p}\"]\n  1 [label=\"{¬ r, q}, {¬ q, r}, {¬ s}, {s, r, t}\"]\n  2 [label=\"{¬ r, q}, {¬ q, r}, {r, t}\"]\n  3 [label=\"{q}\"]\n  4 [label=\"◯\"]\n  5 [label=\"{¬ q}, {t}\"]\n  6 [label=\"{t}\"]\n  7 [label=\"◯\"]\n}"

-}
dpllTableauToDOT : DPLLTableau -> String
dpllTableauToDOT g =
    let
        myStyles =
            { defaultStyles | node = "shape=box, color=white, fontcolor=black", edge = "dir=none, color=blue, fontcolor=blue" }

        toStringNode =
            \( i, cs ) ->
                case i of
                    0 ->
                        Just <| String.join ", " <| List.map PL_CL.cplToString cs

                    1 ->
                        Just "◯"

                    _ ->
                        Just "□"

        toStringEdge =
            \l -> (Just << PL_SS.fplToString << PL_CL.clauseLitToLiteral) l
    in
    String.replace "\n" "" <| String.replace "\"" ">" <| String.replace "=\"" "=<" <| Graph.DOT.outputWithStyles myStyles toStringNode toStringEdge g

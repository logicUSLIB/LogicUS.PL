module LogicUS.PL.ForeignOperators exposing (..)

import List.Extra as LE
import LogicUS.PL.AuxiliarFunctions exposing (powerset, setMinus)
import LogicUS.PL.Clauses exposing (splToClauses)
import LogicUS.PL.Resolution exposing (csplSCFResolution)
import LogicUS.PL.SemanticTableaux exposing (semanticTableau, semanticTableauModels)
import LogicUS.PL.SyntaxSemantics exposing (..)



{- It simplifies the tautology or insat symbol (if it proceeds). It operates only in the first level, that is, it does not go recursively over the formula. -}


sigma : FormulaPL -> FormulaPL
sigma g =
    case g of
        Neg Taut ->
            Insat

        Neg Insat ->
            Taut

        Conj Taut h ->
            h

        Conj h Taut ->
            h

        Conj Insat _ ->
            Insat

        Conj _ Insat ->
            Insat

        Disj Taut _ ->
            Taut

        Disj _ Taut ->
            Taut

        Disj Insat h ->
            h

        Disj h Insat ->
            h

        Impl Taut h ->
            h

        Impl _ Taut ->
            Taut

        Impl Insat _ ->
            Taut

        Impl h Insat ->
            sigma (Neg h)

        Equi h Taut ->
            h

        Equi Taut h ->
            h

        Equi Insat h ->
            sigma (Neg h)

        Equi h Insat ->
            sigma (Neg h)

        _ ->
            g



{- Having in cosideration that in canonic foreign operator δ⁰ₚ F ≣ σ(F{p/⊤} ∨ F{p/⊥}) then we separate the operation in two parts, performing sigma simplifications by the time the substitutions are maked. -}


canonicFO : FormulaPL -> PSymb -> FormulaPL
canonicFO f p =
    if List.member p (fplSymbols f) then
        sigma (Disj (canonicFOT f p) (canonicFOF f p))

    else
        f


canonicFOT : FormulaPL -> PSymb -> FormulaPL
canonicFOT f p =
    case f of
        Atom q ->
            if p == q then
                Taut

            else
                Atom q

        Neg g ->
            sigma (Neg (canonicFOT g p))

        Conj g h ->
            sigma (Conj (canonicFOT g p) (canonicFOT h p))

        Disj g h ->
            sigma (Disj (canonicFOT g p) (canonicFOT h p))

        Impl g h ->
            sigma (Impl (canonicFOT g p) (canonicFOT h p))

        Equi g h ->
            sigma (Equi (canonicFOT g p) (canonicFOT h p))

        _ ->
            f


canonicFOF : FormulaPL -> PSymb -> FormulaPL
canonicFOF f p =
    case f of
        Atom q ->
            if p == q then
                Insat

            else
                Atom q

        Neg g ->
            sigma (Neg (canonicFOF g p))

        Conj g h ->
            sigma (Conj (canonicFOF g p) (canonicFOF h p))

        Disj g h ->
            sigma (Disj (canonicFOF g p) (canonicFOF h p))

        Impl g h ->
            sigma (Impl (canonicFOF g p) (canonicFOF h p))

        Equi g h ->
            sigma (Equi (canonicFOF g p) (canonicFOF h p))

        _ ->
            f



{- It performs conservative retraction to the original language (taken as the set of symbols in the formulas) with forgetting the set of symbols given -}


fplConservativeRetraction : FormulaPL -> List PSymb -> FormulaPL
fplConservativeRetraction f ls =
    let
        lsf =
            List.sort <| LE.unique <| setMinus (fplSymbols f) ls
    in
    List.foldl (\p g -> canonicFO g p) f lsf


splConservativeRetraction : SetPL -> List PSymb -> SetPL
splConservativeRetraction fs ls =
    let
        lsf =
            List.sort <| LE.unique <| setMinus (splSymbols fs) ls
    in
    List.foldl (\p gs -> List.map (\g -> canonicFO g p) gs) fs lsf


harnessedConsequence : SetPL -> FormulaPL -> List PSymb -> Bool
harnessedConsequence kb f ls =
    let
        f_ =
            fplConservativeRetraction f ls
    in
    if f_ == Taut then
        False

    else
        Tuple.first <| csplSCFResolution <| splToClauses <| fplNegation f_ :: kb


informativeSublanguages : FormulaPL -> List PSymb -> List (List PSymb)
informativeSublanguages f ls =
    List.filter (\ls0 -> Taut /= fplConservativeRetraction f ls0) <| powerset ls


omega : List PSymb -> SetPL -> FormulaPL -> Float
omega ls ks f =
    let
        mod_ks =
            semanticTableauModels <| semanticTableau ks

        f_ls =
            fplConservativeRetraction f ls
    in
    (toFloat <| List.length <| List.filter (\i -> fplValuation f_ls i) mod_ks) / (toFloat <| List.length mod_ks)


omegaM : SetPL -> FormulaPL -> List PSymb -> ( Float, List (List PSymb) )
omegaM ks f ls =
    let
        ilf =
            informativeSublanguages f ls
    in
    let
        omega_ilf =
            List.map (\ls0 -> ( omega ls0 ks f, ls0 )) ilf
    in
    List.foldl
        (\( w, ls0 ) ( wMax, lsMax ) ->
            if w < wMax then
                ( wMax, lsMax )

            else if w > wMax then
                ( w, [ ls0 ] )

            else if List.any (\lsMax_i -> List.isEmpty <| setMinus ls0 lsMax_i) lsMax then
                ( wMax, lsMax )

            else
                ( w, List.filter (\lsMax_i -> not <| List.isEmpty <| setMinus lsMax_i ls0) lsMax ++ [ ls0 ] )
        )
        ( 0, [] )
        omega_ilf

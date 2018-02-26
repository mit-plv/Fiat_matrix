Require Import
        Fiat_matrix.KalmanExtraction.

Extraction Language Haskell.

Extract Inductive sumbool => Bool [ True False ].

Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellBasic.
Extract Inlined Constant float_t => "KalmanAxioms.Float_t".


Extraction "haskell/Kalman.hs" KalmanInit KalmanPredict KalmanUpdate.

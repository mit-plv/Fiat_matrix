Require Import Kalman.
Require Import
        Coq.Lists.List
        Coq.Strings.String
        Coq.Setoids.Setoid
        Coq.Arith.PeanoNat
        Coq.omega.Omega
        Coq.setoid_ring.Ring
        Coq.setoid_ring.Ring_theory
        Matrix
        SparseMatrix
        DenseMatrix
        FiatHelpers
        MyHelpers
        MatrixLemmas.

Section Float.
  Axiom float_t: Type.

  Axiom float_zero: float_t.
  Axiom float_one : float_t.

  Axiom float_opp : float_t -> float_t.
  Axiom float_plus : float_t -> float_t -> float_t.
  Axiom float_minus : float_t -> float_t -> float_t.
  Axiom float_times : float_t -> float_t -> float_t.
  Axiom float_div : float_t -> float_t -> float_t.
  Axiom float_inv: float_t -> float_t.
  Axiom float_eq_dec: forall x y: float_t, { x = y } + { x <> y }.

  Require Import Coq.setoid_ring.Field.
  Axiom float_field : field_theory float_zero float_one float_plus float_times float_minus float_opp float_div float_inv eq.

  Definition MEfloat :=
    {| MEt := float_t;

       MEzero := float_zero;
       MEone := float_one;

       MEopp := float_opp;
       MEplus := float_plus;
       MEminus := float_minus;
       MEtimes := float_times;
       MEdiv := float_div;
       MEinv := float_inv;
       MEeqdec := float_eq_dec;

       MEfield := float_field |}.
End Float.

Arguments KalmanImpl /.

Arguments callcADTConstructor / .
Arguments ComputationalADT.cConstructors / .
Arguments ComputationalADT.pcConstructors / .
Arguments callcADTMethod / .
Arguments ComputationalADT.cMethods / .
Arguments ComputationalADT.pcMethods / .

(* (* Arguments MEReals /. *) *)
(* Arguments MEt / . *)
(* Arguments MEzero / . *)
(* Arguments MEone / . *)
(* Arguments MEopp / . *)
(* Arguments MEplus / . *)
(* Arguments MEminus / . *)
(* Arguments MEtimes / . *)
(* Arguments MEdiv / . *)
(* Arguments MEinv / . *)

(* Transparent DenseMatrix. *)
(* (* Arguments DenseMatrix /. *) *)
(* Arguments Mt / . *)
(* Arguments Mget / . *)
(* Arguments Mtimes / . *)
(* Arguments Mfill / . *)
(* Arguments Melementwise_op / . *)

Arguments MVtimes /.
Arguments Vplus /.

Open Scope string_scope.

Section KalmanExtraction.
  Existing Instance MEfloat.

  Definition rep n
    : Type :=
    Eval simpl in ComputationalADT.cRep (KalmanImpl n).

  Definition KalmanInit {n} (init : KalmanState n)
    : rep n :=
    Eval simpl in (CallConstructor (KalmanImpl n) "Init" init).

  Definition KalmanPredict {n} (r: rep n) (F: SDM n) (B: SDM n) (Q: SDM n) (u: Vt n)
    : rep n * KalmanState n :=
    Eval simpl in (CallMethod (KalmanImpl n) "Predict" r F B Q u).

  Definition KalmanUpdate {n} (r: rep n) (H: SDM n) (R: SDM n) (z: Vt n)
    : rep n :=
    Eval simpl in (fst (CallMethod (KalmanImpl n) "Update" r H R z)).
End KalmanExtraction.

Extraction Inline blocked_let.
(* Extraction Inline MVtimes Vplus. *)
Extraction Inline Mt Mget Mtimes Mfill Melementwise_op.
Extraction Inline MEt MEzero MEone MEopp MEplus MEminus MEtimes MEdiv MEinv.

(* Extraction KalmanInit. *)
(* Extraction KalmanPredict. *)
(* Extraction KalmanUpdate. *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.

Extract Inlined Constant float_t => "KalmanAxioms.float_t".
Extract Inlined Constant float_zero => "KalmanAxioms.float_zero".
Extract Inlined Constant float_one => "KalmanAxioms.float_one".
Extract Inlined Constant float_opp => "KalmanAxioms.float_opp".
Extract Inlined Constant float_plus => "KalmanAxioms.float_plus".
Extract Inlined Constant float_minus => "KalmanAxioms.float_minus".
Extract Inlined Constant float_times => "KalmanAxioms.float_times".
Extract Inlined Constant float_div => "KalmanAxioms.float_div".
Extract Inlined Constant float_inv => "KalmanAxioms.float_inv".
Extract Inlined Constant float_eq_dec => "KalmanAxioms.float_eq_dec".

Extract Inlined Constant Cholesky_DC => "KalmanAxioms.cholesky_DC".
Extract Inlined Constant dense_sparse_mul_to_sparse => "KalmanAxioms.dense_sparse_mul_to_sparse".
Extract Inlined Constant sparse_dense_mul => "KalmanAxioms.sparse_dense_mul".
Extract Inlined Constant dense_sparse_mul => "KalmanAxioms.dense_sparse_mul".
Extract Inlined Constant solveR_upper => "KalmanAxioms.solveR_upper".
Extract Inlined Constant solveR_lower => "KalmanAxioms.solveR_lower".

Extraction "kalman.ml" KalmanInit KalmanPredict KalmanUpdate.

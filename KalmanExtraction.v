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

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.

(* Axioms *)

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
Extract Inlined Constant log_two_pi => "KalmanAxioms.log_two_pi".

Extract Inlined Constant Cholesky_DC => "KalmanAxioms.cholesky_DC".
Extract Inlined Constant dense_sparse_mul_to_sparse => "KalmanAxioms.dense_sparse_mul_to_sparse".
Extract Inlined Constant sparse_dense_mul => "KalmanAxioms.sparse_dense_mul".
Extract Inlined Constant dense_sparse_mul => "KalmanAxioms.dense_sparse_mul".
Extract Inlined Constant solveR_upper => "KalmanAxioms.solveR_upper".
Extract Inlined Constant solveR_lower => "KalmanAxioms.solveR_lower".

Extract Inlined Constant logdet => "KalmanAxioms.logdet".
Extract Inlined Constant inversion => "KalmanAxioms.inversion".

(** * Constants that we want to implement in OCaml **)

(** This is the shorter, but slightly less efficient version: *)

(* Extract Inlined Constant SparseMatrix => "KalmanAxioms.sparse_matrix". *)
(* Extract Inlined Constant DenseMatrix => "KalmanAxioms.dense_matrix". *)

(** This is the longer version, more efficient version: *)

Transparent DenseMatrix.
Extraction Inline DenseMatrix.
Extract Inlined Constant DenseMatrix_get => "KalmanAxioms.dense_get".
Extract Inlined Constant DenseMatrix_mul => "KalmanAxioms.dense_mul".
Extract Inlined Constant DenseMatrix_fill => "KalmanAxioms.dense_fill".
Extract Inlined Constant DenseMatrix_elementwise_op => "KalmanAxioms.dense_elementwise_op".

Transparent SparseMatrix.
Extraction Inline SparseMatrix.
Extract Inlined Constant SparseMatrix_get => "KalmanAxioms.sparse_get".
Extract Inlined Constant SparseMatrix_mul => "KalmanAxioms.sparse_mul".
Extract Inlined Constant SparseMatrix_fill => "KalmanAxioms.sparse_fill".
Extract Inlined Constant SparseMatrix_elementwise_op => "KalmanAxioms.sparse_elementwise_op".

Arguments Mt / .
Arguments Mget / .
Arguments Mtimes / .
Arguments Mfill / .
Arguments Melementwise_op / .

(** * Constants that we don't want to see in the final code **)

(** Using extraction inline is typically not enough; the following ensures that
    we can do most simplifications using the [simpl] tactic **)
Arguments KalmanImpl /.
Arguments callcADTConstructor / .
Arguments ComputationalADT.cConstructors / .
Arguments ComputationalADT.pcConstructors / .
Arguments callcADTMethod / .
Arguments ComputationalADT.cMethods / .
Arguments ComputationalADT.pcMethods / .

(** A few things can be done using extraction inline, though: *)

Extraction Inline blocked_let.

(** Inlining the accessors replaces them by direct property accesses
    ([record.field] instead of [field record]) *)
Extraction Inline Mt Mget Mtimes Mfill Melementwise_op.
Extraction Inline MEt MEzero MEone MEopp MEplus MEminus MEtimes MEdiv MEinv MEeqdec.

(** * And now the actual extraction:  *)

Open Scope string_scope.

Transparent blocked_let.
Ltac simplify term :=
  let term := (eval simpl in term) in
  let term := (eval cbv beta iota delta [blocked_let] in term) in
  exact term.
Opaque blocked_let.

Section KalmanExtraction.
  Existing Instance MEfloat.

  Definition rep m n : Type :=
    ltac:(simplify (ComputationalADT.cRep (KalmanImpl m n))).

  Definition KalmanInit {m n} (init : KalmanState n)
    : rep m n :=
    ltac:(simplify (CallConstructor (KalmanImpl m n) "Init" init)).

  Definition KalmanPredict {m n} (r: rep m n) (F: SDM n) (B: SDM n) (Q: SDM n) (u: Vt n)
    : rep m n * KalmanState n :=
    ltac:(simplify (CallMethod (KalmanImpl m n) "Predict" r F B Q u)).

  Definition KalmanUpdate {m n} (r: rep m n) (H: Mt (Matrix := DenseMatrix) m n) (R: SDM n) (z: Vt m)
    : rep m n * MEt :=
    ltac:(simplify (CallMethod (KalmanImpl m n) "Update" r H R z)).
End KalmanExtraction.

(*
Extraction "kalman.ml" KalmanInit KalmanPredict KalmanUpdate.
*)
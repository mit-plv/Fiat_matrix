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
        MyHelpers.

Notation SDM n := (Mt (Matrix := DenseMatrix) n n).
Notation SSM n := (Mt (Matrix := SparseMatrix) n n).
Notation Vt n := (Mt (Matrix := DenseMatrix) n 1).

Global Opaque DenseMatrix.
Global Opaque SparseMatrix.

Section MatrixLemmas.

Context {E: MatrixElem}.

Definition transpose {n} (A : SDM n) :=
  @Mfill E DenseMatrix n n (fun i j => Mget A j i).
Definition MVtimes {n} (M: SDM n) (v: Vt n) := M @* v.
Axiom inversion : forall {n}, SDM n -> SDM n.

Global Add Parametric Morphism n: (MVtimes ) with
      signature (Meq (m:=n)(n:=n)) ==> (Meq (m:=n)(n:=1)) ==> (Meq (m:=n)(n:=1)) as MVtimes_mor.
Admitted.

Global Add Parametric Morphism n: (transpose ) with
      signature (Meq (m:=n)(n:=n)) ==> (Meq (m:=n)(n:=n)) as transpose_mor.
Admitted.


Global Add Parametric Morphism n: (inversion ) with
      signature (Meq (m:=n)(n:=n)) ==> (Meq (m:=n)(n:=n)) as inversion_mor.
Admitted.

Infix "&*" := MVtimes (at level 40, left associativity) : matrix_scope.
Definition Vplus {n} (v: Vt n) (u: Vt n):= v @+ u.
Infix "&+" := Vplus (at level 50, left associativity) : matrix_scope.

Global Add Parametric Morphism n: (Vplus ) with
      signature (Meq (m:=n)(n:=1)) ==> (Meq (m:=n)(n:=1)) ==> (Meq (m:=n)(n:=1)) as Vplus_mor.
Admitted.

Definition Vminus {n} (v: Vt n) (u: Vt n):= v @- u.
Infix "&-" := Vminus (at level 50, left associativity) : matrix_scope.

Global Add Parametric Morphism n: (Vminus ) with
      signature (Meq (m:=n)(n:=1)) ==> (Meq (m:=n)(n:=1)) ==> (Meq (m:=n)(n:=1)) as Vminus_mor.
Admitted.

Definition Id {n} := I n E DenseMatrix.

Arguments Mtimes : simpl never.


Definition sparsify {n} (A: SDM n) := @Mfill E SparseMatrix n n (fun i j => Mget A i j). 
Lemma sparsify_correct: forall n: nat, forall M : SDM n, M @= sparsify M.
Proof.
  intros.
  unfold sparsify.
  unfold "@=".
  intros. 
  rewrite Mfill_correct; try assumption.
  reflexivity.
Qed.

(* can be optimized *) 
Definition densify {n} (A: SSM n) := @Mfill E DenseMatrix n n (fun i j => Mget A i j). 
Lemma densify_correct: forall n: nat, forall M : SSM n, M @= densify M.
Proof.
  intros.
  unfold densify.
  unfold "@=".
  intros.
  rewrite Mfill_correct; try assumption.
  reflexivity.
Qed.
Lemma densify_correct_rev: forall n: nat, forall M : SSM n,  densify M @= M.
Proof.
  intros.
  unfold densify.
  unfold "@=".
  intros.
  rewrite Mfill_correct; try assumption.
  reflexivity.
Qed.

Lemma matrix_eq_commutes :
  forall (m n: nat) ME M1 M2 (m1: @Mt ME M1 m n) (m2: @Mt ME M2 m n),
    m1 @= m2 -> m2 @= m1.
Proof.
  intros.
  unfold "@=" in *.
  intros.
  rewrite H; auto.
Qed.

Axiom solveR: forall {n}, SDM n -> SDM n -> SDM n.
Axiom solveR_correct: forall n: nat, forall M1 M2:SDM n,
  M1 @* (inversion M2) = solveR M2 M1.
Lemma multi_assoc: forall n: nat, forall M1 M2 M3 : SDM n,
      (M1 @* M2) @* M3 @= M1 @* (M2 @* M3).
Proof.
  intros.
  rewrite mult_assoc.
  reflexivity.
Qed.

Axiom Cholesky_DC: forall {n}, SDM n -> SDM n.
Axiom solveR_lower: forall {n}, SDM n -> SDM n -> SDM n.
Axiom solveR_upper: forall {n}, SDM n -> SDM n -> SDM n.
Lemma ABv_assoc: forall n:nat, forall A B: SDM n, forall v : Vt n,
        MVtimes (A @* B) v @=  MVtimes A (MVtimes B v).
Proof.
  intros.
  unfold "&*".
  rewrite mult_assoc.
  reflexivity.
Qed.

Axiom Cholesky_DC_correct: forall n:nat, forall M1 M2 : SDM n, 
      solveR M1 M2 = solveR_upper (transpose (Cholesky_DC M1)) (solveR_lower (Cholesky_DC M1) M2).

Axiom Densify_correct: forall n:nat, forall M : SDM n, forall S : SSM n,
        M @= S -> M @= densify S.


Lemma Densify_correct_rev: forall n:nat, forall M : SDM n, forall S : SSM n,
        M @= densify S -> M @= S.
Proof.
  intros.
  unfold densify in H.
  unfold "@=" in *.
  intros.
  rewrite H; auto. 
  rewrite Mfill_correct; auto.
Qed.

Axiom dense_sparse_mul: forall {n}, SDM n -> SSM n -> SDM n.
Axiom dense_sparse_mul_correct: forall {n}, forall A: SDM n, forall B: SSM n, 
        dense_sparse_mul A B = A @* densify B. 
Axiom sparse_dense_mul: forall {n}, SSM n -> SDM n -> SDM n.
Axiom sparse_dense_mul_correct: forall {n}, forall A: SSM n, forall B: SDM n, 
        sparse_dense_mul A B = densify A @*  B.
Axiom dense_sparse_mul_to_sparse: forall {n}, SDM n -> SSM n -> SSM n.
Axiom dense_sparse_mul_to_sparse_correct: forall {n}, forall A: SDM n, forall B: SSM n, 
        sparsify (dense_sparse_mul A B) = dense_sparse_mul_to_sparse A B. 
End MatrixLemmas.

Hint Resolve sparsify_correct densify_correct densify_correct_rev matrix_eq_commutes solveR_correct multi_assoc Densify_correct Densify_correct_rev dense_sparse_mul_correct sparse_dense_mul_correct dense_sparse_mul_to_sparse_correct eq_Mt_refl: matrices.

Infix "&*" := MVtimes (at level 40, left associativity) : matrix_scope.
Infix "&+" := Vplus (at level 50, left associativity) : matrix_scope.
Infix "&-" := Vminus (at level 50, left associativity) : matrix_scope.

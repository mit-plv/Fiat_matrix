Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.

Class MatrixElem :=
  { MEt :> Type;

    MEzero : MEt;
    MEone : MEt;

    MEopp : MEt -> MEt;
    MEplus : MEt -> MEt -> MEt;
    MEminus : MEt -> MEt -> MEt;
    MEtimes : MEt -> MEt -> MEt;

    MEring : ring_theory MEzero MEone MEplus MEtimes MEminus MEopp eq }.

Infix "*e" := MEtimes (at level 40, left associativity) : ME_scope.
Infix "+e" := MEplus (at level 50, left associativity) : ME_scope.
Infix "-e" := MEminus (at level 50, left associativity) : ME_scope.
Notation e0 := MEzero.
Notation e1 := MEone.

Open Scope ME_scope.
Delimit Scope ME_scope with ME.

Fixpoint fold_nat {A} (upto: nat) (reduce: A -> nat -> A) (zero: A) :=
  match upto with
  | O => zero
  | S upto' => reduce (fold_nat upto' reduce zero) upto'
  end.

Definition pointwise_upto {A} n (R: relation A) : relation (nat -> A) :=
  fun f g => forall a, a < n -> R (f a) (g a).

Lemma pointwise_upto_decr {A}:
  forall (upto : nat) (m1 m2 : nat -> A) R,
    pointwise_upto (S upto) R m1 m2 -> pointwise_upto upto R m1 m2.
Proof.
  unfold pointwise_upto; intuition.
Qed.

Instance pointwise_upto_reflexive {A} k R (reflA : @Reflexive A R) :
  Reflexive (pointwise_upto k R).
Proof. firstorder. Qed.

Instance pointwise_upto_symmetric {A} k R (symA : @Symmetric A R) :
  Symmetric (pointwise_upto k R).
Proof. firstorder. Qed.

Instance pointwise_upto_transitive {A} k R (transA : @Transitive A R) :
  Transitive (pointwise_upto k R).
Proof. firstorder. Qed.

Instance pointwise_upto_equivalence {A} k R (eqA : @Equivalence A R) :
  Equivalence (pointwise_upto k R).
Proof. split; apply _. Qed.

Instance pointwise_upto_Proper {A} k R (transA: @Transitive A R) (symA: @Symmetric A R) :
  Proper (pointwise_relation nat R ==> pointwise_relation nat R ==> Basics.flip Basics.impl)
         (pointwise_upto k R).
Proof.
  unfold Proper, respectful, pointwise_upto, pointwise_relation, Basics.flip, Basics.impl;
    eauto.
Qed.

Add Parametric Morphism A upto : (@fold_nat A upto)
  with signature (pointwise_relation _ (pointwise_relation _ eq) ==>
                  eq ==>
                  eq)
  as fold_nat_morphism.
Proof.
  intros r1 r2 pt_r zero.
  induction upto; intros; simpl;
    try rewrite pt_r, IHupto;
    unfold pointwise_relation in *;
    intuition auto using pointwise_upto_decr.
Qed.

Add Parametric Morphism A upto : (@fold_nat A upto)
  with signature (pointwise_relation _ (pointwise_upto upto eq) ==>
                  eq ==>
                  eq)
  as fold_nat_upto_morphism.
Proof.
  intros r1 r2 pt_r zero.
  induction upto; intros; simpl;
    try rewrite pt_r, IHupto;
    unfold pointwise_relation in *;
    intuition auto using pointwise_upto_decr.
Qed.

Notation sum k f := (fold_nat k (fun acc x => acc +e f x) e0).

Section MatrixElemOps.
  Context {ME: MatrixElem}.

  Add Ring MatrixElemOpsEtRing : MEring.

  Add Parametric Morphism k : (fun f => sum k f)
      with signature (pointwise_relation _ (@eq MEt) ==> @eq MEt)
        as sum_morphism.
  Proof.
    intros; apply fold_nat_morphism;
      unfold pointwise_relation in *;
      intuition auto using f_equal.
  Qed.

  Add Parametric Morphism k : (fun f => sum k f)
      with signature (pointwise_upto k (@eq MEt) ==> @eq MEt)
        as sum_upto_morphism.
  Proof.
    intros; apply fold_nat_upto_morphism;
      unfold pointwise_relation, pointwise_upto in *;
      intuition auto using f_equal.
  Qed.

  Lemma sum_distribute :
    forall n f1 f2,
      sum n (fun x => f1 x +e f2 x) = sum n f1 +e sum n f2.
  Proof.
    unfold sum; induction n; simpl; intros;
      try rewrite IHn; ring.
  Qed.

  Lemma sum_multiply_l :
    forall a n f,
      a *e sum n f = sum n (fun x => a *e f x).
  Proof.
    unfold sum; induction n; simpl; intros;
    try rewrite <- IHn; ring.
  Qed.

  Lemma sum_multiply_r :
    forall a n f,
      sum n f *e a = sum n (fun x => f x *e a).
  Proof.
    unfold sum; induction n; simpl; intros;
      try rewrite <- IHn; ring.
  Qed.

  Lemma sum_e0 :
    forall n, (sum n (fun k => e0)) = e0.
  Proof.
    unfold sum; induction n; simpl; intros; try rewrite IHn; ring.
  Qed.

  Notation "Σ{ x } f" :=
    (fold_nat _ (fun acc x => acc +e f) e0)
      (at level 0, format "Σ{ x }  f").

  Lemma sum_swap :
    forall m n f,
      sum n (fun k => sum m (fun k' => f k' k)) =
      sum m (fun k => sum n (fun k' => f k k')).
  Proof.
    induction m; simpl; intros.
    - rewrite (sum_e0 n); ring.
    - rewrite !sum_distribute.
      rewrite IHm.
      ring.
  Qed.
End MatrixElemOps.

Class Matrix {ME: MatrixElem} :=
  { (** [t m n A] is the type of m*n matrices with elements in A. *)
    Mt :> nat -> nat -> Type;

    Mget : forall {m n}, (Mt m n) -> nat -> nat -> MEt;
    Mtimes : forall {m n p}, (Mt m n) -> (Mt n p) -> (Mt m p);

    Mtimes_correct :
      forall {m n p} (m1: Mt m n) (m2: Mt n p),
      forall i j,
        i < m -> j < p ->
        Mget (Mtimes m1 m2) i j = sum n (fun k => (Mget m1 i k) *e (Mget m2 k j))
  }.

Infix "@*" := Mtimes (at level 40, left associativity) : matrix_scope.

Section MatrixOps.
  Context {ME : MatrixElem} {M : @Matrix ME}.

  Definition Meq {m n} (m1 m2: Mt m n) :=
    forall i j,
      i < m ->
      j < n ->
      Mget m1 i j = Mget m2 i j.
End MatrixOps.

Infix "@=" := Meq (at level 70) : matrix_scope.
Notation "m @[ i , j ]" := (Mget m i j) (at level 20, format "m @[ i ,  j ]") : matrix_scope.

Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

Section MatrixProps.
  Variable E: MatrixElem.
  Variable M: @Matrix E.

  Add Ring MatrixPropsEtRing : MEring.

  Theorem mult_assoc:
    forall {m n p q} (m1: Mt m n) (m2: Mt n p) (m3: Mt p q),
      (m1 @* m2) @* m3 @= m1 @* (m2 @* m3).
  Proof.
    red; intros.
    setoid_rewrite Mtimes_correct; try assumption.

    Ltac urgh :=
      symmetry; etransitivity; (* setoid_rewrite Mtimes_correct should do this *)
      [ apply sum_upto_morphism; red; intros;
        rewrite Mtimes_correct | ]; intuition reflexivity.

    replace (sum p (fun k : nat => (m1 @* m2)@[i, k] *e m3@[k, j])) with
            (sum p (fun k : nat => sum n (fun l : nat => m1@[i, l] *e m2@[l, k]) *e m3@[k, j]))
      by urgh.
    replace (sum n (fun k : nat => m1@[i, k] *e (m2 @* m3)@[k, j])) with
            (sum n (fun k : nat => m1@[i, k] *e sum p (fun l : nat => m2@[k, l] *e m3@[l, j])))
      by urgh.

    repeat setoid_rewrite sum_multiply_l.
    repeat setoid_rewrite sum_multiply_r.
    rewrite sum_swap.
    repeat (apply sum_morphism_Proper; red; intros).
    ring.
  Qed.
End MatrixProps.

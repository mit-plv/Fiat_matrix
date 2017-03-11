Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.

Module Type MatrixElem.
  Parameter t : Type.

  Parameter zero : t.
  Parameter one : t.

  Parameter opp : t -> t.
  Parameter plus : t -> t -> t.
  Parameter minus : t -> t -> t.
  Parameter times : t -> t -> t.

  Axiom ring : ring_theory zero one plus times minus opp eq.

  Module Import Notations.
    Infix "*e" := times (at level 30).
    Infix "+e" := plus (at level 60).
    Infix "-e" := minus (at level 60).
  End Notations.
End MatrixElem.

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

Module MatrixElemProperties (E: MatrixElem).
  Import E.Notations.

  Add Ring Et : E.ring.

  Definition sum k f := fold_nat k (fun acc x => acc +e f x) E.zero.

  Add Parametric Morphism k : (@sum k)
      with signature (pointwise_relation _ (@eq E.t) ==> @eq E.t)
        as sum_morphism.
  Proof.
    intros; apply fold_nat_morphism;
      unfold pointwise_relation in *;
      intuition auto using f_equal.
  Qed.

  Add Parametric Morphism k : (@sum k)
      with signature (pointwise_upto k (@eq E.t) ==> @eq E.t)
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
      ring_simplify; try rewrite IHn;
        ring.
  Qed.

  Lemma sum_multiply_r :
    forall a n f,
      sum n f *e a = sum n (fun x => f x *e a).
  Proof.
    unfold sum; induction n; simpl; intros;
      ring_simplify; try rewrite IHn;
        ring.
  Qed.

  Lemma sum_swap :
    forall m n f,
      sum n (fun k => sum m (fun k' => f k' k)) =
      sum m (fun k => sum n (fun k' => f k k')).
  Proof.
  Admitted.
End MatrixElemProperties.

Module Type Matrix (E: MatrixElem).
  Import E.Notations.
  Module EP := (MatrixElemProperties E).

  (** [t m n A] is the type of m*n matrices with elements in A. *)
  Parameter t: nat -> nat -> Type.

  Parameter get : forall {m n}, (t m n) -> nat -> nat -> E.t.
  Parameter times : forall {m n p}, (t m n) -> (t n p) -> (t m p).

  Definition eq {m n} (m1 m2: t m n) :=
    forall i j,
      i < m ->
      j < n ->
      get m1 i j = get m2 i j.

  Module Import Notations.
    Infix "@*" := times (at level 30) : matrix_scope.
    Infix "@=" := eq (at level 100) : matrix_scope.
    Notation "m @[ i , j ]" := (get m i j) (at level 20, format "m @[ i ,  j ]") : matrix_scope.
  End Notations.

  Open Scope matrix_scope.

  Axiom times_correct :
    forall {m n p} (m1: t m n) (m2: t n p),
    forall i j,
      i < m -> j < p ->
      (m1 @* m2)@[i, j] = EP.sum n (fun k => m1@[i, k] *e m2@[k, j]).
End Matrix.

Module MatrixProperties (E: MatrixElem) (M: Matrix E).
  Import E.Notations.
  Import M.Notations.

  Import M.EP.

  Open Scope matrix_scope.
  Theorem mult_assoc:
    forall {m n p q} (m1: M.t m n) (m2: M.t n p) (m3: M.t p q),
      (m1 @* m2) @* m3 @= m1 @* (m2 @* m3).
  Proof.
    red; intros.
    setoid_rewrite M.times_correct; try assumption.

    Ltac urgh :=
      symmetry; etransitivity; (* setoid_rewrite M.times_correct should do this *)
      [ apply sum_upto_morphism; red; intros;
        rewrite M.times_correct | ]; intuition reflexivity.

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
End MatrixProperties.

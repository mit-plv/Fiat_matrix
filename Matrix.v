Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Field_theory.
Require Import Field_tac.
Require Import PeanoNat.
Require Import Arith.
Require Import Omega.

Class MatrixElem :=
  { MEt :> Type;

    MEzero : MEt;
    MEone : MEt;

    MEopp : MEt -> MEt;
    MEplus : MEt -> MEt -> MEt;
    MEminus : MEt -> MEt -> MEt;
    MEtimes : MEt -> MEt -> MEt;
    MEdiv : MEt -> MEt -> MEt;
    MEinv: MEt -> MEt;
    
    MEfield :field_theory MEzero MEone MEplus MEtimes MEminus MEopp MEdiv MEinv eq }.

Infix "*e" := MEtimes (at level 40, left associativity) : ME_scope.
Infix "+e" := MEplus (at level 50, left associativity) : ME_scope.
Infix "-e" := MEminus (at level 50, left associativity) : ME_scope.
Infix "/e" := MEdiv (at level 50, left associativity) : ME_scope.

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
  unfold pointwise_upto. intuition.
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

  Add Field MatrixElemOpsEtField : MEfield.

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

  Lemma sum_eq :
    forall n f g, (forall i, i < n -> f i = g i) -> sum n f = sum n g.
  Proof.
    intros.
    unfold sum; induction n; simpl; intros;
      try rewrite <- IHn; try omega; auto.
    rewrite H; auto.
  Qed.
  
  Lemma sum_e0' :
    forall n f, (forall i, i < n -> f i = e0) -> (sum n (fun k => f k)) = e0.
  Proof.
    unfold sum; induction n; simpl; intros; try rewrite IHn; try ring.
    - rewrite H; try ring. omega.
    - intros; rewrite H; try reflexivity; omega. 
   Qed.

  Lemma sum_split :
    forall n f g h,
      (forall i, f i = g i +e h i) ->
      sum n f = sum n g +e sum n h. 
  Proof.
    induction n; simpl; intros;
      try rewrite <- IHn; try ring.
    rewrite H.
    rewrite IHn with (g := g) (h := h); auto.
    ring.
  Qed.
        
  Lemma sum_single :
    forall n f x y, x < n -> (forall i, i < n -> i <> x -> f(i) = e0) -> y = f x -> (sum n (fun k => f k)) = y.
  Proof.
    intros.
    unfold sum; induction n.
    - inversion H.
    - destruct (x =? n) eqn:H2.
      + apply Nat.eqb_eq in H2.
        rewrite H1.
        rewrite H2. 
        rewrite sum_e0'.
        * ring.
        * intros. rewrite H0; try reflexivity; omega.
      + apply beq_nat_false in H2.
        assert (x < n) by omega.
        apply IHn in H3. rewrite H3.
        rewrite H0 with (i := n); auto.
        ring.
        intros.
        apply H0; auto. 
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
        Mget (Mtimes m1 m2) i j = sum n (fun k => (Mget m1 i k) *e (Mget m2 k j));
    
    Mfill: forall {m n}, (nat -> nat -> MEt) -> (Mt m n);
    Mfill_correct :
      forall {m n} (f: nat -> nat -> MEt),
      forall i j,
        i < m -> j < n ->
        Mget (@Mfill m n f) i j = f i j;

    Melementwise_op: forall {m n}, (MEt -> MEt -> MEt) -> (Mt m n) -> (Mt m n) -> (Mt m n);
    Melementwise_op_correct:
      forall {m n} (m1: Mt m n) (m2: Mt m n) (op: MEt -> MEt -> MEt),
      forall i j,
        i < m -> j < n ->
        Mget (Melementwise_op op m1 m2) i j = op (Mget m1 i j) (Mget m2 i j)
  }.

Infix "@*" := Mtimes (at level 40, left associativity) : matrix_scope.
Infix "@+" := (Melementwise_op MEplus) (at level 50, left associativity) : matrix_scope.

Section MatrixOps.
  Context {ME : MatrixElem} {M1 M2: @Matrix ME}.
  
  Definition Meq {m n} (m1: @Mt _ M1 m n) (m2 : @Mt _ M2 m n) :=
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

  Add Field MatrixPropsEtField : MEfield.
  
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

Section MatrixProps'.
  Variable E: MatrixElem.
  Variable M1 M2 M3 M4 M12 M34 M23 M12_3 M1_23: @Matrix E.

  Add Field MatrixPropsEtField' : MEfield.

  Axiom normal_field_knowledge:
    forall r, r <> e0 -> MEinv r <> e0.
  Axiom non_trivial_ring:
    e0 <> e1.
  
  Definition Mtimes_correct' {M1 M2 M3: @Matrix E} {m n p: nat} 
    (Mtimes: (@Mt _ M1 m n) -> (@Mt _ M2 n p) -> (@Mt _ M3 m p)) := 
    forall (m1: @Mt _ M1 m n) (m2: @Mt _ M2 n p), 
    forall i j,
      i < m -> j < p ->
      Mget (Mtimes m1 m2) i j = sum n (fun k => (Mget m1 i k) *e (Mget m2 k j)).

  Theorem mult_assoc':
    forall {m n p q} (m1: Mt m n) (m2: Mt n p) (m3: Mt p q)
    (Mtimes12:  _ -> _ -> (@Mt _ M12 m p))
    (Mtimes23: _ -> _ -> (@Mt _ M23 n q))
    (Mtimes12_3: _ -> _ -> (@Mt _ M12_3 m q)) 
    (Mtimes1_23:  _ -> _ -> (@Mt _ M1_23 m q)), 
    Mtimes_correct' Mtimes12 -> 
    Mtimes_correct' Mtimes23 -> 
    Mtimes_correct' Mtimes1_23 -> 
    Mtimes_correct' Mtimes12_3 -> 
      Mtimes12_3 (Mtimes12 m1 m2) m3 @= Mtimes1_23 m1 (Mtimes23 m2 m3).
  Proof.
    red; intros.
    setoid_rewrite H1; try assumption.
    setoid_rewrite H2; try assumption.
    
    Ltac urgh H :=
      symmetry; etransitivity; (* setoid_rewrite Mtimes_correct should do this *)
      [ apply sum_upto_morphism; red; intros;
        rewrite H at 1| ]; intuition reflexivity.

    replace (sum p (fun k : nat => Mtimes12 m1 m2@[i, k] *e m3@[k, j])) with
            (sum p (fun k : nat => sum n (fun l : nat => m1@[i, l] *e m2@[l, k]) *e m3@[k, j]))
    by urgh H.

    replace (sum n (fun k : nat => m1@[i, k] *e Mtimes23 m2 m3@[k, j])) with
            (sum n (fun k : nat => m1@[i, k] *e sum p (fun l : nat => m2@[k, l] *e m3@[l, j])))
      by urgh H0.

    repeat setoid_rewrite sum_multiply_l.
    repeat setoid_rewrite sum_multiply_r.
    rewrite sum_swap.
    repeat (apply sum_morphism_Proper; red; intros).
    ring.
  Qed.
  
  Theorem plus_mult_dist:
  forall {m n p} (m1: Mt m n) (m2: Mt m n) (m3: Mt n p),
    (m1 @+ m2) @* m3 @= m1 @* m3 @+ m2 @* m3.
Proof.
  red; intros.
  repeat ((setoid_rewrite Mtimes_correct || setoid_rewrite Melementwise_op_correct); try assumption). 
  replace (sum n (fun k : nat => (m1 @+ m2)@[i, k] *e m3@[k, j]))
    with (sum n (fun k : nat => m1@[i, k] *e m3@[k, j] +e m2@[i, k] *e m3@[k, j])).
  - apply sum_distribute.
  - apply sum_upto_morphism. red. intros.
    repeat ((setoid_rewrite Mtimes_correct || setoid_rewrite Melementwise_op_correct); try assumption). ring.
 Qed. 
End MatrixProps'.


Ltac elim_bool:=
   repeat match goal with
  | [ |- context [Nat.eqb ?x ?y]] => let eq := fresh "eq" in destruct (x =? y) eqn: eq
  | [H: ?x =? ?y = false |- _] => apply Nat.eqb_neq in H
  | [H: ?x =? ?y = true |- _] => apply Nat.eqb_eq in H
  | [H: ?x <? ?y = true |- _] => apply Nat.ltb_lt in H
  | [H: ?x <? ?y = false |- _] => apply Nat.ltb_ge in H                                 | [H: ?x <=? ?y = true |- _] => apply Nat.leb_le in H
  | [H: ?x <=? ?y = false |- _] => apply Nat.leb_gt in H                                 end.

Ltac urgh :=
repeat (
    try
      ( let eq := fresh "eq" in 
        match goal with
        | [ |- context[?x =? ?y]] => destruct (x =? y) eqn: eq
        | [ |- context[?x <? ?y]] => destruct (x <? y) eqn: eq
        | [ |- context[?x <=? ?y]] => destruct (x <=? y) eqn: eq
        | [ |- context[Mfill _ ]] => rewrite Mfill_correct
        | [ |- context [Melementwise_op _ _ _]] => rewrite Melementwise_op_correct
        | [ |- context[let (_, _) := ?x in _]] => destruct x eqn: eq
        | [ |- context[match ?x with | _ => _ end]] => destruct (x) eqn: eq  
        | [H: context[let (_, _) := ?x in _] |- _] => destruct x eqn: eq
        | [H: context[?x =? ?y] |- _] => destruct (x =? y) eqn: eq
        | [H: context[?x <? ?y] |- _] => destruct (x <? y) eqn: eq
        | [H: context[?x <=? ?y] |- _] => destruct (x <=? y) eqn: eq
        | [H: context[match ?x with | _ => _ end] |- _] => destruct (x) eqn: eq
        | [H: Some _ = None |- _] => inversion H
        | [H: None = Some _|- _] => inversion H                                       
        | [H: true = false|- _] => inversion H
        | [H: false = true|- _] => inversion H 
        end); 
  try elim_bool;  
  auto;
  try omega).


Section MatrixInversion.
  Variable E: MatrixElem.
  Variable M: @Matrix E.
  Add Field MatrixInversionEtField' : MEfield.
  Variable n: nat.

    Set Implicit Arguments.
  Lemma eq_Mt_refl: forall m n, reflexive (Mt m n) (Meq).
  Proof.
    unfold reflexive. unfold "@=". 
    intros.
    reflexivity.
  Qed.
  
  Lemma eq_Mt_sym: forall m n, symmetric (Mt m n) (Meq).
  Proof.
    unfold symmetric. unfold "@=".
    intros.
    rewrite H; auto.
  Qed.
  
  Lemma eq_Mt_trans: forall m n, transitive (Mt m n) (Meq).
  Proof.
    unfold transitive. unfold "@=".
    intros.
    rewrite H; auto.
  Qed.
  
  Add Parametric Relation m n: (Mt m n) (Meq)
      reflexivity proved by (eq_Mt_refl (m:=m) (n:=n))
      symmetry proved by (eq_Mt_sym (m:=m) (n:=n))
      transitivity proved by (eq_Mt_trans (m:=m) (n:=n))                        
        as Meq_id.

  Add Parametric Morphism m n p: (Mtimes) with
      signature (Meq (m:=m)(n:=n)) ==> (Meq (m:=n)(n:=p)) ==> (Meq (m:=m)(n:=p)) as Mtimes_mor. 
  Proof.
    intros.
    unfold "@=".
    intros.
    rewrite Mtimes_correct; auto.
    rewrite Mtimes_correct; auto.
    apply sum_upto_morphism; red; intros.
    rewrite H; try assumption.
    rewrite H0; try assumption.
    reflexivity.
  Qed.
  
  Definition I := @Mfill E M n n (fun i j => (if beq_nat i j then MEone else MEzero)).
  Definition e (x y: nat) (c: MEt) := @Mfill E M n n (fun i j => (if ((beq_nat i x) && (beq_nat j y))%bool then c else MEzero)).
  Definition row_mul (x: nat) (c: MEt) := @Mfill E M n n (fun i j => (if beq_nat i j then (if beq_nat i x then c else MEone) else MEzero)).
  Definition row_add_to_row (x y: nat) (c: MEt) := I @+ (e x y c). 
  Definition swap (x y: nat) := I @+ (e x x (MEopp MEone)) @+ (e y y (MEopp MEone)) @+ (e x y MEone) @+ (e y x MEone). 
    
  Lemma I_is_identity:
    forall M: Mt n n, M @* I @= M /\ I @* M @= M.
  Proof.
    unfold I.
    intros.
    split.
    
    - unfold Meq.
      intros.
      rewrite Mtimes_correct; try assumption.
     
      rewrite sum_single with (x := j) (y := M0@[i, j]); auto. 
      + intros.
      rewrite Mfill_correct; try assumption.
      apply <- Nat.eqb_neq in H2.
      rewrite H2.
      ring.
      + assert (I@[j, j] = e1).
      {
        unfold I.
        rewrite Mfill_correct; try assumption.
        rewrite <- beq_nat_refl.
        reflexivity. 
      }
      rewrite Mfill_correct; try assumption.
      rewrite <- beq_nat_refl.
      ring. 

    -
      unfold Meq.
      intros.
      rewrite Mtimes_correct; try assumption.
      rewrite sum_single with (x := i) (y := M0@[i,j]); auto.
      + intros.
        rewrite Mfill_correct; auto.
        assert (i <> i0) by omega.
        apply <- Nat.eqb_neq in H3.
        rewrite H3.
        ring. 
      + rewrite Mfill_correct; auto.
        rewrite <- beq_nat_refl.
        ring.
      
  Qed.

  Lemma I_is_left_identity:
    forall M: Mt n n, I @* M @= M.
  Proof.
    apply I_is_identity.
  Qed.

  Lemma I_is_right_identity:
    forall M: Mt n n, M @* I @= M.
  Proof.
    apply I_is_identity.
  Qed.
  
  Definition invertible (M : Mt n n) :=
    exists M', M @* M' @= I /\ M' @* M @= I. 

  Lemma I_is_invertible:
    invertible I.
  Proof.
    exists I.
    split; apply I_is_identity.
  Qed.

  Lemma AB_BA:
    forall A B, invertible A -> A @* B @= I -> B @* A @= I. 
  Proof.
    intros.
    unfold invertible in H.
    inversion H.
    inversion H1.
    rename x into B'.
    assert (B' @* (A @* B) @= B' @* I).
    {
      setoid_rewrite H0.
      reflexivity.
    }

    rewrite <- mult_assoc in H4.
    rewrite H3 in H4.
    rewrite I_is_left_identity in H4.
    rewrite I_is_right_identity in H4.
    rewrite H4.
    assumption.
  Qed.

  Parameter is_eq_dec : forall x y: MEt, { eq x y } + { ~ eq x y }.

  Fixpoint GE_elemdown (A: Mt n n) (x: nat) (cur: nat) :=
    match cur with
    | O => (I, A)
    | S cur' =>
      let ee := row_add_to_row (n - cur) x (MEopp (Mget A (n - cur) x)) in
      let (E', EA') := GE_elemdown (ee @* A) x cur' in
      (E' @* ee, EA')
    end.

  Fixpoint get_first_none_zero (A: Mt n n) (i: nat) (y: nat) :=
    match i with
    | O => n
    | S i' =>
      if (is_eq_dec (Mget A (n - i) y) MEzero) then
        get_first_none_zero A i' y
      else
        n - i
    end.
  
        
  Fixpoint GE_stage1 (A: Mt n n) (i: nat) :=
    match i with
    | O => Some (I, A)
    | S i' =>
      let r := get_first_none_zero A i (n - i) in
      if (r =? n) then
        None
      else
        let A0 := (swap (n - i) r) @* A in 
        let ee := (row_mul (n - i) (MEinv (Mget A0 (n - i) (n - i)))) in
        let (E', EA') := GE_elemdown (ee @* A0) (n - i) (i - 1) in
        let ret := GE_stage1 EA' i' in
        match ret with
        | None => None
        | Some (E'', EA'') => Some (E'' @* E' @* ee @* swap (n - i) r, EA'')
        end
    end.
  
  Fixpoint GE_elemup (A: Mt n n) (x: nat) (i: nat) :=
    match i with
    | O => (I, A)
    | S i' =>
      let ee := row_add_to_row i' x (MEopp (Mget A i' x)) in
      let (E', EA') := GE_elemup (ee @* A) x i' in
      (E' @* ee, EA')
    end.
  
  Fixpoint GE_stage2 (A: Mt n n) (i: nat) :=
    match i with
    | O => (I, A)
    | S i' =>
        let (E', EA') := GE_elemup (A) i' i' in
        let (E'', EA'') := GE_stage2 EA' i' in
        (E'' @* E', EA'')
    end.

  Definition Inversion (A: Mt n n) := 
    match GE_stage1 A n with
    | None => None
    | Some (E, EA) => Some (fst (GE_stage2 EA n) @* E)
    end.
    
  Lemma get_element_e:
    forall x y c i j, forall A: Mt n n, 
        i < n -> j < n -> x < n -> y < n ->
        Mget ((e x y c) @* A) i j = if (i =? x) then c *e Mget A y j else e0. 
  Proof.
    intros.
    elim_bool.
    - intros.
      unfold e.
      rewrite Mtimes_correct; auto.
      apply sum_single with (x0 := y); auto.
      + intros.
        rewrite Mfill_correct; auto.
        elim_bool; auto; simpl; try ring.
        contradiction. 
      + rewrite Mfill_correct; auto.
        elim_bool; auto; simpl; try ring; try contradiction.
        tauto.
    - intros.
      unfold e.
      rewrite Mtimes_correct; auto.
      simpl.
      apply sum_e0'.
      intros.
      rewrite Mfill_correct; auto.
      elim_bool; auto; simpl; try ring; subst; try tauto.
  Qed.

  Lemma get_element_row_mul:
    forall x c i j, forall A: Mt n n, 
        i < n -> j < n -> x < n ->
        Mget ((row_mul x c) @* A) i j = if (i =? x) then c *e Mget A i j else Mget A i j. 
  Proof.
    intros; elim_bool; intros; unfold row_mul; rewrite Mtimes_correct; auto; simpl.
    - apply sum_single with (x0 := i); auto.
      + intros. rewrite Mfill_correct; auto.
        elim_bool; auto; simpl; subst; try ring; try tauto. 
        subst; tauto. 
      + rewrite Mfill_correct; auto.
        elim_bool; auto; simpl; try ring; subst; try tauto.
    - apply sum_single with (x0 := i); auto.
      + intros. rewrite Mfill_correct; auto.
        elim_bool; auto; simpl; try ring; subst; try tauto.
      + rewrite Mfill_correct; auto.
        elim_bool; auto; simpl; try ring; subst; try tauto.    
  Qed.

  Lemma get_element_row_add_to_row:
    forall x y c i j, forall A: Mt n n, 
        i < n -> j < n -> x < n -> y < n ->
        Mget ((row_add_to_row x y c) @* A) i j = (if i =? x then Mget A i j +e c *e Mget A y j else Mget A i j). 
  Proof.
    intros.
    elim_bool; intros; unfold row_add_to_row.
     -
      rewrite plus_mult_dist; auto.
      rewrite Melementwise_op_correct; auto.
      assert ((e x y c @* A)@[i, j] = c *e A@[y, j]) by (rewrite get_element_e; auto; elim_bool; auto; tauto). 
      rewrite H3.
      assert (I @* A @= A) by apply I_is_identity.
      rewrite H4; auto.
    - 
      rewrite plus_mult_dist; auto.
      rewrite Melementwise_op_correct; auto.
      assert ((e x y c @* A)@[i, j] = e0) by (rewrite get_element_e; auto; elim_bool; auto; tauto). 
      rewrite H3.
      assert (I @* A @= A) by apply I_is_identity.
      rewrite H4; auto.
      ring.   
  Qed.

  Lemma get_element_swap:
    forall x y i j, forall A: Mt n n, 
        i < n -> j < n -> x < n -> y < n ->
        Mget ((swap x y) @* A) i j = (if i =? x then Mget A y j else if i =? y then Mget A x j else Mget A i j). 
  Proof.
    intros.
    urgh; unfold swap; urgh; repeat (rewrite plus_mult_dist; urgh); repeat (rewrite get_element_e; urgh); try rewrite I_is_left_identity; repeat subst; urgh; field.
  Qed.

  Ltac urgh :=
repeat (
    try
      ( let eq := fresh "eq" in 
        match goal with
        | [ |- context[?x =? ?y]] => destruct (x =? y) eqn: eq
        | [ |- context[?x <? ?y]] => destruct (x <? y) eqn: eq
        | [ |- context[?x <=? ?y]] => destruct (x <=? y) eqn: eq
        | [ |- context[Mfill _ ]] => rewrite Mfill_correct
        | [ |- context [Melementwise_op _ _ _]] => rewrite Melementwise_op_correct
        | [ |- context[let (_, _) := ?x in _]] => destruct x eqn: eq
        | [ |- context[match ?x with | _ => _ end]] => destruct (x) eqn: eq  
        | [H: context[let (_, _) := ?x in _] |- _] => destruct x eqn: eq
        | [H: context[?x =? ?y] |- _] => destruct (x =? y) eqn: eq
        | [H: context[?x <? ?y] |- _] => destruct (x <? y) eqn: eq
        | [H: context[?x <=? ?y] |- _] => destruct (x <=? y) eqn: eq
        | [H: context[match ?x with | _ => _ end] |- _] => destruct (x) eqn: eq               | [H: Some _ = None |- _] => inversion H
        | [H: None = Some _|- _] => inversion H
        | [H: true = false|- _] => inversion H
        | [H: false = true|- _] => inversion H                                     
        | [ |- context[((e _ _ _) @* _)@[_, _]]] => rewrite get_element_e
        | [ |- context[((row_mul _ _) @* _)@[_, _]]] => rewrite get_element_row_mul
        | [ |- context[((row_add_to_row _ _ _) @* _)@[_, _]]] => rewrite get_element_row_add_to_row
        | [ |- context[((swap _ _) @* _)@[_, _]]] => rewrite get_element_swap                                                               
      end); 
  try elim_bool;  
  auto;
  try omega).
  
  Lemma GE_elemdown_correct_1 :
    forall A x cur,
      x < n -> cur < n - x ->
      (fst (GE_elemdown A x cur) @* A) @= snd (GE_elemdown A x cur).
  Proof.
    intros.
    generalize dependent A. 
    induction cur.
    - intros. simpl. apply I_is_identity.
    - assert (cur < n - x) by omega. intros.
      eapply IHcur in H1.
      simpl.
      destruct (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur) eqn: eq.
      simpl.
      rewrite eq in H1. simpl in H1.
      rewrite <- mult_assoc in H1.
      assumption.
  Qed.

  Lemma GE_elemdown_correct_keep :
    forall A x cur,
      x < n -> cur < n - x -> Mget A x x = e1 ->
      forall i j, i < n - cur -> j < n -> Mget (snd (GE_elemdown A x cur)) i j = Mget A i j.
  Proof.
    intros.
    generalize dependent A.
    generalize dependent i.
    generalize dependent j.
    induction cur.
    - intros.
      simpl.
      reflexivity.
    - intros.
      simpl.
      destruct (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur) eqn: eq.
      simpl.
      assert (snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)@[i, j] = (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A)@[i, j]).
      {
        apply IHcur; auto; try omega.
        rewrite get_element_row_add_to_row; auto; try omega. 
        elim_bool; auto.
        omega.
      }
      rewrite eq in H4. simpl in H4.
      rewrite H4.
      rewrite get_element_row_add_to_row; auto; try omega.
      elim_bool; auto.
      omega.
  Qed.
  
  Lemma GE_elemdown_correct_2 :
    forall A x cur,
      x < n -> cur < n - x -> Mget A x x = e1 ->
      forall y, y >= n - cur -> y < n -> Mget (snd (GE_elemdown A x cur)) y x = e0.
  Proof.
    intros.
    generalize dependent A.
    generalize dependent y.
    induction cur. 
    - intros.
      simpl. omega.
    - intros.
      destruct (beq_nat y (n - S cur)) eqn: eq; elim_bool.
      + simpl.
        destruct (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur) eqn: eq2. 
        simpl.
        assert (m0@[y, x] = (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A)@[y, x]).
        {
          assert (m0 = snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)) by (rewrite eq2; auto).
          rewrite H4. 
          apply GE_elemdown_correct_keep; auto; try omega.
          rewrite get_element_row_add_to_row; auto; try omega.
          elim_bool; auto. omega.
        }
        rewrite H4.
        rewrite get_element_row_add_to_row; auto; try omega.
        elim_bool; auto; try omega.
        rewrite <- eq0.
        rewrite H1.
        ring.
      + simpl.
        destruct (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur) eqn: eq2.
        simpl.
        assert (m0 = snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)) by (rewrite eq2; auto).
        rewrite H4.
        apply IHcur; auto; try omega.
        rewrite get_element_row_add_to_row; auto; try omega.
        elim_bool; auto. omega.
  Qed.

  Definition lower_left_zeros (A: Mt n n) (L: nat) :=
    forall i j,
      i < n -> j < n -> j < L -> i > j -> Mget A i j = e0.
  
  Lemma GE_elemdown_correct_keep_0:
    forall A x cur,
      x < n -> cur < n - x -> Mget A x x = e1 -> lower_left_zeros A x -> 
      lower_left_zeros (snd (GE_elemdown A x cur)) x.
  Proof.
    intros.
    generalize dependent A.
    induction cur.
    - intros.
      simpl.
      assumption.
    - intros.
      simpl.
      destruct (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A)  x cur) eqn: eq.
      simpl.
      unfold lower_left_zeros in *.
      intros.
      destruct (i <? (n - S cur)) eqn: eq2.
      + elim_bool.
        replace (m0) with (snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)) by (rewrite eq; auto).
        assert (e0 = (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A)@[i, j]).
        {
          rewrite get_element_row_add_to_row; auto; try omega.
          elim_bool; auto; try omega. 
          rewrite H2; auto.
        }
        rewrite H7. 
        apply GE_elemdown_correct_keep; auto; try omega.
        rewrite get_element_row_add_to_row; auto; try omega.
        elim_bool; auto; try omega.
      + destruct (i =? (n - S cur)) eqn: eq3; elim_bool; auto; try omega.
        * subst.
          replace (m0) with (snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)) by (rewrite eq; auto).
          assert (e0 = (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A)@[n - S cur, j]).
          {
            rewrite get_element_row_add_to_row; auto; try omega.
            elim_bool; auto; try omega.
            rewrite H2; auto.
            replace (A@[x, j]) with e0 by (rewrite H2; auto).
            ring.
          }
          rewrite H7.
          apply GE_elemdown_correct_keep; auto; try omega.
          rewrite get_element_row_add_to_row; auto; try omega.
          elim_bool; auto; try omega.
        * replace (m0) with (snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)) by (rewrite eq; auto).
          apply IHcur; auto; try omega.
          --- rewrite get_element_row_add_to_row; auto; try omega.
              elim_bool; auto; try omega.
          --- intros.
              rewrite get_element_row_add_to_row; auto; try omega.
              elim_bool; auto; try omega.
              rewrite H2; auto.
              replace (A@[x, j0]) with e0 by (rewrite H2; auto).
              ring. 
  Qed.
  
  Lemma GE_elemdown_correct_extend_0:
    forall A x,
      x < n -> Mget A x x = e1 -> lower_left_zeros A x -> 
      lower_left_zeros (snd (GE_elemdown A x (n - x - 1))) (x + 1).
  Proof.
    intros.
    unfold lower_left_zeros.
    intros.
    destruct (j =? x) eqn: eq; elim_bool.
    - rewrite eq. apply GE_elemdown_correct_2; auto; omega. 
    - apply GE_elemdown_correct_keep_0; auto; omega.
  Qed.

  Lemma  get_first_none_zero_at_least:
    forall A i j, get_first_none_zero A i j >= n - i.
  Proof.
    intros.
    induction i.
    - simpl. omega.
    - simpl.
      destruct (is_eq_dec (A@[n - S i, j]) e0); omega. 
  Qed.

  Lemma  get_first_none_zero_at_most:
    forall A i j, get_first_none_zero A i j <= n.
  Proof.
    intros.
    induction i.
    - simpl. omega.
    - simpl.
      destruct (is_eq_dec (A@[n - S i, j]) e0); omega. 
  Qed.

  Lemma  get_first_none_zero_correct:
    forall A i j, get_first_none_zero A i j < n -> A@[get_first_none_zero A i j, j] <> e0.
  Proof.
    intros.
    induction i.
    - simpl. simpl in H. omega.
    - simpl; urgh. 
      simpl in H.
      urgh.
  Qed.
  
  Lemma GE_stage1_correct_1:
    forall A i E EA,
      i <= n -> GE_stage1 A i = Some (E, EA) -> 
      E @* A @= EA.
  Proof.
    intros.
    generalize dependent A.
    generalize dependent E0.
    generalize dependent EA.
    induction i; intros.
    - simpl in H0. inversion H0; subst.
      apply I_is_left_identity.
    - unfold GE_stage1 in H0.
      fold GE_stage1  in H0.
      urgh.
      remember (swap (n - S i) (get_first_none_zero A (S i) (n - S i)) @* A) as A0.
        remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1. 
        inversion H0.
        replace ((if is_eq_dec (A@[n - S i, n - S i]) e0
     then get_first_none_zero A i (n - S i)
                  else n - S i)) with (get_first_none_zero A (S i) (n - S i)) by (auto).
        rewrite mult_assoc. 
        rewrite <- HeqA0. 
        assert (m  @* A1 @= m0).
        {
          replace m with (fst (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite eq; auto).
          replace m0 with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite eq; auto).
          apply GE_elemdown_correct_1; urgh.
        }
      destruct (GE_stage1 m0 i) eqn: eq3.
      * destruct p0.
        apply IHi in eq3; try omega. 
        
        rewrite mult_assoc.
        rewrite mult_assoc.
        rewrite <- HeqA1. 
        rewrite H1.
        rewrite <- H3.
        inversion eq1.
        rewrite <- H5.
        rewrite <- H6.
        assumption.
      * inversion eq1.
  Qed.

  Lemma GE_stage1_correct_keep :
    forall A i E EA,
      i <= n -> GE_stage1 A i = Some (E, EA) -> 
      forall x y, x < n - i -> y < n -> Mget EA x y = Mget A x y. 
  Proof.
    intros A i.
    generalize dependent A.
    induction i; intros.
    - simpl in H0.
      inversion H0; subst.
      reflexivity.
    - simpl in H0; urgh.
      +
        remember (swap (n - S i) (get_first_none_zero A i (n - S i)) @* A) as A0.
        remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *. 
        inversion H0. 
        rewrite <- H5. 
        rewrite IHi with (A := m0) (EA := m2) (E0 := m1); auto; try omega.
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (i - 0))) by (rewrite eq; auto).
        rewrite GE_elemdown_correct_keep; auto; try omega.
        *
          apply transitivity with (y0 := A0@[x, y]).
          --- rewrite HeqA1.
              rewrite get_element_row_mul; urgh.
          --- rewrite HeqA0.
              rewrite get_element_swap; urgh.
              assert (get_first_none_zero A i (n - S i) >= n - i) by apply get_first_none_zero_at_least.
              omega.
              assert (get_first_none_zero A i (n - S i) <= n) by apply get_first_none_zero_at_most.
              omega.
        * rewrite HeqA1.
          rewrite get_element_row_mul; urgh.
          field.
          rewrite HeqA0.
          rewrite get_element_swap; urgh.
          --- apply get_first_none_zero_correct; urgh. 
              assert (get_first_none_zero A i (n - S i) <= n) by apply get_first_none_zero_at_most.
              omega.
          --- assert (get_first_none_zero A i (n - S i) <= n) by apply get_first_none_zero_at_most.
              omega.
      + remember (swap (n - S i) (n - S i) @* A) as A0; remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *. 
        inversion H0. 
        rewrite <- H5. 
        rewrite IHi with (A := m0) (EA := m2) (E0 := m1); auto; try omega.
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (i - 0))) by (rewrite eq; auto).
        rewrite GE_elemdown_correct_keep; auto; try omega.
        *
          apply transitivity with (y0 := A0@[x, y]).
          --- rewrite HeqA1.
              rewrite get_element_row_mul; urgh.
          --- rewrite HeqA0.
              rewrite get_element_swap; urgh.
        * rewrite HeqA1.
          rewrite get_element_row_mul; urgh.
          field.
          rewrite HeqA0.
          rewrite get_element_swap; urgh.
  Qed.
  
  Definition Diag_ones (A: Mt n n) (L: nat) :=
    forall i,
      i < n -> i < L -> Mget A i i = e1.

  Lemma GE_stage1_extend_ones :
    forall A i E EA,
      i <= n -> Diag_ones A (n - i) -> GE_stage1 A i = Some (E, EA) -> 
      Diag_ones EA n.
  Proof.
    intros.
    generalize dependent A.
    generalize dependent E0.
    generalize dependent EA.
    induction i; intros; urgh. 
    - simpl in H1. inversion H1; subst.
      replace n with (n - 0) by omega.
      assumption.
    - unfold Diag_ones.
      intros.
      unfold GE_stage1 in H1; urgh. fold GE_stage1 in *.
      remember (swap (n - S i) (get_first_none_zero A (S i) (n - S i)) @* A) as A0.
      remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.

      assert (get_first_none_zero A (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
      assert (get_first_none_zero A (S i) (n - S i) >= n - S i) by apply get_first_none_zero_at_least.
      
      assert (Diag_ones m0 (n - i)).
      {
        unfold Diag_ones; intros.
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite eq; auto). 
        rewrite GE_elemdown_correct_keep; auto; try omega.
        + rewrite HeqA1.
          rewrite get_element_row_mul; elim_bool; auto; try omega.
          * rewrite eq3; field.
            rewrite HeqA0. rewrite get_element_swap; urgh.
            --- apply get_first_none_zero_correct.
                omega.
          * rewrite HeqA0.
            rewrite get_element_swap; urgh.
            apply H0; urgh.
        + rewrite HeqA1; urgh.
          field.
          rewrite HeqA0; urgh.
          apply get_first_none_zero_correct.
          omega. 
      }
      apply IHi in eq1; auto; try omega.
      inversion H1. 
      rewrite <- H9.
      apply eq1; auto.
  Qed.

  Lemma GE_stage1_extend_zeros :
    forall A i E EA,
      i <= n -> lower_left_zeros A (n - i) -> GE_stage1 A i = Some (E, EA) -> 
      lower_left_zeros EA n.
  Proof.
    intros A i.
    generalize dependent A.
    induction i; intros; urgh. 
    - replace n with (n - 0) by omega.
      simpl in H1.
      inversion H1.
      rewrite <- H4. 
      assumption.
    - unfold GE_stage1 in H1; urgh. fold GE_stage1 in *.
      remember (swap (n - S i) (get_first_none_zero A (S i) (n - S i)) @* A) as A0.
      remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.

      assert (get_first_none_zero A (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
      assert (get_first_none_zero A (S i) (n - S i) >= n - S i) by apply get_first_none_zero_at_least.
      
      assert (lower_left_zeros m0 (n - i)).
      {
        unfold lower_left_zeros.
        intros. 
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite eq; auto).
        replace (S i - 1) with (n - (n - S i) - 1) by omega. 
        apply GE_elemdown_correct_extend_0 with (x := n - S i); urgh.
        + rewrite HeqA1; urgh.
          field.
          rewrite HeqA0; urgh.
          apply get_first_none_zero_correct; urgh.
        + unfold lower_left_zeros; intros.
          rewrite HeqA1; urgh.
          rewrite HeqA0; urgh.
          * replace ( A@[get_first_none_zero A (S i) (n - S i), j0]) with e0 by (rewrite <- H0; auto; omega).
          ring. 
          * rewrite HeqA0; urgh.
            rewrite <- H0; auto; omega.
      }
      apply IHi with (A := m0) (E0 := m1); auto; try omega.
      inversion H1. 
      rewrite <- H7.
      assumption.
  Qed.

  Definition normalized_upper_triangle (A: Mt n n) := 
    Diag_ones A n /\ lower_left_zeros A n.
  
  Theorem GE_stage1_correct:
    forall A E EA,
      GE_stage1 A n = Some (E, EA) -> 
      E @* A @= EA /\ normalized_upper_triangle EA.
  Proof.
    intros.
    split.
    - eapply GE_stage1_correct_1; eauto.
    - unfold normalized_upper_triangle.
      split.
      + eapply GE_stage1_extend_ones; eauto.
        unfold Diag_ones. intros. omega.
      + eapply GE_stage1_extend_zeros; eauto.
        unfold lower_left_zeros; intros. omega.
  Qed.

  Lemma GE_elemup_correct_1 :
    forall A x i,
      x < n -> i <= x ->
      (fst (GE_elemup A x i) @* A) @= snd (GE_elemup A x i).
  Proof.
    intros.
    generalize dependent A. 
    induction i.
    - intros. simpl. apply I_is_identity.
    - assert (i <= x) by omega. intros.
      eapply IHi in H1.
      simpl.
      destruct (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i) eqn: eq.
      simpl.
      rewrite eq in H1. simpl in H1.
      rewrite <- mult_assoc in H1.
      assumption.
  Qed.

  Definition upper_right_zeros (A: Mt n n) (L: nat) :=
    forall i j,
      i < n -> j < n -> j >= n - L -> i < j -> Mget A i j = e0.

  Lemma nut_preserve:
    forall A x i',
      x < n -> i' < x -> normalized_upper_triangle A -> 
      normalized_upper_triangle ((row_add_to_row i' x (MEopp (Mget A i' x))) @* A).
  Proof.
    intros.
    unfold normalized_upper_triangle.
    inversion H1.
    unfold Diag_ones in H2. unfold lower_left_zeros in H3. 
    split.
    + unfold Diag_ones; intros.
      rewrite get_element_row_add_to_row; auto; try omega.
      elim_bool; auto; try omega.
      replace (A@[x, i]) with e0 by (rewrite H3; auto; omega).
      replace (A@[i, i]) with e1 by (rewrite H2; auto; omega).
      ring.
    + unfold lower_left_zeros; intros. 
      rewrite get_element_row_add_to_row; auto; try omega.
      elim_bool; auto; try omega.
      replace (A@[i, j]) with e0 by (rewrite H3; auto; omega).
      replace (A@[x, j]) with e0 by (rewrite H3; auto; omega).
      ring.
  Qed.
  
  Lemma GE_elemup_correct_2 :
    forall A x i,
      x < n -> i <= x -> normalized_upper_triangle A
           -> normalized_upper_triangle (snd (GE_elemup A x i)). 
  Proof.
    intros.
    generalize dependent A.
    generalize dependent x.
    
    induction i; intros.
    - simpl. assumption.
    - simpl.
      destruct (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i) eqn: eq.
      replace (snd (m @* row_add_to_row i x (MEopp (A@[i, x])), m0)) with (snd (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i)) by (rewrite eq; auto). 
      apply IHi; auto; try omega.
      apply nut_preserve; auto.
  Qed.

  Lemma GE_elemup_correct_keep :
    forall A x i,
      x < n -> i <= x -> normalized_upper_triangle A ->
      forall i' j, i' < n -> i' >= i -> j < n -> Mget (snd (GE_elemup A x i)) i' j = Mget A i' j.
  Proof.
    intros.
    generalize dependent A.
    generalize dependent i.
    generalize dependent j.
    generalize dependent i'.
    generalize dependent x. 
    induction i.
    - intros.
      simpl.
      reflexivity.
    - intros.
      simpl.
      destruct (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i) eqn: eq.
      simpl.
      assert (snd (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i)@[i', j] = (row_add_to_row i x (MEopp (A@[i, x])) @* A)@[i', j]).
      {
        apply IHi; auto; try omega.
        apply nut_preserve; auto; try omega.
      } 
      rewrite eq in H5. simpl in H5.
      rewrite H5.
      rewrite get_element_row_add_to_row; auto; try omega.
      elim_bool; auto.
      omega.
  Qed.
  
  Lemma GE_elemup_correct_3 :
    forall A x i,
      x < n -> i <= x -> normalized_upper_triangle A ->
      (forall i0, i0 < i -> (snd (GE_elemup A x i))@[i0, x] = e0).  
  Proof.
    intros.
    generalize dependent A.
    generalize dependent x.
    generalize dependent i.
    generalize dependent i0. 
    induction i; intros.
    - simpl. omega. 
    - simpl.
      inversion H1.
      unfold Diag_ones in H3.
      unfold lower_left_zeros in H4. 
      destruct (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i) eqn: eq.
      replace (snd (m @* row_add_to_row i x (MEopp (A@[i, x])), m0)) with (snd (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i)) by (rewrite eq; auto).
      destruct (i0 =? i) eqn: eq2; elim_bool; auto.
      + rewrite GE_elemup_correct_keep; auto; try omega.
        * rewrite get_element_row_add_to_row; auto; try omega.
          elim_bool; auto; try omega.
          replace (A@[x, x]) with e1 by (rewrite H3; auto; omega).
          rewrite eq0.
          ring.
        * apply nut_preserve; auto; try omega.
      + rewrite IHi; auto; try omega.
        apply nut_preserve; auto; try omega.
  Qed.

  Lemma GE_elemup_correct_4 :
    forall A x i L ,
      x < n -> i <= x -> L < n - x -> normalized_upper_triangle A -> upper_right_zeros A L ->  
      upper_right_zeros (snd (GE_elemup A x i)) L. 
  Proof.
    intros.
    generalize dependent A.
    generalize dependent x.
    generalize dependent L.
    induction i; intros; try assumption.
    simpl.
    destruct (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i) eqn: eq.
    replace (snd (m @* row_add_to_row i x (MEopp (A@[i, x])), m0)) with (snd (GE_elemup (row_add_to_row i x (MEopp (A@[i, x])) @* A) x i)) by (rewrite eq; auto).
    apply IHi; auto; try omega.
    - apply nut_preserve; auto; omega.
    - unfold upper_right_zeros.
      intros.
      rewrite get_element_row_add_to_row; auto; try omega.
      elim_bool; auto; try omega.
      rewrite eq0.
      replace (A@[i, j]) with e0 by (rewrite H3; auto; omega).
      replace (A@[x, j]) with e0 by (rewrite H3; auto; omega).
      ring.
  Qed.

  Lemma GE_elemup_correct_5:
    forall A x,
      x < n -> normalized_upper_triangle A -> upper_right_zeros A (n - x - 1) ->  
      upper_right_zeros (snd (GE_elemup A x x)) (n - x). 
  Proof.
    intros.
    unfold upper_right_zeros.
    intros.
    destruct (j =? x) eqn: eq; elim_bool; auto.
    - rewrite eq. apply GE_elemup_correct_3; auto; try omega.
    - rewrite GE_elemup_correct_4 with (L := n - x - 1);auto; try omega.
  Qed.

  Lemma GE_stage2_correct_1:
    forall A i,
      i <= n ->
      fst (GE_stage2 A i) @* A @= snd (GE_stage2 A i).
  Proof.
    intros.
    generalize dependent A.
    induction i.
    - intros; simpl.
      apply I_is_identity.
    - intros.
      simpl.
      destruct (GE_elemup A i i) eqn: eq1.
      destruct (GE_stage2 m0 i) eqn: eq2.
      simpl.
      rewrite mult_assoc.
      replace (m) with (fst (GE_elemup A i i)) by (rewrite eq1; auto). 
      rewrite GE_elemup_correct_1; auto; try omega.
      replace (m1) with (fst (GE_stage2 m0 i)) by (rewrite eq2; auto).
      replace (m2) with (snd (GE_stage2 m0 i)) by (rewrite eq2; auto).
      replace (m0) with (snd (GE_elemup A i i)) by (rewrite eq1; auto).      
      apply IHi; auto; try omega. 
  Qed.

  Lemma GE_stage2_correct_2:
    forall A i,
      i <= n -> normalized_upper_triangle A -> 
      normalized_upper_triangle (snd (GE_stage2 A i)).
  Proof.
    intros.
    generalize dependent A.
    induction i.
    - intros. simpl. assumption.
    - intros; simpl.
      destruct (GE_elemup A i i) eqn: eq1.
      destruct (GE_stage2 m0 i) eqn: eq2.
      simpl.
      replace (m2) with (snd (GE_stage2 m0 i)) by (rewrite eq2; auto).
      apply IHi; auto; try omega.
      replace (m0) with (snd (GE_elemup A i i)) by (rewrite eq1; auto).
      apply GE_elemup_correct_2; auto; try omega.
  Qed.

  Lemma GE_stage2_correct_3:
    forall A i,
      i <= n -> normalized_upper_triangle A -> upper_right_zeros A (n - i) -> 
      upper_right_zeros (snd (GE_stage2 A i)) n.
  Proof.
    intros.
    generalize dependent A.
    induction i.
    - intros; simpl. replace (n) with (n - 0) by omega. assumption.
    - intros; simpl.
      destruct (GE_elemup A i i) eqn: eq1.
      destruct (GE_stage2 m0 i) eqn: eq2.
      simpl.
      replace (m2) with (snd (GE_stage2 m0 i)) by (rewrite eq2; auto).
      apply IHi; auto; try omega.
      + replace (m0) with (snd (GE_elemup A i i)) by (rewrite eq1; auto).
        apply GE_elemup_correct_2; auto; try omega.
      + replace (m0) with (snd (GE_elemup A i i)) by (rewrite eq1; auto).
        apply GE_elemup_correct_5; auto; try omega.
        replace (n - i - 1) with (n - S i) by omega.
        assumption.
  Qed.

  Theorem GE_stage2_correct:
    forall A,
      normalized_upper_triangle A ->
      fst (GE_stage2 A n) @* A @= snd (GE_stage2 A n) /\ snd (GE_stage2 A n) @= I.
  Proof.
    intros.
    split.
    - apply GE_stage2_correct_1. auto.
    - unfold "@=".
      intros.
      destruct (j <=? i) eqn: eq; elim_bool; auto; try omega.
      + destruct (j =? i) eqn: eq2; elim_bool; auto; try omega.
        * subst.
          unfold I.
          rewrite Mfill_correct; elim_bool; auto; try omega.
          apply GE_stage2_correct_2; auto.
        * unfold I.
          rewrite Mfill_correct; elim_bool; auto; try omega.
          apply GE_stage2_correct_2; auto; omega.
      + unfold I.
        rewrite Mfill_correct; elim_bool; auto; try omega.
        apply GE_stage2_correct_3; auto; try omega.
        unfold upper_right_zeros; intros.
        omega.
  Qed.

  Theorem Inversion_correct:
    forall A E,
      Inversion A = Some E -> E @* A @= I.
  Proof.
    intros.
    unfold Inversion in H.
    destruct (GE_stage1 A n) eqn: eq; try inversion H.
    clear H1.
    destruct p.
    inversion H. clear H.
    assert (m @* A @= m0 /\ normalized_upper_triangle m0) by (apply GE_stage1_correct; assumption).
    inversion H. clear H.
    rewrite mult_assoc.
    rewrite H0.
    assert ((snd (GE_stage2 m0 n)) @= I) by (apply GE_stage2_correct; auto).
    rewrite <- H.
    apply GE_stage2_correct.
    assumption.
  Qed.

  Lemma invertible_closed:
    forall A B,
      invertible A -> invertible B -> invertible (A @* B).
  Proof.
    intros.
    unfold invertible in *.
    inversion H.
    inversion H0.
    exists (x0 @* x).
    split.
    - rewrite mult_assoc.
      assert (B @* (x0 @* x) @= ((B @* x0) @* x)) by (rewrite mult_assoc; reflexivity).
      rewrite H3.
      inversion H2.
      rewrite H4.
      rewrite I_is_left_identity.
      apply H1.
    - rewrite mult_assoc.
      assert ((x @* (A @* B)) @= ((x @* A) @* B)) by (rewrite mult_assoc; reflexivity).
      rewrite H3. 
      inversion H1.
      rewrite H5.
      rewrite I_is_left_identity.
      apply H2.
  Qed.

  Lemma row_mul_invertible:
    forall i x,
      i < n -> x <> MEzero -> invertible (row_mul i x).
  Proof.
    intros.
    unfold invertible.
    exists (row_mul i (MEinv x)).
    split.
    - unfold Meq.
      intros.
      rewrite get_element_row_mul; auto; try omega.
      destruct (i0 =? i) eqn: eq; elim_bool.
      + unfold row_mul. rewrite Mfill_correct; urgh.
        * unfold I; urgh.
          field. assumption.
        * unfold I; urgh.
          field.
      + unfold row_mul; urgh.
        * unfold I; urgh.
        * unfold I; urgh.
    - unfold Meq; intros.
      rewrite get_element_row_mul; urgh.
      + unfold row_mul; unfold I; urgh.
        * field. assumption.
        * field. assumption.
      + unfold row_mul; unfold I; urgh.
  Qed.

  Lemma row_add_to_row_invertible:
    forall x y c,
      x < n -> y < n -> x <> y -> invertible (row_add_to_row x y c).
  Proof.
    intros.
    unfold invertible.
    exists (row_add_to_row x y (MEopp c)).
    split; unfold Meq; intros; rewrite get_element_row_add_to_row; urgh; unfold row_add_to_row; unfold I; unfold e; urgh; simpl in *; try inversion eq7; try inversion eq8;  try inversion eq4; try field.
  Qed.

  Axiom swap_invertible:
    forall x y,
      x < n -> y < n -> invertible (swap x y).
  (*Proof.
    intros.
    unfold invertible.
    exists (swap x y).
    split; unfold Meq; intros; unfold I; unfold swap; urgh; simpl; rewrite Mtimes_correct; auto.
    - remember (if i =? x then y else if i =? y then x else i) as t.
      apply sum_single with (x0 := t); intros; try rewrite Heqt; unfold I; unfold e; urgh; simpl; try field; simpl in *; urgh.
    - apply sum_e0';intros; unfold I; unfold e; urgh; simpl; try field; simpl in *; urgh.
    - remember (if i =? x then y else if i =? y then x else i) as t.
      apply sum_single with (x0 := t); intros; try rewrite Heqt; unfold I; unfold e; urgh; simpl; try field; simpl in *; urgh.
    - apply sum_e0';intros; unfold I; unfold e; urgh; simpl; try field; simpl in *; urgh.
  Qed.*)
  
  Lemma GE_elemdown_preserve_invertibility:
    forall A x cur,
      x < n -> cur < n - x -> invertible A ->
      invertible (snd (GE_elemdown A x cur)). 
  Proof.
    intros.
    generalize dependent A.
    generalize dependent x.
    induction cur; intros. 
    - simpl. assumption.
    - simpl. 
      destruct (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur) eqn: eq.
      simpl.
      replace (m0) with (snd (GE_elemdown (row_add_to_row (n - S cur) x (MEopp (A@[n - S cur, x])) @* A) x cur)) by (rewrite eq; auto).
      apply IHcur; try omega.
      apply invertible_closed; try assumption.
      apply row_add_to_row_invertible; omega.
  Qed.
        
  Lemma kernal_span:
    forall F: (nat -> nat -> MEt), forall i: nat,
        (forall j k, j <= i -> k > j -> k < n -> F j k = e0) ->
        (forall j, j < i -> F j j = e1) ->
        F i i = e0 ->
        (exists c: nat -> MEt, forall k, k < n -> F i k = sum i (fun j => (c j) *e (F j k))).
  Proof.
    intros.
    generalize dependent F.
    induction i.
    - intros.
      exists (fun x => e0).
      intros.
      simpl.
      destruct (k =? 0) eqn: eq; urgh.
      + rewrite eq0. assumption.
      + apply H; omega.
    - intros.
      assert (exists c: nat -> MEt, forall k: nat, k < n -> (if i <? i then F i k else F (S i) k -e F i k *e F (S i) i) = sum i (fun j => (c j) *e (if j <? i then F j k else F (S i) k -e F i k *e F (S i) i))).
      {
        apply IHi with (F := (fun x y => if x <? i  then F x y else (F (S i) y) -e (F i y *e F (S i) i))).
        - intros.
          urgh.
          assert (i = j) by omega.
          rewrite <- H5 in H3. 
          destruct (k =? i) eqn: eq2; urgh.
          assert (F (S i) k = e0).
          {
            destruct (k =? S i) eqn: eq3; urgh.
            - rewrite eq1. apply H1.
            - rewrite H; try omega; reflexivity.
          }
          rewrite H6.
          rewrite H; try omega.
          ring.
        - intros.
          urgh.
        - urgh.
          rewrite H0; try omega. 
          ring.
      }
      inversion H2.
      remember (x) as c'. 
      clear H2 Heqc' x. 
      exists (fun x => if x =? i then F (S i) i else c' x). 
      intros.
      apply H3 in H2.
      urgh.
      rewrite sum_eq with (g := fun x => c' x *e F x k) in H2 .
      + rewrite sum_split with (g := fun x => (if x =? i then e0 else c' x) *e F x k) (h := fun x => (if x =? i then F (S i) i else e0) *e F x k).
        * assert (fold_nat (S i)
                           (fun (acc : MEt) (x : nat) => acc +e (if x =? i then e0 else c' x) *e F x k) e0 = F (S i) k -e F i k *e F (S i) i).
          {
            simpl.
            urgh.
            rewrite sum_eq with (g := fun x => c' x *e F x k).
            - rewrite <- H2.
              ring.
            - intros.
              urgh.
          }
          rewrite H4.
          rewrite sum_single with (x := i) (y := F (S i) i *e F i k); urgh; try ring.
          intros.
          urgh.
          ring.
        * intros.
          urgh; ring.
      + intros.
        urgh.
  Qed.
  
  Lemma get_first_none_zero_invertibility_lemma:
    forall A i,
      i <= n -> 0 < i -> invertible A -> Diag_ones A (n - i) -> lower_left_zeros A (n - i + 1) -> Mget A (n - i) (n - i) = e0 -> False.
  Proof.
    intros.
    inversion H1.
    inversion H5.
    remember x as B.
    clear H5 H6 HeqB x.
    assert ((exists c: nat -> MEt, forall k, k < n -> Mget A k (n - i) = sum (n - i) (fun j => (c j) *e (Mget A k j)))).
    {
      apply kernal_span with (F := fun i j => Mget A j i).
      - intros. unfold lower_left_zeros in H2.
        apply H3; try omega.
      - intros.
        apply H2; try omega.
      - assumption. 
    }
    inversion H5.
    remember (x) as c.
    clear H5 Heqc x.
    assert (forall j, j < n - i -> sum n (fun k => Mget B (n - i) k *e Mget A k j) = e0). 
    {
      intros.
      unfold Meq in H7.
      rewrite <- Mtimes_correct; try omega.
      rewrite H7; try omega.
      unfold I; urgh. 
    }
    assert (sum n (fun k => Mget B (n - i) k *e Mget A k (n - i)) = e1). 
    {
      intros.
      unfold Meq in H7.
      rewrite <- Mtimes_correct; try omega.
      rewrite H7; try omega.
      unfold I; urgh. 
    }
    assert (sum n (fun k => Mget B (n - i) k *e Mget A k (n - i)) = e0).
    {
      rewrite sum_eq with (g := fun x => sum (n - i) (fun (y : nat) => B@[n - i, x] *e (c y *e A@[x, y]))).
      - rewrite sum_swap with (n0 := n) (m := n - i).
        apply sum_e0'.
        intros.
        rewrite sum_eq with (g := fun x => c i0 *e (B@[n - i, x] *e A@[x, i0])).
        + rewrite <- sum_multiply_l.
          rewrite H5; auto.
          ring.
        + intros.
          ring.
      - intros.
        rewrite <- sum_multiply_l.
        rewrite <- H6; auto.
    }
    remember (sum n (fun k : nat => B@[n - i, k] *e A@[k, n - i])) as x. 
    rewrite H9 in H8.
    assert (e0 <> e1) by apply non_trivial_ring.
    rewrite H8 in H10.
    unfold not in H10.
    apply H10.
    reflexivity.
  Qed.

  Lemma get_first_none_zero_less_condition:
    forall A i j,
      i <= n -> (get_first_none_zero A i j = n -> (forall k, k >= n - i -> k < n -> Mget A k j = e0)).
  Proof.
    intros.
      generalize dependent k.
      induction i.
      + intros.
        omega.
      + intros.
        destruct (k =? n - S i) eqn: eq; urgh.
        * simpl in H0.
          urgh.
          rewrite eq0.
          assumption.
        * apply IHi; try omega.
          simpl in H0.
          urgh.
  Qed.

  Lemma get_first_none_zero_invertibility:
          forall A i,
            i <= n -> 0 < i -> invertible A -> Diag_ones A (n - i) -> lower_left_zeros A (n - i) -> get_first_none_zero A i (n - i) < n.
  Proof.
    intros.
    assert (get_first_none_zero A i (n - i) <= n) by (apply get_first_none_zero_at_most). 
    assert (get_first_none_zero A i (n - i) < n <-> get_first_none_zero A i (n - i) <> n) by (split; omega).
    apply H5.
    clear H4 H5.
    unfold not.
    intros.
    assert ((forall k, k >= n - i -> k < n -> Mget A k (n - i) = e0)) by (apply get_first_none_zero_less_condition; omega). 
    clear H4.
    apply get_first_none_zero_invertibility_lemma with (A := A) (i := i); urgh.
    - unfold lower_left_zeros.
      intros.
      destruct (j =? n - i) eqn: eq; urgh.
      + rewrite eq0. apply H5; omega.
      + apply H3; omega.
    - apply H5; omega.
  Qed.
  
  Lemma GE_stage1_preserve_invertibility:
    forall A i,
      i <= n -> lower_left_zeros A (n - i) -> invertible A -> Diag_ones A (n - i) ->
      GE_stage1 A i <> None. 
  Proof.
    intros.
    generalize dependent A.
    induction i.
    - intros.
      unfold not.
      intros.
      inversion H3.
    - intros.
      
      remember (swap (n - S i) (get_first_none_zero A (S i) (n - S i)) @* A) as A0; remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1.
      assert (get_first_none_zero A (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
        assert (get_first_none_zero A (S i) (n - S i) >= n - S i) by apply get_first_none_zero_at_least.
      assert (forall m m0, get_first_none_zero A (S i) (n - S i) <> n -> GE_elemdown A1 (n - S i) (S i - 1) = (m, m0) -> GE_stage1 m0 i <> None). 
      {
        intros.
        apply IHi; try omega.
        - try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.
            unfold lower_left_zeros.
            intros. 
            replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite H6; auto).
            replace (S i - 1) with (n - (n - S i) - 1) by omega. 
            apply GE_elemdown_correct_extend_0 with (x := n - S i); urgh.
            + rewrite HeqA1; urgh.
              field.
              rewrite HeqA0; urgh.
              apply get_first_none_zero_correct; urgh.
            + unfold lower_left_zeros; intros.
              rewrite HeqA1; urgh.
              rewrite HeqA0; urgh.
              * replace ( A@[get_first_none_zero A (S i) (n - S i), j0]) with e0 by (rewrite <- H0; auto; try omega).
                ring. 
              * rewrite HeqA0; urgh.
                rewrite <- H0; auto; omega.
        - replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite H6; auto).
          apply GE_elemdown_preserve_invertibility; urgh.
          rewrite HeqA1.
          apply invertible_closed.
          + apply row_mul_invertible; try omega.
            rewrite HeqA0; urgh. 
            * assert (get_first_none_zero A (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
              assert (A@[get_first_none_zero A (S i) (n - S i), n - S i] <> e0) by (apply get_first_none_zero_correct; omega).
              remember (A@[get_first_none_zero A (S i) (n - S i), n - S i]) as r.
              apply normal_field_knowledge.
  
              assumption.
          + rewrite HeqA0; urgh.
            apply invertible_closed; try assumption.
            apply swap_invertible; try omega. 
        - 
          unfold Diag_ones; intros.
          replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite H6; auto).
          rewrite GE_elemdown_correct_keep; auto; try omega.
          + rewrite HeqA1.
            rewrite get_element_row_mul; elim_bool; auto; try omega.
            * rewrite eq; field.
              rewrite HeqA0. rewrite get_element_swap; urgh.
              --- apply get_first_none_zero_correct.
                  omega.
            * rewrite HeqA0.
              rewrite get_element_swap; urgh.
              apply H2; urgh.
          + rewrite HeqA1; urgh.
            field.
            rewrite HeqA0; urgh.
            apply get_first_none_zero_correct.
            omega.
      }
      unfold GE_stage1; urgh; fold GE_stage1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *.
      
      + 
        assert (get_first_none_zero A (S i) (n - S i) < n) by (apply get_first_none_zero_invertibility; try assumption; omega).
        omega.
      + unfold not.
        intros.
        inversion H6.
      + rewrite <- eq1 at 1.
        fold GE_stage1. 
        apply H5 with (m:= m); assumption. 
  Qed.

  Definition default_get {A: Type} (d: A) (c: option A) :=
    match c with
    | None => d
    | Some c' => c'
    end.

  Theorem Inversion_very_correct:
    forall A,
      invertible A -> default_get I (Inversion A) @* A @= I.
  Proof.
    intros.
    assert (GE_stage1 A n <> None).
    {
      apply GE_stage1_preserve_invertibility; urgh.
      - unfold lower_left_zeros; intros; urgh.
      - unfold Diag_ones; intros; urgh.
    }
    unfold default_get.
    unfold Inversion.
    urgh.
    - apply Inversion_correct.
      unfold Inversion.
      urgh.
      subst.
      inversion eq0; subst.
      assumption.
    - unfold not in H0.
      assert (False) by auto.
      inversion H1.
  Qed.
        
End MatrixInversion. 
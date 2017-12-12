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
Require Import MyHelpers.

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
Infix "@-" := (Melementwise_op MEminus) (at level 50, left associativity) : matrix_scope.

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

Section SpecialMatrices.
  Variable n: nat.
  Variable E: MatrixElem.
  Variable M: @Matrix E.
  Add Field SpecialMatricesField : MEfield.

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
End SpecialMatrices.

Section Morphisms.
   Variable ME : MatrixElem.
  Add Field Afield' : MEfield.
  Notation DM := Mt.
  Variable M: @Matrix ME.
  (* Existing Instance DenseMatrix.*)
  
  (*Notation DM := (Mt (ME := ME) (Matrix := DenseMatrix)).*)
  
  Lemma eq_Mt_refl {m n}: reflexive (DM m n) (Meq).
  Proof.
    unfold reflexive. unfold "@=". 
    intros.
    reflexivity.
  Qed.
  
  Lemma eq_Mt_sym {m n}: symmetric (DM m n) (Meq).
  Proof.
    unfold symmetric. unfold "@=".
    intros.
    rewrite H; auto.
  Qed.
  
  Lemma eq_Mt_trans {m n}:  transitive (DM m n) (Meq).
  Proof.
    unfold transitive. unfold "@=".
    intros.
    rewrite H; auto.
  Qed.
  
  Global Add Parametric Relation m n: (DM m n) (Meq)
      reflexivity proved by (eq_Mt_refl (m:=m) (n:=n))
      symmetry proved by (eq_Mt_sym (m:=m) (n:=n))
      transitivity proved by (eq_Mt_trans (m:=m) (n:=n))                        
        as Meq_id.

  Global Add Parametric Morphism m n p: (Mtimes) with
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

   Global Add Parametric Morphism m n op: (Melementwise_op op) with
        signature (Meq (m:=m)(n:=n)) ==> (Meq (m:=m)(n:=n)) ==> (Meq (m:=m)(n:=n)) as Melementwise_mor. 
  Proof.
    intros.
    unfold "@=".
    intros.
    rewrite Melementwise_op_correct; auto.
    rewrite Melementwise_op_correct; auto.
    rewrite H; try assumption.
    rewrite H0; try assumption.
    reflexivity.
  Qed.
  
  Definition Restricted_Eq {m} {n} (f: nat -> nat -> MEt) (g: nat -> nat -> MEt) :=
    forall i j, i < m -> j < n -> f i j = g i j.
  
  Lemma eq_Res_refl {m n}: reflexive (nat -> nat -> MEt) (@Restricted_Eq m n).
  Proof.
    unfold reflexive. unfold Restricted_Eq. 
    intros.
    reflexivity.
  Qed.

  Lemma eq_Res_sym {m n}: symmetric (nat -> nat -> MEt) (@Restricted_Eq m n).
  Proof.
    unfold symmetric. unfold Restricted_Eq. 
    intros.
    rewrite H; auto.
  Qed.

  Lemma eq_Res_trans {m n}:  transitive (nat -> nat -> MEt) (@Restricted_Eq m n).
  Proof.
    unfold transitive. unfold Restricted_Eq. 
    intros.
    rewrite H; auto.
  Qed.

  Global Add Parametric Relation m n: (nat -> nat -> MEt) (@Restricted_Eq m n)
      reflexivity proved by (eq_Res_refl (m:=m) (n:=n))
      symmetry proved by (eq_Res_sym (m:=m) (n:=n))
      transitivity proved by (eq_Res_trans (m:=m) (n:=n))                        
        as Res_id.
  Print Mfill. 
  Global Add Parametric Morphism m n: (Mfill) with
        signature (@Restricted_Eq m n) ==> (Meq (m:=m)(n:=n)) as Mfill_mor.
  Proof.
    intros.
    unfold "@=".
    intros.
    rewrite Mfill_correct; auto.
    rewrite Mfill_correct; auto.
  Qed.
  
End Morphisms.  
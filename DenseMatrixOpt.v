Require Import
        Coq.Lists.List
        Coq.Strings.String
        Coq.Setoids.Setoid
        Coq.Arith.PeanoNat
        Coq.omega.Omega
        Coq.setoid_ring.Ring
        Coq.setoid_ring.Ring_theory
        Matrix
        DenseMatrix.

Section A.
  Variable ME : MatrixElem.
  Add Field Afield : MEfield.
  
  Variable M: Matrix.
  (*Notation DM := (Mt (ME := ME) (Matrix := DenseMatrix)).*)
  Notation DM := Mt. 
  
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
  
  Add Parametric Relation m n: (DM m n) (Meq)
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

   Add Parametric Morphism m n op: (Melementwise_op op) with
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

  Add Parametric Relation m n: (nat -> nat -> MEt) (@Restricted_Eq m n)
      reflexivity proved by (eq_Res_refl (m:=m) (n:=n))
      symmetry proved by (eq_Res_sym (m:=m) (n:=n))
      transitivity proved by (eq_Res_trans (m:=m) (n:=n))                        
        as Res_id.
  Print Mfill. 
  Add Parametric Morphism m n: (Mfill) with
        signature (@Restricted_Eq m n) ==> (Meq (m:=m)(n:=n)) as Mfill_mor.
  Proof.
    intros.
    unfold "@=".
    intros.
    rewrite Mfill_correct; auto.
    rewrite Mfill_correct; auto.
  Qed.

  Print DenseMatrix. 
  Lemma get_then_fill {m n}: forall M: DM m n,
      M @= Mfill (fun i j => M@[i, j]).
  Proof.
    intros.
    unfold "@=".
    intros.
    rewrite Mfill_correct; auto.
  Qed.

  Lemma op_then_get {m n}: forall A B : DM m n, forall op i j,
        i < m -> j < n -> 
      (Melementwise_op op A B)@[i, j] = op (A@[i, j]) (B@[i, j]). 
  Proof.
    intros.
    rewrite Melementwise_op_correct; auto.
  Qed.
  
  Lemma split_terms {m n}: forall A B: DM m n, forall op f,
        @Restricted_Eq m n (fun i j => f((Melementwise_op op A B)@[i, j])) ((fun i j => f(op (A@[i, j]) (B@[i, j])))).
  Proof.
    intros.
    unfold Restricted_Eq.
    intros.
    rewrite op_then_get; auto.
  Qed.
  Print Mfill.
  
  Lemma Mfill_and_matrix {m n}: forall A: DM m n, forall f op, 
      Melementwise_op op (Mfill f) A @= (Mfill (fun i j => op (f i j) (A@[i, j]))).
  Proof.
    intros.
    unfold "@=". 
    intros. 
    rewrite Mfill_correct; auto.
    rewrite Melementwise_op_correct; auto.
    rewrite Mfill_correct; auto.
  Qed.

  Lemma matrix_and_Mfill {m n}: forall A: DM m n, forall f op, 
      Melementwise_op op A (Mfill f) @= (Mfill (fun i j => op (A@[i, j]) (f i j))).
  Proof.
    intros.
    unfold "@=". 
    intros. 
    rewrite Mfill_correct; auto.
    rewrite Melementwise_op_correct; auto.
    rewrite Mfill_correct; auto.
  Qed.

  Lemma Mfill_and_Mfill: forall m n: nat, forall f g op, 
      Melementwise_op op (@Mfill ME M m n g) (Mfill f) @= (Mfill (fun i j => op (g i j) (f i j))).
  Proof.
    intros.
    unfold "@=". 
    intros. 
    rewrite Mfill_correct; auto.
    rewrite Melementwise_op_correct; auto.
    rewrite Mfill_correct; auto.
    rewrite Mfill_correct; auto.    
  Qed.

  Lemma M_and_M_and_M {m n}: forall A B C: DM m n, forall op1 op2,
        Melementwise_op op1 (Melementwise_op op2 A B) C @= Mfill (fun i j => op1 (op2 (A@[i, j]) (B@[i, j])) (C@[i, j])).
  Proof.
    intros.
    unfold "@="; intros.
    rewrite Melementwise_op_correct; auto.
    rewrite Melementwise_op_correct; auto.
    rewrite Mfill_correct; auto.
  Qed.

  Lemma M_and_M_and_M2 {m n}: forall A B C: DM m n, forall op1 op2,
        Melementwise_op op1 A (Melementwise_op op2 B C) @= Mfill (fun i j => op1 (A@[i, j]) (op2 (B@[i, j]) (C@[i, j]))).
  Proof.
    intros.
    unfold "@="; intros.
    rewrite Melementwise_op_correct; auto.
    rewrite Melementwise_op_correct; auto.
    rewrite Mfill_correct; auto.
  Qed.
  
  Infix "@-" := (Melementwise_op MEminus) (at level 50, left associativity) : matrix_scope.

  (*Definition is_variable {A} (_:A) := True. 
  Ltac check_if_var :=
    match goal with
    | [x:_ |- _] =>
      match goal with
      | [|- is_variable x] => try constructor
      end
    end.
  
  Lemma M_and_M_and_M' {m n}: forall A B C: DM m n, forall op1 op2,
        is_variable A -> is_variable B -> is_variable C -> Melementwise_op op1 (Melementwise_op op2 A B) C @= Mfill (fun i j => op1 (op2 (A@[i, j]) (B@[i, j])) (C@[i, j])).
  Proof.
    intros.
    apply M_and_M_and_M.
  Qed.

  Lemma M_and_M_and_M2' {m n}: forall A B C: DM m n, forall op1 op2,
        is_variable A -> is_variable B -> is_variable C -> Melementwise_op op1 A (Melementwise_op op2 B C) @= Mfill (fun i j => op1 (A@[i, j]) (op2 (B@[i, j]) (C@[i, j]))).
  Proof.
    intros.
    apply M_and_M_and_M2.
  Qed.
  
  Hint Rewrite @M_and_M_and_M' @M_and_M_and_M2' using check_if_var: MOPT.*)

  Ltac MOPT :=
    match goal with
    | [A: DM _ _, B: DM _ _, C : DM _ _ |- _] => rewrite (M_and_M_and_M A B C)
    | [A: DM _ _, B: DM _ _, C : DM _ _ |- _] => rewrite (M_and_M_and_M2 A B C)
    | [A: DM _ _ |- _] => rewrite (Mfill_and_matrix A)
    | [A: DM _ _ |- _] => rewrite (matrix_and_Mfill A)
    | _ => rewrite Mfill_and_Mfill
    end.
  
  Theorem test {n}: forall A B C D E F: DM n n,
     (A @+ B @+ C) @+ (D @+ E @+ F) @+ (A @+ A @+ B) @= A.
  Proof.
    intros.
    MOPT.
    MOPT.
    MOPT.
    MOPT. 
    Time repeat MOPT. 
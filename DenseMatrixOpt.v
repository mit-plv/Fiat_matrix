Require Import
        Coq.Lists.List
        Coq.Strings.String
        Coq.Setoids.Setoid
        Coq.Arith.PeanoNat
        Coq.omega.Omega
        Coq.setoid_ring.Ring
        Coq.setoid_ring.Ring_theory
        Matrix
        DenseMatrix
        MyHelpers.


Section A.
  Variable ME : MatrixElem.
  Add Field Afield : MEfield.
  Notation DM := (Mt (ME := ME) (Matrix := DenseMatrix)).
  Existing Instance DenseMatrix.
  
  Lemma get_then_fill {m n}: forall M: DM m n,
      M @= (Mfill (fun i j => M@[i, j]) : DM m n).
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
        @Restricted_Eq _ m n (fun i j => f((Melementwise_op op A B)@[i, j])) ((fun i j => f(op (A@[i, j]) (B@[i, j])))).
  Proof.
    intros.
    unfold Restricted_Eq.
    intros.
    rewrite op_then_get; auto.
  Qed.
  
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
      Melementwise_op op (@Mfill ME _ m n g) (Mfill f) @= (Mfill (fun i j => op (g i j) (f i j))).
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
    | [ |- context[Melementwise_op _ (Melementwise_op _ ?A ?B) ?C]] =>
      tryif (is_variable A; is_variable B; is_variable C) then rewrite (M_and_M_and_M A B C) else fail 0
    | [ |- context[Melementwise_op _ ?A (Melementwise_op _ ?B ?C)]] =>
      tryif (is_variable A; is_variable B; is_variable C) then rewrite (M_and_M_and_M2 A B C) else fail 0
    | [ |- context[Melementwise_op _ (Mfill _) ?A]] => tryif (is_variable A) then rewrite (Mfill_and_matrix A) else fail 0
    | [ |- context[Melementwise_op _ ?A (Mfill _)]] => tryif (is_variable A) then rewrite (matrix_and_Mfill A) else fail 0
    | _ => rewrite Mfill_and_Mfill
    end.
   
  Theorem test {n}: forall A B C D E F: DM n n,
     (A @+ B @+ C) @+ (D @+ E @+ F) @+ (A @+ A @+ B) @= A.
  Proof.
    intros.
    
    Print M_and_M_and_M .
    Locate "@+".
    repeat MOPT.
  Admitted.

End A.
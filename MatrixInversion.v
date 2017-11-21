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
Require Import Matrix.
Require Import MyHelpers.

Section MatrixInversionX.

  Variable E: MatrixElem.
  Variable M: @Matrix E.
  Add Field MatrixInversionEtField' : MEfield.

  
  Lemma eq_Mt_refl {m n}: reflexive (Mt m n) (Meq).
  Proof.
    unfold reflexive. unfold "@=". 
    intros.
    reflexivity.
  Qed.
  
  Lemma eq_Mt_sym {m n}: symmetric (Mt m n) (Meq).
  Proof.
    unfold symmetric. unfold "@=".
    intros.
    rewrite H; auto.
  Qed.
  
  Lemma eq_Mt_trans {m n}:  transitive (Mt m n) (Meq).
  Proof.
    unfold transitive. unfold "@=".
    intros.
    rewrite H; auto.
  Qed.

End MatrixInversionX.

Section MatrixInversion.
  Variable E: MatrixElem.
  Variable M: @Matrix E.
  Add Field MatrixInversionEtField'' : MEfield.
  Variable n: nat.

  Print eq_Mt_refl. 
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
  
  Lemma non_trivial_ring:
    e0 <> e1.
  Proof.
    Print field_theory.
    intro.
    symmetry in H.    
    apply MEfield.(F_1_neq_0).
    assumption.
  Qed.

  Lemma  normal_field_knowledge:
    forall r, r <> e0 -> MEinv r <> e0.
  Proof.
    intros.
    assert (MEinv r *e r = e1) by (field; assumption).
    unfold not; intros.
    rewrite H1 in H0.
    assert (e0 *e r = e0) by field.
    rewrite H2 in H0.
    assert (e0 <> e1) by (apply non_trivial_ring). 
    contradiction.
  Qed.

  
  Definition I := I n E M.
  Definition e := e n E M. 
  Definition row_mul := row_mul n E M.
  Definition row_add_to_row := row_add_to_row n E M.
  Definition swap := swap n E M.
  
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

  Hint Rewrite @Mfill_correct @Melementwise_op_correct @get_element_e  @get_element_row_mul @get_element_row_add_to_row @get_element_swap: MMM. 
  Ltac urgh := 
    repeat match goal with
    | _ => discriminate
    | _ => progress subst
    | _ => field
    | _ => progress auto
    | _ => omega
    | _ => progress autorewrite with MMM
    | [ |- context[let (_, _) := ?x in _]] => destruct x eqn: ?                                 
    | _ => progress elim_bool
                    
    | [ |- context[?x <? ?y]] => destruct (x <? y) eqn: ?
    | [ |- context[?x <=? ?y]] => destruct (x <=? y) eqn: ?
                                                            
    | [ |- context[match ?x with | _ => _ end]] => destruct (x) eqn: ?
                                                                       
    | [H: context[let (_, _) := ?x in _] |- _] => destruct x eqn: ?
                                                                    
    | [H: context[?x =? ?y] |- _] => destruct (x =? y) eqn: ?
                                                              
    | [H: context[?x <? ?y] |- _] => destruct (x <? y) eqn: ?
    | [H: context[?x <=? ?y] |- _] => destruct (x <=? y) eqn: ?
    | [H: context[match ?x with | _ => _ end] |- _] => destruct (x) eqn: ?                  
    end.
  
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
          replace m with (fst (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
          replace m0 with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
          apply GE_elemdown_correct_1; urgh.
        }
      destruct (GE_stage1 m0 i) eqn: eq3.
      * destruct p.
        apply IHi in eq3; try omega. 
        
        rewrite mult_assoc.
        rewrite mult_assoc.
        rewrite <- HeqA1. 
        rewrite H1.
        rewrite <- H3.
        inversion Heqo.
        rewrite <- H5.
        rewrite <- H6.
        assumption.
      * inversion Heqo.
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
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (i - 0))) by (rewrite Heqp; auto).
        rewrite GE_elemdown_correct_keep; auto; try omega.
        *
          apply transitivity with (y0 := A0@[x, y]).
          --- rewrite HeqA1.
              rewrite get_element_row_mul; urgh;
              assert (get_first_none_zero A i (n - S i) <= n) by apply  get_first_none_zero_at_most;
              omega. 
          --- rewrite HeqA0.
              rewrite get_element_swap; urgh.
              assert (get_first_none_zero A i (n - S i) >= n - i) by apply get_first_none_zero_at_least.
              omega.
              assert (get_first_none_zero A i (n - S i) <= n) by apply get_first_none_zero_at_most.
              omega.
        * rewrite HeqA1.
          rewrite get_element_row_mul; urgh.
          apply get_first_none_zero_correct.
          assert (get_first_none_zero A i (n - S i) <= n) by apply  get_first_none_zero_at_most;
            omega.

          assert (get_first_none_zero A i (n - S i) <= n) by apply  get_first_none_zero_at_most;
              omega. 
      + remember (swap (n - S i) (n - S i) @* A) as A0; remember (row_mul (n - S i) (MEinv (A0@[n - S i, n - S i])) @* A0) as A1; try rewrite <- HeqA0 in *; try rewrite <- HeqA1 in *. 
        inversion H0. 
        rewrite <- H5. 
        rewrite IHi with (A := m0) (EA := m2) (E0 := m1); auto; try omega.
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (i - 0))) by (rewrite Heqp; auto).
        rewrite GE_elemdown_correct_keep; auto; try omega.
        *
          apply transitivity with (y0 := A0@[x, y]).
          --- rewrite HeqA1.
              rewrite get_element_row_mul; urgh.
          --- rewrite HeqA0.
              rewrite get_element_swap; urgh.
        * rewrite HeqA1.
          rewrite get_element_row_mul; urgh.
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
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite Heqp; auto). 
        rewrite GE_elemdown_correct_keep; auto; try omega.
        + rewrite HeqA1.
          rewrite get_element_row_mul; elim_bool; auto; try omega.
          * rewrite eq; field. 
            rewrite HeqA0. rewrite get_element_swap; urgh.
            --- apply get_first_none_zero_correct.
                omega.
          * rewrite HeqA0.
            rewrite get_element_swap; urgh.
            apply H0; urgh.
        + rewrite HeqA1; urgh.
          apply get_first_none_zero_correct.
          omega. 
      }
      apply IHi with (E0:=m1) (EA:=m2) in H6 ; auto; try omega.
      inversion H1. 
      rewrite <- H9.
      apply H6; auto.
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
        replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite Heqp; auto).
        replace (S i - 1) with (n - (n - S i) - 1) by omega. 
        apply GE_elemdown_correct_extend_0 with (x := n - S i); urgh.
        + 
          apply get_first_none_zero_correct; urgh.
        + unfold lower_left_zeros; intros.
          rewrite get_element_row_mul; urgh.
          * replace ( A@[get_first_none_zero A (S i) (n - S i), j0]) with e0 by (rewrite <- H0; auto; omega).
            ring.
          * rewrite <- H0; auto; omega.
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
          unfold I. unfold Matrix.I. 
          rewrite Mfill_correct; elim_bool; auto; try omega.
          apply GE_stage2_correct_2; auto.
        * unfold I. unfold Matrix.I. 
          rewrite Mfill_correct; elim_bool; auto; try omega.
          apply GE_stage2_correct_2; auto; omega.
      + unfold I. unfold Matrix.I. 
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
      + unfold row_mul. unfold Matrix.row_mul. rewrite Mfill_correct; urgh.
        * unfold I; unfold Matrix.I; urgh.
        * unfold I; unfold Matrix.I; urgh.
      + unfold row_mul; unfold Matrix.row_mul; urgh.
        * unfold I; unfold Matrix.I; urgh.
        * unfold I; unfold Matrix.I; urgh.
    - unfold Meq; intros.
      rewrite get_element_row_mul; urgh.
      + unfold row_mul; unfold Matrix.row_mul; unfold I; unfold Matrix.I; urgh.
      + unfold row_mul; unfold Matrix.row_mul; unfold I; unfold Matrix.I; urgh.
  Qed.

  Lemma row_add_to_row_invertible:
    forall x y c,
      x < n -> y < n -> x <> y -> invertible (row_add_to_row x y c).
  Proof.
    intros.
    unfold invertible.
    exists (row_add_to_row x y (MEopp c)).
    split; unfold Meq; intros; rewrite get_element_row_add_to_row; urgh; unfold row_add_to_row; unfold Matrix.row_add_to_row; unfold I; unfold Matrix.I; unfold e; unfold Matrix.e; urgh; simpl in *; try inversion eq7; try inversion eq8;  try inversion eq4; try field.
  Qed.

  Lemma swap_invertible:
    forall x y,
      x < n -> y < n -> invertible (swap x y).
  Proof.
    intros.
    unfold invertible.
    exists (swap x y).
    split; unfold Meq; intros; unfold I; unfold Matrix.I; unfold swap; unfold Matrix.swap; urgh; simpl; rewrite Mtimes_correct; auto; urgh. 
    - remember (if j =? x then y else if j =? y then x else j) as t.
      apply sum_single with (x0 := t); intros; try rewrite Heqt; unfold I; unfold Matrix.I; unfold e; unfold Matrix.e; urgh. 
    - apply sum_e0';intros; unfold I; unfold Matrix.I; unfold e; unfold Matrix.e; urgh.
    - remember (if j =? x then y else if j =? y then x else j) as t.
      apply sum_single with (x0 := t); intros; try rewrite Heqt; unfold I; unfold Matrix.I; unfold e; unfold Matrix.e; urgh.
    - apply sum_e0';intros; unfold I; unfold Matrix.I; unfold e; unfold Matrix.e; urgh.
  Qed.
  
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
      apply H; omega.
    - intros.
      assert (exists c: nat -> MEt, forall k: nat, k < n -> (if i <? i then F i k else F (S i) k -e F i k *e F (S i) i) = sum i (fun j => (c j) *e (if j <? i then F j k else F (S i) k -e F i k *e F (S i) i))).
      {
        apply IHi with (F := (fun x y => if x <? i  then F x y else (F (S i) y) -e (F i y *e F (S i) i))).
        - intros.
          urgh.
          assert (i = j) by omega.
          rewrite <- H5 in H3. 
          destruct (k =? i) eqn: eq2; urgh.
          assert (F (S j) k = e0).
          {
            destruct (k =? S j) eqn: eq3; urgh.
            rewrite H; try omega; reflexivity.
          }
          rewrite H5.
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
        * intros.
          urgh.
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
      unfold I; unfold Matrix.I; urgh. 
    }
    assert (sum n (fun k => Mget B (n - i) k *e Mget A k (n - i)) = e1). 
    {
      intros.
      unfold Meq in H7.
      rewrite <- Mtimes_correct; try omega.
      rewrite H7; try omega.
      unfold I; unfold Matrix.I; urgh. 
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
          rewrite eq.
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
      + apply H5; omega.
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
            + apply get_first_none_zero_correct; urgh.
            + unfold lower_left_zeros; intros.
              urgh. 
              * replace ( A@[get_first_none_zero A (S i) (n - S i), j0]) with e0 by (rewrite <- H0; auto; try omega).
                ring. 
              *  rewrite <- H0; auto; omega.
        - replace (m0) with (snd (GE_elemdown A1 (n - S i) (S i - 1))) by (rewrite H6; auto).
          apply GE_elemdown_preserve_invertibility; urgh.
          apply invertible_closed.
          + apply row_mul_invertible; try omega.
            urgh. 
            * assert (get_first_none_zero A (S i) (n - S i) <= n) by apply get_first_none_zero_at_most.
              assert (A@[get_first_none_zero A (S i) (n - S i), n - S i] <> e0) by (apply get_first_none_zero_correct; omega).
              remember (A@[get_first_none_zero A (S i) (n - S i), n - S i]) as r.
              apply normal_field_knowledge.
  
              assumption.
          + apply invertible_closed; try assumption.
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
          + urgh. apply get_first_none_zero_correct.
            omega.
      }

      Ltac urgh2 :=
    repeat (try
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
      
                       
        
      unfold GE_stage1; urgh2; try rewrite HeqA1 in *; try rewrite HeqA0 in *. 
      + 
        assert (get_first_none_zero A (S i) (n - S i) < n) by (apply get_first_none_zero_invertibility; try assumption; omega).
        omega.
      +
        unfold not.
        intros.
        inversion H6.
      +
        rewrite <- eq1 at 1.
        fold GE_stage1 in *.
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
      inversion Heqo0; subst.
      assumption.
    - unfold not in H0.
      assert (False) by auto.
      inversion H1.
  Qed.
        
End MatrixInversion. 
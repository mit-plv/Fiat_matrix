Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import Matrix. 
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.
Require Import MyHelpers.
 
(** *Row major matrix, but for each row, we only store some non-zero elements. 
     in increased index order; efficient storage but not efficient multiplication *)


Section A.
 Variable ME : MatrixElem.
 Add Field Afield : MEfield.

Fixpoint get_v {ME: MatrixElem} (l: list (nat * MEt)) (k : nat) := 
  match l with
  | nil => MEzero
  | (a, b) :: l' => if (Nat.eqb k a) then b +e get_v l' k else get_v l' k
  end. 

Definition get {ME: MatrixElem} m n (M: list (list (nat * MEt))) (i j : nat) := 
if andb (i <? m) (j <? n) then
  get_v (nth_default nil M i) j
else
  MEzero.

Fixpoint generate_row  (f: nat -> nat -> MEt) (j n i: nat) :=
  match j with
  | 0 => nil
  | S j' =>
    if MEeqdec (f i (n - j)) (MEzero) then
      generate_row f  j' n i
    else
      (n - j, f i (n - j)):: generate_row f j' n i
  end.

Print map.

Fixpoint nat_list (i m: nat) :=
  match i with
  | 0 => nil
  | S i' => (m - i):: nat_list i' m
  end.

Definition Generate  (m n: nat) (f: nat -> nat -> MEt) :=
  map (generate_row f n n) (nat_list m m). 

Lemma nat_list_length: forall i m, length (nat_list i m) = i.
  Proof.
    intros.
    induction i; try eauto.
    simpl.
    rewrite IHi.
    reflexivity.
  Qed.

Lemma nat_list_element: forall i m j,
      j < i -> nth_default O (nat_list i m) j = m + j - i.
Proof.
    intros.
    generalize dependent j. 
    induction i; try eauto.
    - intros.
      inversion H.
    - intros.
      simpl.
      destruct j.
      + unfold nth_default.
        unfold nth_error.
        omega.
      + assert (j < i) by omega.
        apply IHi in H0.
        rewrite nth_default_S.
        rewrite H0.
        omega.
Qed.
  
Lemma generate_get_row_correct:
  forall m n f i j,
    i < m -> j < n -> get m n (Generate m n f) i j = get_v (generate_row f n n i) j.
Proof.
  intros.
  unfold Generate.
  unfold get.
  assert (i <? m = true) by (apply Nat.leb_le; omega).
  assert (j <? n = true) by (apply Nat.leb_le; omega).
  rewrite H1, H2.
  simpl.
  erewrite nth_default_map_in_range.
  - rewrite nat_list_element; auto.
    replace (m + i - m) with i by omega.
    reflexivity.
  - rewrite nat_list_length. assumption. 
Qed.

Lemma generate_row_get_element_correct_lemma: forall k n i j f, 
    j < n - k -> get_v (generate_row f k n i) j = e0.
Proof.
  intros.
  induction k.
  - simpl. reflexivity.
  - simpl.
    destruct (MEeqdec (f i (n - S k))).
    + apply IHk.  omega.
    + simpl.
      assert (j <> n - S k) by omega.
      apply Nat.eqb_neq in H0. rewrite H0.
      apply IHk.
      omega.
Qed. 

Lemma generate_row_get_element_correct:
  forall i j m n k f, 
    i < m -> n - k <= j -> j < n -> k <= n -> get_v (generate_row f k n i) j = f i j. 
Proof.
  intros.
  generalize dependent j.
  induction k; intros.
  - omega.
  - simpl in *.
    destruct (MEeqdec (f i (n - S k)) e0).
    + destruct (beq_nat (n - S k) j) eqn: eq.
      * apply beq_nat_true in eq.
       
        destruct (beq_nat (n - k) j) eqn: eq2.
        --- apply beq_nat_true in eq2.
            apply IHk; try omega.
        --- apply beq_nat_false in eq2.
            rewrite generate_row_get_element_correct_lemma; try omega.
            rewrite eq in e.
            rewrite e.
            reflexivity.
      * apply beq_nat_false in eq.
        rewrite IHk; try omega.
        reflexivity.
    + cbn.
      destruct (beq_nat j (n - S k)) eqn: eq.
      * apply beq_nat_true in eq.
        rewrite <- eq.
        rewrite generate_row_get_element_correct_lemma; try omega.
        ring.
      * apply beq_nat_false in eq.
        apply IHk; try omega.
Qed.

Fixpoint v_v_mul_le {ME: MatrixElem} (m n p i j k: nat) (v : list (nat * MEt)) (M2: list (list (nat * MEt))) :=
  match v with 
  | nil => MEzero
  | (t, a)::l' => if (t <? k) then (a *e get n p M2 t j) +e v_v_mul_le m n p i j k l' M2
                  else v_v_mul_le m n p i j k l' M2
  end. 

Fixpoint v_v_mul_eq {ME: MatrixElem} (m n p i j k: nat) (v : list (nat * MEt)) (M2: list (list (nat * MEt))) :=
  match v with 
  | nil => MEzero
  | (t, a)::l' => if (beq_nat t k) then (a *e get n p M2 t j) +e v_v_mul_eq m n p i j k l' M2
                  else v_v_mul_eq m n p i j k l' M2
  end. 

Fixpoint v_matrix_mul {ME: MatrixElem} (m n p i j: nat) (M1 M2: list (list (nat * MEt))) :=
  match j with 
  | 0 => nil
  | S j' => (j', v_v_mul_le m n p i j' n (nth_default nil M1 i) M2) :: v_matrix_mul m n p i j' M1 M2
  end. 

Fixpoint Matrix_mul {ME: MatrixElem} (m n p k: nat) (M1 M2: list (list (nat * MEt))):= 
  match k with 
  | 0 => @nil(list  (nat * MEt))
  | S k' => v_matrix_mul m n p (m - k) p M1 M2::Matrix_mul m n p k' M1 M2
  end. 


Lemma v_v_mul_induct: forall m n p i j k v M2, 
  v_v_mul_le m n p i j k v M2 +e v_v_mul_eq m n p i j k v M2 = v_v_mul_le m n p i j (S k) v M2. 
Proof. 
  intros. 
  induction v as [| (t, a) v' IHv]. 
  - cbn. ring. 
  - cbn. destruct (t <? k) eqn:eq.
    + apply Nat.leb_le in eq.
      assert (t =? k = false). { apply beq_nat_false_iff. omega. }
      assert (t <=? k = true). { apply Nat.leb_le.  omega. }
      assert (match k with
    | 0 => false
    | S m' => t <=? m'
    end = true). { destruct k. - omega. - apply Nat.leb_le. omega. }
      rewrite H. rewrite H0. rewrite H1. clear H H0 H1. 
      rewrite <- IHv. ring. 
    + apply leb_iff_conv in eq. destruct (t =? k) eqn:eq2.
      * apply beq_nat_true in eq2. 
        assert (t <=? k = true). { apply Nat.leb_le. omega. }
        assert (match k with
    | 0 => false
    | S m' => t <=? m'
    end = false). { destruct k. - reflexivity. - apply Nat.leb_nle. omega. }
        rewrite H. rewrite H0. rewrite <- IHv. ring. 
      * apply beq_nat_false in eq2.
         assert (t <=? k = false). { apply Nat.leb_nle. omega. }
         assert (match k with
    | 0 => false
    | S m' => t <=? m'
    end = false). { destruct k. - reflexivity. - apply Nat.leb_nle. omega. }
         rewrite H. rewrite H0. rewrite <- IHv. ring. 
Qed. 

Lemma v_v_mul_eq_out: forall m n p i j k M1 M2, 
  i < m -> k < n -> v_v_mul_eq m n p i j k (nth_default nil M1 i) M2 = get m n M1 i k *e get n p M2 k j. 
Proof. 
  intros. 
  unfold get at 1. assert (andb (i <? m) (k <? n) = true).
  { apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. }
  rewrite H1. clear H1. 
  remember ((nth_default nil M1 i)) as l. clear Heql. 
  induction l as [| (t, a) l IHl]. 
  - cbn. ring. 
  - cbn. destruct (t =? k) eqn :eq; rewrite Nat.eqb_sym in eq; rewrite eq. 
    + rewrite IHl. apply beq_nat_true in eq. subst. ring.
    + rewrite IHl. ring.
Qed. 


Lemma v_v_mul_equals_sum: forall m n p i j k M1 M2, 
  i < m -> k <= n -> v_v_mul_le m n p i j k (nth_default nil M1 i) M2 = sum k (fun k => (get m n M1 i k) *e (get n p M2 k j)).
Proof. 
  intros. 
  induction k as [| k IHk]. 
  - cbn. remember ((nth_default nil M1 i)) as l. clear Heql. 
    induction l as [| (t, a) l IHl]. 
    + cbn. reflexivity. 
    + cbn. apply IHl.
  - rewrite <- v_v_mul_induct. cbn. rewrite IHk.
    + rewrite v_v_mul_eq_out; try omega. ring. 
    + omega. 
Qed. 



Lemma Mtimes_row : forall m n p k M1 M2 i, 
  k <= m -> i < k -> nth_default nil (Matrix_mul m n p k M1 M2) i = v_matrix_mul m n p (m - k + i) p M1 M2. 
Proof. 
  simpl; intros.
  generalize dependent i. 
  induction k as [| k IHk]; intros. 
  - inversion H0. 
  - destruct i. 
    + cbn. rewrite Nat.add_0_r. reflexivity. 
    + cbn. rewrite nth_default_S. 
      assert (H3: m - S k + S i = m - k + i). 
      { omega. } rewrite H3. 
      assert (H4: k <= m). { omega. }
      apply IHk with (i :=i) in H4. 
      * rewrite H4. reflexivity.
      * omega. 
Qed. 

Lemma Mtimes_col_lemma : forall m n p i j k M1 M2, 
  k >= j -> get_v (v_matrix_mul m n p i j M1 M2) k = MEzero.
Proof. 
  intros. 
  generalize dependent k. 
  induction j as [|j IHj]; intros. 
  - cbn. reflexivity. 
  - cbn. assert (H1: k =? j = false). { apply Nat.eqb_neq. omega. }
    rewrite H1. 
    assert (H2 : k >= j). { omega. }
    apply IHj in H2. apply H2. 
Qed.



Lemma Mtimes_col : forall m n p i j k M1 M2, 
  i < m -> k < j -> get_v (v_matrix_mul m n p i j M1 M2) k = sum n (fun k0 => (get m n M1 i k0) *e (get n p M2 k0 k)).
Proof. 
  simpl; intros. 
  generalize dependent k.
  induction j as [| j IHj]; intros.
  - inversion H0. 
  - cbn. destruct (k=?j) eqn:eq.
    + apply beq_nat_true in eq. 
      assert (H1: k >= j). { omega. }
      rewrite Mtimes_col_lemma. 
      * rewrite eq. rewrite v_v_mul_equals_sum; try omega. ring. 
      * apply H1. 
    + apply beq_nat_false in eq. assert (H1: k < j). { omega. }
      apply IHj; try apply H1. 
Qed. 


End A. 


Definition SparseMatrix {ME: MatrixElem} : Matrix.
 unshelve eapply {| Mt m n := list (list (nat * MEt));
                    Mget m n mx i j := get m n mx i j; 
                    Mtimes m n p m1 m2 := Matrix_mul m n p m m1 m2;
                    Mfill m n f := Generate ME m n f;
                    Melementwise_op m n op m1 m2:= Generate ME m n (fun i j => op (get m n m1 i j) (get m n m2 i j))|}.
  simpl. intros. 
  unfold get at 1. 
  assert (H1: i <? m = true).
  { rewrite Nat.ltb_antisym. apply Bool.negb_true_iff. apply Nat.leb_gt. apply H. }
  assert (H2: j <? p = true).
  { rewrite Nat.ltb_antisym. apply Bool.negb_true_iff. apply Nat.leb_gt. apply H0. }
  rewrite H1. rewrite H2. simpl. 
  rewrite Mtimes_row; try omega. 
  assert (H3: (m - m + i) = i). { omega. }
  rewrite H3. 
  rewrite Mtimes_col; try omega.
  reflexivity.

  simpl.
  intros. 
  rewrite generate_get_row_correct; try assumption.
  rewrite generate_row_get_element_correct with (m := m); try omega.
  reflexivity.

  simpl. intros.
  rewrite generate_get_row_correct; try assumption.
  rewrite generate_row_get_element_correct with (m := m); try omega.
  reflexivity. 
Defined.

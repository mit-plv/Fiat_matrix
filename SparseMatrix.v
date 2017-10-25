Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import Matrix. 
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.



Lemma nth_default_0: forall A: Type, forall a b : A, forall l: list A, 
  nth_default b (a::l) 0 = a.
Proof. 
  intros a l. 
  reflexivity. 
Qed. 

Lemma nth_default_nil: forall A: Type, forall b : A, forall i, 
  nth_default b nil i = b.
Proof. 
  intros A0. intros b. intros i. 
  unfold nth_default. 
  unfold nth_error. 
  destruct i. 
  - reflexivity. 
  - reflexivity. 
Qed. 

Lemma nth_default_S: forall A: Type, forall a b : A, forall l: list A, forall i, 
  nth_default b (a :: l) (S i) = nth_default b l i.
Proof. 
  intros A0 a b l i. 
  unfold nth_default. 
  unfold nth_error. 
  reflexivity. 
Qed. 


Lemma nth_default_map : forall A B X d d0 i, forall f: A -> B, 
  f (d) = d0 -> nth_default d0 (map f X) i =  f (nth_default d X i). 
Proof. 
  intros A B X.  
  induction X as [| v X IHX]. 
  - intros d d0 i0 f H. simpl. rewrite nth_default_nil. rewrite nth_default_nil. rewrite H. reflexivity. 
  - intros d d0 i0 f H. destruct i0. 
    + rewrite nth_default_0. simpl. rewrite nth_default_0. reflexivity. 
    + rewrite nth_default_S. simpl. rewrite nth_default_S. apply IHX. 
      apply H.
Qed.  


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
                    Mtimes m n p m1 m2 := Matrix_mul m n p m m1 m2 |}.
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
Defined.

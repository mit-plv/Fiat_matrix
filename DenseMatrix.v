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


Section A.
 Variable ME : MatrixElem.
 Add Field Afield : MEfield.

Definition get_v {ME: MatrixElem} (l: list MEt) (k : nat) := 
  nth_default MEzero l k. 

Definition get {ME: MatrixElem} m n (M: list (list MEt)) (i j : nat) := 
if andb (i <? m) (j <? n) then
  get_v (nth_default nil M i) j
else
  MEzero.


Fixpoint v_matrix_mul {ME: MatrixElem} (m n p i j: nat) (M1 M2: list (list MEt)) :=
  match j with 
  | 0 => nil
  | S j' => sum n (fun k => (get m n M1 i k) *e (get n p M2 k (p - j))) :: v_matrix_mul m n p i j' M1 M2
  end. 

Fixpoint Matrix_mul {ME: MatrixElem} (m n p k: nat) (M1 M2: list (list MEt)):= 
  match k with 
  | 0 => @nil(list  MEt)
  | S k' => v_matrix_mul m n p (m - k) p M1 M2::Matrix_mul m n p k' M1 M2
  end. 

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

Lemma Mtimes_col : forall m n p i j k M1 M2, 
  j <= p -> k < j -> get_v (v_matrix_mul m n p i j M1 M2) k = sum n (fun k0 => (get m n M1 i k0) *e (get n p M2 k0 (p - j + k))).
Proof. 
  simpl; intros.  
  generalize dependent k.
  induction j as [| j IHj]; intros.
  - inversion H0.
  - destruct k. 
    + cbn. rewrite Nat.add_0_r. reflexivity. 
    + cbn. unfold get_v. rewrite nth_default_S. 
      assert (H1: p - S j + S k = p - j + k). { omega. }
      rewrite H1. assert (H2: j <= p). { omega. }
      assert (H3: k < j). { omega. }
      apply IHj; try assumption. 
Qed.
End A. 

Definition DenseMatrix {ME: MatrixElem} : Matrix.
 unshelve eapply {| Mt m n := list (list MEt);
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
  assert (H4: p - p + j = j). { omega. } rewrite H4. 
  reflexivity. 
Defined.

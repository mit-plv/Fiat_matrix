Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import matrix. 
Module SparseMatrix (ET : MatrixElem) : Matrix ET.
  
End SparseMatrix.

Axiom A: Type. 
Axiom A_plus : A -> A -> A. 
Axiom A_mul : A -> A -> A. 
Infix "+" := A_plus.
Infix "*" := A_mul.
Axiom A_plus_commu: forall a b : A, a + b = b + a. 
Axiom A_plus_assoc: forall a b c: A, (a + b) + c = a + (b + c).
Axiom A_dist: forall a b c: A, a * (b + c) = (a * b) + (a * c).
Axiom A_times_commu: forall a b : A, a * b = b * a. 
Axiom A_times_assoc: forall a b c: A, (a * b) * c = a * (b * c).

Axiom zero: A. 
Axiom A_plus_zero_r: forall a : A, a + zero = a. 
Axiom A_plus_zero_l: forall a : A, zero + a = a. 
Axiom A_times_zero_l: forall a : A, zero * a = zero. 
Axiom A_times_zero_r: forall a : A, a * zero = zero. 



Fixpoint summation (f : nat -> A) k := 
  match k with 
  | 0 => zero
  | S n => f (k) + summation f n
  end.

Lemma summation_equal_function_equal: forall (f f1: nat -> A), forall (k : nat), 
  (forall i: nat, f i = f1 i) -> summation f k = summation f1 k. 
Proof. 
  intros. 
  induction k as [| k IHk].
  - cbn. reflexivity. 
  - cbn. rewrite H. rewrite IHk. reflexivity. 
Qed. 

Lemma summation_scalar_r: forall (f: nat -> A), forall (k : nat), forall (c : A), 
  summation (fun x => (f x) * c) k = (summation f k) * c. 
Proof. 
  intros. 
  induction k as [| k IHk]. 
  - cbn. rewrite A_times_zero_l. reflexivity. 
  - cbn. rewrite IHk. symmetry. rewrite A_times_commu. rewrite A_dist. 
    rewrite (A_times_commu (c) (f(S k))). 
    rewrite (A_times_commu (c) (summation f k)).
    reflexivity.  
Qed. 

Lemma summation_scalar_l: forall (f: nat -> A), forall (k : nat), forall (c : A), 
  summation (fun x => c * (f x)) k = c * (summation f k). 
Proof. 
  intros. 
  induction k as [| k IHk]. 
  - cbn. rewrite A_times_zero_r. reflexivity. 
  - cbn. rewrite IHk. rewrite A_dist. 
    reflexivity.  
Qed. 


Lemma summation_taking_out: forall (f1 f2 : nat -> A), forall (k : nat), 
  summation (fun x => (f1 x) + f2(x)) k = (summation f1 k) + summation f2 k.
Proof. 
  intros. 
  induction k as [| k IHk]. 
  - simpl. rewrite A_plus_zero_r. reflexivity. 
  - cbn. rewrite IHk. rewrite A_plus_assoc. 
    assert (H: (f2 (S k) + (summation f1 k + summation f2 k)) = ((f2 (S k) + summation f1 k) + summation f2 k)).
    { rewrite <- A_plus_assoc. reflexivity. }
    rewrite H.
    symmetry. rewrite A_plus_assoc. 
    assert (H1: summation f1 k + (f2 (S k) + summation f2 k) = f2 (S k) + summation f1 k + summation f2 k).
    { rewrite <- A_plus_assoc. assert (H1: summation f1 k + f2 (S k) = f2 (S k) + summation f1 k). 
      { rewrite A_plus_commu. reflexivity. } 
      rewrite H1. reflexivity. }
    rewrite H1. reflexivity. 
Qed. 

Lemma summation_finite_order_swap: forall (n m : nat),
                                    forall (f: nat -> nat -> A), 
  summation (fun j => summation (fun i => f i j) n) m
  = summation (fun i => summation (fun j => f i j) m) n. 
Proof. 
  induction n as [| n IHn]. 
  - intros. cbn. 
    induction m as [| m IHm]. 
    + cbn. reflexivity. 
    + cbn. rewrite A_plus_zero_l. rewrite IHm. reflexivity. 
  - intros. 
    cbn. rewrite <- IHn. rewrite <- summation_taking_out. apply summation_equal_function_equal. 
    reflexivity. 
Qed. 







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

Record Matrix := 
{ 
  content: list (list (nat * A));
  col : nat; }.

Fixpoint get_v (l: list (nat * A)) (k : nat) := 
  match l with
  | nil => zero
  | (a, b) :: l' => if (Nat.eqb k a) then b + get_v l' k else get_v l' k
  end. 

Definition get (M : Matrix) (i j : nat) := 
if andb (j <=? (col M)) (1 <=? j) then
  get_v (nth_default nil (nil::M.(content)) i) j
else
  zero.

Definition n_row (M : Matrix) :=
  length M.(content).

Definition n_col (M : Matrix) := 
  M.(col). 

Fixpoint v_v_dot (M : Matrix) (n m: nat) (v : list (nat * A)) := 
  match n with
  | 0 => zero
  | S n' => (v_v_dot M n' m v) + (get_v v n) * (get M n m)
  end. 

Fixpoint v_matrix_mul (M : Matrix) (n m: nat) (v : list (nat * A)) := 
  match m with 
  | 0 => @nil(nat * A) 
  | S m' => (m, v_v_dot M n m v) :: v_matrix_mul M n m' v
  end. 

Definition Matrix_mul (M1 : Matrix) (M2 : Matrix) := 
  {| 
    content:= map (v_matrix_mul M2 M1.(col) M2.(col)) M1.(content);
    col:= M2.(col);|}.

Infix "**" := Matrix_mul (at level 40). 

Theorem Matrix_mul_invariant_row: forall M1 M2, 
  n_row (M1 ** M2) = n_row M1.
Proof. 
  intros. 
  unfold Matrix_mul. 
  unfold n_row. 
  cbn. rewrite map_length.
  reflexivity. 
Qed. 

Theorem Matrix_mul_invariant_col: forall M1 M2, 
  n_col (M1 ** M2) = n_col M2.
Proof. 
  intros. 
  unfold Matrix_mul. 
  unfold n_col. 
  cbn. reflexivity. 
Qed. 


Fixpoint ll (m : nat) := 
  match m with 
  | 0 => nil
  | S m' => (m, zero) :: ll m' 
  end. 

Lemma Matrix_mul_invariant_value_lemma0: forall l i j k, 
  get_v (nth_default nil l i) j = get_v (nth_default (ll k) l i) j.
Proof.  
  intros. 
  destruct (nth_error l i) eqn: eq. 
  - unfold nth_default. rewrite eq. reflexivity. 
  - unfold nth_default. rewrite eq. 
    induction k as [| k IHk]. 
    + cbn. reflexivity. 
    + cbn. destruct (j =? S k) eqn: eq2.
      * rewrite <- IHk. cbn. rewrite A_plus_zero_l. reflexivity. 
      * rewrite <- IHk. cbn. reflexivity. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma1: forall M n m,
  v_v_dot M n m nil = zero.
Proof. 
  intros. 
  induction n as [| n IHn]. 
  - cbn. reflexivity. 
  - cbn. rewrite IHn. rewrite A_times_zero_l. rewrite A_plus_zero_l. 
    reflexivity. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma2: forall M1 M2 i, 
  nth_default (ll (col M2)) (map (v_matrix_mul M2 (col M1) (col M2)) (content M1)) i
  = v_matrix_mul M2 (col M1) (col M2) (nth_default nil (content M1) i).
Proof. 
  intros. rewrite nth_default_map with (d := nil). 
  - reflexivity. 
  - unfold v_matrix_mul. 
    induction (col M2) as [| m IHm]. 
    + cbn. reflexivity. 
    + cbn. rewrite IHm. rewrite Matrix_mul_invariant_value_lemma1. reflexivity. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma3: forall M n v, 
  v_v_dot M n 0 v = zero.
Proof. 
  intros. 
  induction n as [| n IHn]. 
  - cbn. reflexivity. 
  - cbn. rewrite IHn. rewrite A_times_zero_r. rewrite A_plus_zero_l.
    reflexivity. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma4: forall M n v j, 
  j = 0 ->  get_v (v_matrix_mul M n M.(col) v) j = zero. 
Proof. 
  intros. 
  rewrite H. 
  induction (col M) as [| mm IHmm]. 
  - cbn. reflexivity. 
  - cbn. rewrite IHmm. reflexivity. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma5: forall M n v j, 
  (col M) < j -> v_v_dot M n j v = zero.
Proof. 
  intros. 
  induction n as [| n IHn]. 
  - cbn. reflexivity. 
  - cbn. rewrite IHn. unfold get at 1. 
    assert (H1: andb (j <=? col M)  (1 <=? j) = false).
    { rewrite Bool.andb_false_iff. left. 
      apply Nat.leb_gt. apply H. }
    rewrite H1. rewrite A_times_zero_r. 
    rewrite A_plus_zero_l. reflexivity. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma6: forall M n v j k, 
  k < j ->  get_v (v_matrix_mul M n k v) j = zero. 
Proof. 
  intros. assert (H' := H). 
  induction k as [| mm IHmm]. 
  - cbn. reflexivity. 
  - cbn. assert (H1 : j =? S mm = false). 
    { apply Nat.eqb_neq. apply Nat.lt_neq in H'.
      apply Nat.neq_sym. apply H'. }
    rewrite H1. rewrite IHmm. 
    + reflexivity. 
    + apply Lt.lt_le_S in H'. apply Le.le_Sn_le in H'. 
      apply Gt.le_S_gt in H'. apply H'.
    + apply Lt.lt_le_S in H'. apply Le.le_Sn_le in H'. 
      apply Gt.le_S_gt in H'. apply H'.
Qed. 

Lemma Matrix_mul_invariant_value_lemma7: forall M n v j, 
  andb (j <=? (col M)) (1 <=? j) = true -> 
    get_v (v_matrix_mul M n (col M) v) j = v_v_dot M n j v. 
Proof. 
  intros. 
  unfold v_matrix_mul. 
  generalize dependent j. 
  induction (col M) as [| mm IHmm]. 
  - intros. symmetry in H. apply Bool.andb_true_eq in H. 
    inversion H. symmetry in H0. apply Nat.leb_le in H0. inversion H0. 
    symmetry in H1. apply Nat.leb_le in H1. rewrite H2 in H1. inversion H1. 
  - intros. destruct (j =? S mm) eqn : eq2. 
    + apply Nat.eqb_eq in eq2. rewrite eq2. 
      cbn. assert (H1: (mm =? mm) = true). 
      { rewrite Nat.eqb_eq. reflexivity. }
      rewrite H1. rewrite Matrix_mul_invariant_value_lemma6. 
      * rewrite A_plus_zero_r. reflexivity. 
      * apply Gt.le_S_gt. reflexivity. 
    + cbn. rewrite eq2. apply IHmm. 
      apply Bool.andb_true_iff in H. inversion H. 
      rewrite Nat.leb_le in H0. 
      apply Bool.andb_true_iff. 
      split. 
      * apply Nat.eqb_neq in eq2. apply Nat.leb_le. 
        apply Gt.gt_S_le. unfold ge. 
        apply Nat.le_neq. 
        split. 
        --- apply H0. 
        --- apply eq2. 
      * apply H1. 
Qed. 

Lemma Matrix_mul_invariant_value_lemma8: forall M i k, 
  1 <= k /\ k <= col(M) -> get_v (nth_default nil (content M) i) k = get M (S i) k. 
Proof. 
  intros. 
  unfold get. 
  assert (H1: andb (k <=? col M)  (1 <=? k) = true). 
  { apply Bool.andb_true_iff. 
    split. 
    - apply Nat.leb_le. apply H. 
    - apply Nat.leb_le. apply H. 
  }
  rewrite H1. rewrite nth_default_S. 
  reflexivity. 
Qed. 

Theorem Matrix_mul_invariant_value: forall M1 M2 i j, 
  get (M1 ** M2) i j = summation (fun x => (get M1 i x) * (get M2 x j)) (n_col M1).
Proof. 
  intros. 
  unfold Matrix_mul. 
  unfold get at 1. 
  cbn. 
  destruct i. 
  - cbn. induction (n_col M1) as [| m IHm]. 
    + cbn. destruct ((andb (j <=? col M2) (match j with
                       | 0 => false
                       | S _ => true
                       end))).
      * reflexivity. * reflexivity. 
    + cbn. rewrite <- IHm. destruct ((andb (j <=? col M2) (match j with
                       | 0 => false
                       | S _ => true
                       end))).
      * rewrite A_plus_zero_r. unfold get at 1. 
        destruct (andb (S m <=? col M1) (1 <=? S m)). 
        --- cbn. rewrite A_times_zero_l. reflexivity. 
        --- rewrite A_times_zero_l. reflexivity. 
      * rewrite A_plus_zero_r. unfold get at 1. 
        destruct (andb (S m <=? col M1) (1 <=? S m)). 
        --- cbn. rewrite A_times_zero_l. reflexivity. 
        --- cbn. rewrite A_times_zero_l. reflexivity. 
  - rewrite nth_default_S. rewrite Matrix_mul_invariant_value_lemma0 with (k := (col M2)).
    rewrite Matrix_mul_invariant_value_lemma2.  
    destruct (((j <=? col M2) && match j with
                       | 0 => false
                       | S _ => true
                       end)%bool) eqn : eq. 
    + assert (eq' := eq). 
      apply Matrix_mul_invariant_value_lemma7 with (n := (col M1)) (v := (nth_default nil (content M1) i)) in eq.
      rewrite eq. unfold n_col.
      assert (H1: forall M1 M2 j i k, k <= (col M1) -> v_v_dot M2 k j (nth_default nil (content M1) i) =
      summation (fun x : nat => get M1 (S i) x * get M2 x j) k). 
      { intros. 
        induction k as [| k IHk]. 
        * cbn. reflexivity.
        * cbn. rewrite IHk.
          --- rewrite Matrix_mul_invariant_value_lemma8. 
              +++ rewrite A_plus_commu. reflexivity. 
              +++ split. 
                  *** omega. 
                  *** apply H. 
          --- omega. 
      }
      rewrite H1. 
      * reflexivity. 
      * reflexivity. 
    + assert (H: forall x, get M2 x j = zero). 
      {
        intros. unfold get. assert (H: andb (j <=? col M2) (1 <=? j) = false).
        { 
          apply Bool.andb_false_iff in eq. inversion eq. 
          * apply Bool.andb_false_iff. left. apply H. 
          * apply Bool.andb_false_iff. right. apply H. 
        }
        rewrite H. reflexivity. 
      }
      rewrite summation_equal_function_equal with (f1 := (fun x => zero)).
      * assert (H1 : forall x, summation (fun _ : nat => zero) x = zero). 
        {
          induction x as [| x IHx]. 
          --- cbn. reflexivity. 
          --- cbn. rewrite IHx. rewrite A_plus_zero_r. reflexivity. 
        }
        rewrite H1. reflexivity. 
      * intros. rewrite H. rewrite A_times_zero_r. reflexivity. 
Qed. 

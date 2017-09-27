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
 Add Ring Aring : MEring.


Definition get {ME: MatrixElem} (m n: nat) (M: list MEt) (i j : nat) :=
  nth_default MEzero M (i * n + j). 

Fixpoint Generate {ME: MatrixElem} (m n k: nat) (f: nat -> MEt) :=
  match k with 
  | 0 => @nil(MEt)
  | S k' => (f (m * n - k)) :: Generate m n k' f
  end.

Definition Matrix_mul {ME: MatrixElem} (m n p: nat) (M1 M2: list MEt):=
  Generate m p (m * p) (fun k => (sum n (fun i => get m n M1 (Nat.div k  p) i *e get n p M2 i (Nat.modulo k p)))).

Definition Matrix_elem_op {ME: MatrixElem} (op: MEt -> MEt -> MEt) (m n: nat) (M1 M2: list MEt):=
  Generate m n (m * n) (fun k => op (get m n M1 (Nat.div k n) (Nat.modulo k n)) (get m n M2 (Nat.div k n) (Nat.modulo k n))).
End A. 

Lemma Generate_index: forall {ME: MatrixElem} (m n l i: nat) (f: nat -> MEt),
   i < l -> 
    nth_default MEzero (Generate m n l f) i = f(m * n + i - l).
Proof.
  intros.
  generalize dependent i. induction l; intros.
  - inversion H.
  - cbn.
    destruct i.
    + rewrite nth_default_0.  auto.
    + rewrite nth_default_S.
      rewrite IHl; try omega.
      replace (m * n + i - l) with (m * n + (S i) - (S l)) by omega.
      reflexivity.
Qed. 

Corollary Generate_get: forall {ME: MatrixElem} (m n i j: nat) (f: nat -> MEt),
   i < m -> j < n -> 
   get m n (Generate m n (m * n) f) i j = f(i * n + j).
Proof.
  intros.
  unfold get.
  rewrite Generate_index.
  - rewrite minus_plus. reflexivity.
  - destruct m; try omega.
    destruct n; try omega.
    
    assert (i <= m) by omega.
    assert (j <= n) by omega.
    assert (i * S n <= m * S n) by (apply mult_le_compat_r; assumption).
    assert (i * S n + j <= m * S n + j) by (apply plus_le_compat_r; assumption).
    assert (m * S n + j <= m * S n + n) by (apply plus_le_compat_l; assumption).
    assert (m * S n + n < S m * S n).
    {
      simpl.
      rewrite <- mult_n_Sm.
      omega.
    }
    omega.
Qed.

Definition DenseMatrix {ME: MatrixElem} : Matrix.
 unshelve eapply {| Mt m n := list  MEt;
                    Mget m n mx i j := get m n mx i j; 
                    Mtimes m n p m1 m2 := Matrix_mul m n p m1 m2;
                    Melementwise_op m n op m1 m2:= Matrix_elem_op op m n m1 m2|}.
 - intros.  
   unfold Matrix_mul. 
   rewrite Generate_get; try assumption.
   replace ((i * p + j) / p) with (i).
   replace ((i * p + j) mod p) with (j).
   reflexivity.
   + rewrite plus_comm. rewrite Nat.mod_add; try omega.
     rewrite Nat.mod_small; auto.
   + apply Nat.div_unique with (a := (i * p + j)) (b := p) (r := j); auto.
     rewrite mult_comm. reflexivity.
 - intros.  
   unfold Matrix_elem_op. 
   rewrite Generate_get; try assumption.
   replace ((i * n + j) / n) with (i).
   replace ((i * n + j) mod n) with (j).
   reflexivity.
   + rewrite plus_comm. rewrite Nat.mod_add; try omega.
     rewrite Nat.mod_small; auto.
   + apply Nat.div_unique with (a := (i * n + j)) (b := n) (r := j); auto.
     rewrite mult_comm. reflexivity.
Defined.

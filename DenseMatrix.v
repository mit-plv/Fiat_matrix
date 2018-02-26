Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import Matrix. 
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.
Require Import MyHelpers. 

Definition DenseMatrix_t A := list A.

Section A.
 Context {ME : MatrixElem}.
 Add Field Afield : MEfield.

 Definition DenseMatrix_get (m n: nat) (M: DenseMatrix_t MEt) (i j : nat) :=
   nth_default MEzero M (i * n + j). 

 Fixpoint Generate (m n k: nat) (f: nat -> MEt) :=
   match k with 
   | 0 => @nil(MEt)
   | S k' => (f (m * n - k)) :: Generate m n k' f
   end.

 Definition DenseMatrix_mul (m n p: nat) (M1 M2: DenseMatrix_t MEt):=
   Generate m p (m * p) (fun k => (sum n (fun i => DenseMatrix_get m n M1 (Nat.div k  p) i *e DenseMatrix_get n p M2 i (Nat.modulo k p)))).

 Definition Matrix_elem_op (op: MEt -> MEt -> MEt) (m n: nat) (M1 M2: DenseMatrix_t MEt):=
   Generate m n (m * n) (fun k => op (DenseMatrix_get m n M1 (Nat.div k n) (Nat.modulo k n)) (DenseMatrix_get m n M2 (Nat.div k n) (Nat.modulo k n))).

 Lemma Generate_index: forall (m n l i: nat) (f: nat -> MEt),
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

 Corollary Generate_get: forall (m n i j: nat) (f: nat -> MEt),
     i < m -> j < n -> 
     DenseMatrix_get m n (Generate m n (m * n) f) i j = f(i * n + j).
 Proof.
   intros.
   unfold DenseMatrix_get.
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
End A. 

Definition DenseMatrix_fill {ME: MatrixElem} m n f := Generate m n (m * n) (fun x => f (x / n) (x mod n)).
Definition DenseMatrix_elementwise_op {ME: MatrixElem} m n op m1 m2 := Matrix_elem_op op m n m1 m2.

Definition DenseMatrix {ME: MatrixElem} : Matrix.
 unshelve eapply {| Mt m n := DenseMatrix_t MEt;
                    Mget := DenseMatrix_get;
                    Mtimes := DenseMatrix_mul;
                    Mfill := DenseMatrix_fill;
                    Melementwise_op := DenseMatrix_elementwise_op |};
   unfold DenseMatrix_fill, DenseMatrix_elementwise_op.
 - intros.  
   unfold DenseMatrix_mul. 
   rewrite Generate_get; try assumption.
   replace ((i * p + j) / p) with (i).
   replace ((i * p + j) mod p) with (j).
   reflexivity.
   + rewrite plus_comm. rewrite Nat.mod_add; try omega.
     rewrite Nat.mod_small; auto.
   + apply Nat.div_unique with (a := (i * p + j)) (b := p) (r := j); auto.
     rewrite mult_comm. reflexivity.
 - intros.
   simpl.
   rewrite Generate_get; auto.
   Print Nat.div_unique.
   rewrite <- Nat.div_unique with (b := n) (q := i) (r := j) (a := i * n + j); auto; try omega.
   Focus 2.
   rewrite Nat.mul_comm. reflexivity.

   rewrite Nat.add_comm. 
   rewrite Nat.mod_add; try omega.
   rewrite Nat.mod_small; try omega.
   reflexivity.

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

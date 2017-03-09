Require Import List.
Require Import Setoid.

Module Matrix. 
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


Axiom Matrix: Type. 
Axiom get : Matrix -> nat -> nat -> A. 
Axiom n_row: Matrix -> nat.
Axiom n_col: Matrix -> nat.
Axiom Matrix_plus: Matrix -> Matrix -> Matrix. 
Axiom Matrix_mul: Matrix -> Matrix -> Matrix. 
Infix "++" := Matrix_plus.
Infix "**" := Matrix_mul (at level 40). 


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
    rewrite (A_times_commu (c) (f(k - 0))). 
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

Axiom Matrix_mul_invariant_value: forall M1 M2 i j, 
  get (M1 ** M2) i j = summation (fun x => (get M1 i x) * (get M2 x j)) (n_col M1).


Axiom Matrix_mul_invariant_row: forall M1 M2, 
  n_row (M1 ** M2) = n_row M1. 

Axiom Matrix_mul_invariant_col: forall M1 M2, 
  n_col (M1 ** M2) = n_col M2. 


Definition eql (M1 M2: Matrix) := 
  (forall i j, get M1 i j = get M2 i j) /\ (n_row M1 = n_row M2) /\ (n_col M1 = n_col M2). 

Infix "==" := eql (at level 100). 

Lemma eql_reflexive : Reflexive (@eql). 
Proof. 
  unfold Reflexive. 
  intros. unfold eql. 
  split. 
  - reflexivity. 
  - split. 
    + reflexivity. 
    + reflexivity.  
Qed. 

Lemma eql_transitivity : Transitive (@eql).
Proof. 
  unfold Transitive. 
  intros. unfold eql. 
  inversion H.
  inversion H0.
  split. 
  - intros.  rewrite H1.  rewrite H3. 
    reflexivity. 
  - inversion H2. inversion H4. 
    split. 
    + rewrite H5. apply H7. 
    + rewrite H6. apply H8. 
Qed. 

Lemma eql_symmetry: Symmetric (@eql).
Proof. 
  unfold Symmetric. 
  intros. unfold eql. inversion H. inversion H1. 
  split. 
  - symmetry. apply H0. 
  - split. 
    + rewrite H2. reflexivity. 
    + rewrite H3. reflexivity.  
Qed. 

Add Parametric Relation : (Matrix) (@eql)
 reflexivity proved by eql_reflexive
 symmetry proved by eql_symmetry
 transitivity proved by eql_transitivity
 as eql_rel.

Add Parametric Morphism: (Matrix_mul)
   with signature (@eql ==> @eql ==> @eql)
     as plus_morphism.
Proof. 
  intros. 
  unfold eql. inversion H0. inversion H2. inversion H. inversion H6. 
  split. 
  - intros. 
    rewrite Matrix_mul_invariant_value.
    rewrite Matrix_mul_invariant_value.
    rewrite H8. 
    apply summation_equal_function_equal. 
    intros. 
    rewrite H1. 
    rewrite H5. 
    reflexivity. 
  - split. 
    + rewrite Matrix_mul_invariant_row. 
      rewrite Matrix_mul_invariant_row. 
      rewrite H7. reflexivity. 
    + rewrite Matrix_mul_invariant_col. 
      rewrite Matrix_mul_invariant_col.
      rewrite H4. reflexivity. 
Qed. 

Theorem Matrix_mul_assoc: forall M1 M2 M3,
  (M1 ** M2) ** M3 == M1 ** (M2 ** M3). 
Proof. 
  intros. 
  unfold eql.
  split. 
  - intros. rewrite Matrix_mul_invariant_value. 
    rewrite Matrix_mul_invariant_col. 
    rewrite Matrix_mul_invariant_value. 
    assert (H1: summation (fun x : nat => get (M1 ** M2) i x * get M3 x j) (n_col M2)
    = summation (fun x : nat => (summation (fun y => (get M1 i y * get M2 y x) * get M3 x j) (n_col M1))) (n_col M2)).
    {
      apply summation_equal_function_equal. intros. 
      rewrite Matrix_mul_invariant_value. 
      rewrite summation_scalar_r. reflexivity. 
    }
    rewrite H1. rewrite summation_finite_order_swap. 
    apply summation_equal_function_equal. 
    intros. rewrite Matrix_mul_invariant_value. rewrite <- summation_scalar_l. 
    apply summation_equal_function_equal. intros. 
    rewrite A_times_assoc. reflexivity. 
  - split. 
    + rewrite Matrix_mul_invariant_row. 
      rewrite Matrix_mul_invariant_row. 
      rewrite Matrix_mul_invariant_row. 
      reflexivity. 
    + rewrite Matrix_mul_invariant_col.
      rewrite Matrix_mul_invariant_col.
      rewrite Matrix_mul_invariant_col. 
      reflexivity. 
Qed. 

End Matrix. 
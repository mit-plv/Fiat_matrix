Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import Matrix. 
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.

Section A. 
Variable E: MatrixElem.
Variable M: @Matrix E.

Record YC_data {n: nat} := {
  X: Mt n n;
  Y: Mt n n;
}. 

Axiom transpose : forall {n}, Mt n n -> Mt n n. 
Axiom Mplus : forall {n}, Mt n n -> Mt n n -> Mt n n. 
Infix "@+" := Mplus (at level 50, left associativity) : matrix_scope.

Definition update n (f: YC_data) (A: Mt n n) := 
  let X' := A @* f.(X) @+ f.(Y) in
  let Z' := X' @* X' in
  let Y' := f.(Y) @* (transpose Z') in
  {| X := X'; Y := Y'|}. 

Print sigT. 
Print ex. 
Theorem Optimizer: forall n f A, {f': _ & f' = update n f A}. 
Proof. 
  intros. 
  destruct f.   
  econstructor. 
  cbv delta [update]. 
  cbv beta.
  cbv beta delta [X].
  
Defined. 

Variable n: nat.
Variable f: @YC_data n. 
Compute projT1 (Optimizer n f). 
Print projT1. 

Search beq_nat. 
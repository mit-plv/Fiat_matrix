Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import Matrix. 
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.
Require Import SparseMatrix.
Require Import DenseMatrix.

Section A. 
Variable E: MatrixElem.
Definition M:= (@DenseMatrix E).
(* Definition M':= (@SparseMatrix E). *)
(* Axiom transposeM: forall {n}, @Mt _  M n n -> @Mt _ M n n. *)
(* Axiom transposeM': forall {n}, @Mt _  M' n n -> @Mt _ M' n n. *)

Existing Instance M.

Axiom transpose : forall {n}, Mt n n -> Mt n n. 
Axiom Mplus : forall {n}, Mt n n -> Mt n n -> Mt n n. 
Infix "@+" := Mplus (at level 50, left associativity) : matrix_scope.
Axiom Mminus : forall {n}, Mt n n -> Mt n n -> Mt n n. 
Infix "@-" := Mminus (at level 50, left associativity) : matrix_scope.
Axiom Vt: nat -> Type. 
Axiom MVtimes : forall {n m}, Mt m n -> Vt n -> Vt m.
Axiom inversion : forall {n}, Mt n n -> Mt n n. 
Infix "&*" := MVtimes (at level 40, left associativity) : matrix_scope.
Axiom Vplus : forall {n}, Vt n -> Vt n -> Vt n.
Infix "&+" := Vplus (at level 50, left associativity) : matrix_scope.
Axiom Vminus : forall {n}, Vt n -> Vt n -> Vt n.
Infix "&-" := Vminus (at level 50, left associativity) : matrix_scope.
Axiom Id : forall {n}, Mt n n. 
Axiom sparsify: forall {n}, Mt n n -> Mt n n.
Axiom sparsify_correct: forall n: nat, forall M : Mt n n, M @= sparsify M. 
Axiom densify: forall {n}, Mt n n -> Mt n n.
Axiom densify_correct: forall n: nat, forall M : Mt n n, M @= densify M. 
Axiom dense_sparse_correct: forall n : nat, forall M1 M2 : Mt n n,
      M1 @* M2 = densify(M1 @* sparsify M2).
Axiom solveR: forall {n}, Mt n n -> Mt n n -> Mt n n.
Axiom solveR_correct: forall n: nat, forall M1 M2: Mt n n,
      M1 @* (inversion M2) = solveR M2 M1.
Axiom multi_assoc: forall n: nat, forall M1 M2 M3 : Mt n n,
      (M1 @* M2) @* M3 = M1 @* (M2 @* M3).
Record priori {n: nat} :=
  {
    x_pr : Vt n;
    p_pr : Mt n n;
  }.
Record posteriori {n: nat} :=
  {
    x_po : Vt n;
    p_po : Mt n n;
  }.


Definition similar {n: nat} {p1 p2 : @posteriori n} := 
  p1.(x_po) = p2.(x_po) /\ p1.(p_po) @= p2.(p_po).
Infix "$=" := similar (at level 70) : matrix_scope.

Definition update_posteriori_to_priori n (f: posteriori) (F B Q: Mt n n) (u: Vt n) :=
  let x' := F &* f.(x_po) &+ B &* u in
  let p' := F @* f.(p_po) @* (transpose F) @+ Q in
  {| x_pr := x'; p_pr := p' |}. 
Definition update_priori_to_posteriori n (f: priori) (H R: Mt n n) (z: Vt n) :=
  let y' := z &- H &* f.(x_pr) in
  let S' := H @* f.(p_pr) @* transpose(H) @+ R in
  let K' := f.(p_pr) @* transpose(H) @* inversion(S') in
  let x' := f.(x_pr) &+ K' &* y' in
  let p' := (Id @- K' @* H) @* f.(p_pr) in 
  {| x_po := x'; p_po := p' |}. 


Theorem Optimizer1: {f': _ & forall n f H R z, f' n f H R z = update_priori_to_posteriori n f H R z}. 
Proof. 
  intros. 
  econstructor.
  intros.
  destruct f.
  cbv delta [update_priori_to_posteriori].
  cbv beta.
  simpl p_pr. simpl x_pr.
  rewrite dense_sparse_correct.
  change ((let y' := z &- H &* x_pr0 in
   let S' := densify (H @* p_pr0 @* sparsify (transpose H)) @+ R in
   let K' := p_pr0 @* transpose H @* inversion S' in
   let x' := x_pr0 &+ K' &* y' in
   let p' := (Id @- K' @* H) @* p_pr0 in {| x_po := x'; p_po := p' |})) with ((let y' := z &- H &* x_pr0 in
   let K' := p_pr0 @* transpose H @* inversion ( densify (H @* p_pr0 @* sparsify (transpose H)) @+ R) in
   let x' := x_pr0 &+ K' &* y' in
   let p' := (Id @- K' @* H) @* p_pr0 in {| x_po := x'; p_po := p' |})).
  replace (p_pr0 @* transpose H @*
                 inversion (densify (H @* p_pr0 @* sparsify (transpose H)) @+ R))
          with (p_pr0 @* (transpose H @*
                                    inversion (densify (H @* p_pr0 @* sparsify (transpose H)) @+ R))) by (rewrite <- multi_assoc at 1; reflexivity).
  rewrite solveR_correct.
  replace (let y' := z &- H &* x_pr0 in
   let K' :=
     p_pr0 @*
     solveR (densify (H @* p_pr0 @* sparsify (transpose H)) @+ R) (transpose H) in
   let x' := x_pr0 &+ K' &* y' in
   let p' := (Id @- K' @* H) @* p_pr0 in {| x_po := x'; p_po := p' |})
          with (
   let K' :=
     p_pr0 @*
     solveR (densify (H @* p_pr0 @* sparsify (transpose H)) @+ R) (transpose H) in
   let x' := x_pr0 &+ K' &* (z &- H &* x_pr0) in
   let p' := (Id @- K' @* H) @* p_pr0 in {| x_po := x'; p_po := p' |}) by (auto).
  reflexivity. 
Defined. 


Variable n: nat.
Variable f: @ posteriori n. 
Variable F B Q: Mt n n.
Variable u: Vt n. 
Compute projT1 (Optimizer1 n f F B Q u). 


Record YC_data {n: nat} :=
  { X: Mt n n;
    Y: Mt n n;
  }. 


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
  reflexivity. 
Defined. 

Variable f1: @YC_data n.
Variable A: Mt n n.
Compute projT1 (Optimizer n f1 A). 
Print projT1. 





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

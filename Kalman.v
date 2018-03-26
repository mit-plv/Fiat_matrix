Require Import
        Coq.Lists.List
        Coq.Strings.String
        Coq.Setoids.Setoid
        Coq.Arith.PeanoNat
        Coq.omega.Omega
        Coq.setoid_ring.Ring
        Coq.setoid_ring.Ring_theory
        Matrix
        SparseMatrix
        DenseMatrix
        FiatHelpers
        MyHelpers
        MatrixLemmas
        optimize_ADT.

(* These operations need to be implemented. *)
(* log of the determinant of a matrix *)
Axiom logdet : forall {ME: MatrixElem} {n}, SDM n -> MEt.
(* log of 2*pi *)
Axiom log_two_pi : forall {ME: MatrixElem}, MEt.

Add Parametric Morphism ME n: (@logdet ME n)
    with signature (Meq (n:=n) (m:=n)) ==> (eq) as logdet_mor.
Admitted.

Definition Mplus {ME : MatrixElem} {M : Matrix} {m n : nat} :
  @Mt ME M m n -> @Mt ME M m n -> @Mt ME M m n := Melementwise_op MEplus.
Infix "@+" := Mplus.

Global Add Parametric Morphism {ME : MatrixElem} {M : Matrix} m n: (Mplus ) with
      signature (Meq (m:=m)(n:=n)) ==> (Meq (m:=m)(n:=n)) ==> (Meq (m:=m)(n:=n)) as Mplus_mor.
Admitted.

Section KalmanFilter.
  Variable m n : nat.
  Context {ME : MatrixElem}.

  Fixpoint nat_to_MEt (n : nat) : MEt :=
  match n with
  | 0 => e0
  | S n' => e1 +e nat_to_MEt n'
  end.

  Record KalmanState :=
    { x : Vt n;
      P : SDM n}.
  
  Definition KalmanSig : ADTSig :=
    ADTsignature {
      Constructor "Init" : KalmanState -> rep,
      Method "Predict"   : rep * (SDM n) * (SDM n) * (SDM n) * (Vt n) -> rep * KalmanState,
      Method "Update"    : rep * (SDM n) * (SDM n) * (Vt n) -> rep * MEt
    }.

  Definition KalmanSpec : ADT KalmanSig :=
    Def ADT {
      rep := KalmanState,

      Def Constructor1 "Init" (init_state: KalmanState): rep := ret init_state,,

      Def Method4 "Predict" (r : rep) (F: SDM n) (B: SDM n) (Q: SDM n) (u: Vt n) : rep * KalmanState :=
        x' <<- F &* r.(x) &+ B &* u;
        p' <<- F @* r.(P) @* (transpose F) @+ Q;
        xx <- {X | X @= x'};
        pp <- {P | P @= p'};
        ret (r, {|x := xx; P := pp|}),

      Def Method3 "Update" (r : rep) (H: Mt (Matrix := DenseMatrix) m n) (R: SDM n) (z: Vt m) : rep * MEt :=
        y' <<- z &- H @* r.(x);
        S' <<- H @* r.(P) @* transpose(H) @+ R;
        K' <<- r.(P) @* transpose(H) @* inversion(S');
        x' <<- r.(x) &+ K' @* y';
        p' <<- (Id @- K' @* H) @* r.(P);
        (*garbage <<- K' @* K' @+ S';*)
        ret ({| x := x'; P := p' |}, e0 -e (e1 /e (e1 +e e1)) *e (Mget (transpose y' @* inversion S' @* y') 0 0 +e logdet S' +e nat_to_MEt n *e log_two_pi))
    }%methDefParsing.

  Record SparseKalmanState :=
    { Sx : Vt n;
      SP : SSM n }.

  Definition use_a_sparse_P (or : KalmanState) (nr : SparseKalmanState) :=
    or.(x) @= nr.(Sx) /\ or.(P) @= nr.(SP).

  Definition SharpenedKalman :
    FullySharpened KalmanSpec.
  Proof.
    Optimize_ADT KalmanState SparseKalmanState use_a_sparse_P.
  Defined.
 
  Definition KalmanImpl : ComputationalADT.cADT KalmanSig :=
    Eval simpl in projT1 SharpenedKalman.

  Print KalmanImpl.
End KalmanFilter.

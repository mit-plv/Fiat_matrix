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
   
Section AlphaBetaFilter.
  Variable n : nat.
  Context {ME : MatrixElem}.
  Variable DT : SDM n.
  Variable Alpha : SDM n.
  Variable Beta : SDM n. 
 
  Record ABState :=
    { x : Vt n;
      v : Vt n }.
  
  Definition ABSig : ADTSig :=
    ADTsignature {
      Constructor "Init" : ABState -> rep,
      Method "Predict"   : rep   -> rep * (Vt n),
      Method "Update"    : rep * (Vt n)  -> rep * unit
    }.

  Definition ABSpec : ADT ABSig :=
    Def ADT {
      rep := ABState,

      Def Constructor1 "Init" (init_state: ABState): rep := ret init_state,,

      Def Method0 "Predict" (r : rep) : rep * (Vt n) :=
        x' <<- r.(x);
        xx <- {X | X @= x'};
        ret (r, xx),

      Def Method1 "Update" (r : rep) (x_: Vt n): rep * unit :=
	x' <<- r.(x) &+ DT @* r.(v);
	v' <<- r.(v);
	rk <<- x_ &- x';
	x' <<- x' &+ Alpha @* rk;
	v' <<- v' &+ Beta @* rk;
	ret ({| x := x'; v := v' |}, tt)
        }%methDefParsing.
  
  Record NState :=
    { Sx : Vt n;
      Sv : Vt n }.

  Definition use_a_sparse_P (or : ABState) (nr : NState) :=
    or.(x) @= nr.(Sx) /\ or.(v) @= nr.(Sv).

  Definition SharpenedAB :
    FullySharpened ABSpec.
  Proof.
    Optimize_ADT ABState NState use_a_sparse_P.
  Defined.

  Definition ABImpl : ComputationalADT.cADT ABSig :=
    Eval simpl in projT1 SharpenedAB.

  Print ABImpl.

End AlphaBetaFilter.

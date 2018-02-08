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
        optimize_single_method.

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
      Method "Predict"   : rep * unit * unit * unit * unit  -> rep * (Vt n),
      Method "Update"    : rep * (Vt n) * unit * unit -> rep * unit
    }.

  Definition ABSpec : ADT ABSig :=
    Def ADT {
      rep := ABState,

      Def Constructor1 "Init" (init_state: ABState): rep := ret init_state,,

      Def Method4 "Predict" (r : rep) (_ : unit) (__: unit) (___ : unit) (____ : unit) : rep * (Vt n) :=
        x' <<- r.(x);
        xx <- {X | X @= x'};
        ret (r, xx),

      Def Method3 "Update" (r : rep) (x_: Vt n) (_: unit) (__ : unit): rep * unit :=
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
    start sharpening ADT.
    unfold StringId, StringId0, StringId1.

    Open Scope string_scope.

    hone representation using use_a_sparse_P;
      unfold use_a_sparse_P in *; cleanup; try reveal_body_evar.

    Ltac guess_pick_val r_o r_n:=
        let x := fresh "x" in
        let Sv := fresh "Sv" in
        evar (x: Vt n); evar (Sv: Vt n); refine pick val {| Sx := x; Sv := Sv |}; subst x; subst Sv; try (split; simpl; clearit r_o r_n; try apply eq_Mt_refl; eauto with matrices).
    
      {

        
        Optimize_single_method guess_pick_val r_o r_n.
      }

      {
        Optimize_single_method guess_pick_val r_o r_n.
      }
      
      {
        Optimize_single_method guess_pick_val r_o r_n.
      }

      cbv beta.
      expose_rets_hidden_under_blets. 
      finish_SharpeningADT_WithoutDelegation.

  Defined.

  Definition ABImpl : ComputationalADT.cADT ABSig :=
    Eval simpl in projT1 SharpenedAB.

  Print ABImpl.

End AlphaBetaFilter.

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

Section KalmanFilter.
  Variable n : nat.
  Context {ME : MatrixElem}.

  Record KalmanState :=
    { x : Vt n;
      P : SDM n }.

  Definition KalmanSig : ADTSig :=
    ADTsignature {
      Constructor "Init" : KalmanState -> rep,
      Method "Predict"   : rep * (SDM n) * (SDM n) * (SDM n) * (Vt n) -> rep * KalmanState,
      Method "Update"    : rep * (SDM n) * (SDM n) * (Vt n) -> rep * unit
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

      Def Method3 "Update" (r : rep) (H: SDM n) (R: SDM n) (z: Vt n) : rep * unit :=
        y' <<- z &- H &* r.(x);
        S' <<- H @* r.(P) @* transpose(H) @+ R;
        K' <<- r.(P) @* transpose(H) @* inversion(S');
        x' <<- r.(x) &+ K' &* y';
        p' <<- (Id @- K' @* H) @* r.(P);
        garbage <<- K' @* K' @+ S';
        ret ({| x := x'; P := p' |}, tt)
    }%methDefParsing.

  Record SparseKalmanState :=
    { Sx : Vt n;
      SP : SSM n }.

  Definition use_a_sparse_P (or : KalmanState) (nr : SparseKalmanState) :=
    or.(x) @= nr.(Sx) /\ or.(P) @= nr.(SP).

  Definition SharpenedKalman :
    FullySharpened KalmanSpec.
  Proof.
    start sharpening ADT.
    unfold StringId, StringId0, StringId1.

    Open Scope string_scope.

    hone representation using use_a_sparse_P;
      unfold use_a_sparse_P in *; cleanup; try reveal_body_evar.

      Ltac guess_pick_val r_o r_n:=
        let x := fresh "x" in
        let SP := fresh "SP" in
         evar (x: Vt n); evar (SP: SSM n); refine pick val {| Sx := x; SP := SP |}; subst x; subst SP; try (split; simpl; clearit r_o r_n; try apply eq_Mt_refl; eauto with matrices).

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

  Definition KalmanImpl : ComputationalADT.cADT KalmanSig :=
    Eval simpl in projT1 SharpenedKalman.

  Print KalmanImpl.

  (* Lemma refine_first : *)
  (*   forall {A B} (a a': Comp A) c (f: A -> Comp B), *)
  (*     refine a' a -> *)
  (*     refine (Bind a f) c -> *)
  (*     refine (Bind a' f) c. *)
  (* Proof. *)
  (*   intros. *)
  (*   etransitivity. *)
  (*   apply refine_under_bind_both; eauto. *)
  (*   reflexivity. *)
  (*   assumption. *)
  (* Qed. *)

  (* Ltac maybe_unfold_in haystack needle := *)
  (*   match constr:(tt) with *)
  (*   | _ => let e := (eval unfold needle in haystack) in e *)
  (*   | _ => constr:(haystack) *)
  (*   end. *)
End KalmanFilter.

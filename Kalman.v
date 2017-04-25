Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Coq.Strings.String
  Coq.Lists.List
  Fiat.ADTRefinement.BuildADTRefinements.

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
  Notation SDM n := (Mt (ME := E) (Matrix := DenseMatrix) n n).

  Axiom Vt: forall n: nat, Type.

  Record KalmanState (n: nat) := {
    x : Vt n;
    P : SDM n;
  }.

  Definition KalmanSig n : ADTSig :=
    ADTsignature {
      Constructor "Init" : (KalmanState n) -> rep,
      Method "Predict"   : rep * (SDM n) * (SDM n) * (SDM n) * (Vt n) -> rep * (KalmanState n),
      Method "Update"    : rep * (SDM n) * (SDM n) * (Vt n) -> rep * unit
    }.

  Axiom transpose : forall {n}, SDM n -> SDM n.
  Axiom Mplus : forall {n}, SDM n -> SDM n -> SDM n.
  Infix "@+" := Mplus (at level 50, left associativity) : matrix_scope.
  Axiom Mminus : forall {n}, SDM n -> SDM n -> SDM n.
  Infix "@-" := Mminus (at level 50, left associativity) : matrix_scope.
  Axiom MVtimes : forall {n}, SDM n -> Vt n -> Vt n.
  Axiom inversion : forall {n}, SDM n -> SDM n.
  Infix "&*" := MVtimes (at level 40, left associativity) : matrix_scope.
  Axiom Vplus : forall {n}, Vt n -> Vt n -> Vt n.
  Infix "&+" := Vplus (at level 50, left associativity) : matrix_scope.
  Axiom Vminus : forall {n}, Vt n -> Vt n -> Vt n.
  Infix "&-" := Vminus (at level 50, left associativity) : matrix_scope.
  Axiom Id : forall {n}, SDM n.

  Definition similar {n: nat} (p1 p2 : KalmanState n) :=
    p1.(x) = p2.(x) /\ p1.(P) @= p2.(P).
  Infix "$=" := similar (at level 70) : matrix_scope.

  Notation n := 42. (* FIXME *)

  Axiom block : forall A, A -> Comp A.

  Definition KalmanSpec : ADT (KalmanSig n) :=
    Def ADT {
      rep := KalmanState n,

      Def Constructor1 "Init" (init_state: KalmanState n): rep := ret init_state,,

      Def Method4 "Predict" (r : rep) (F: SDM n) (B: SDM n) (Q: SDM n) (u: Vt n) : rep * (KalmanState n) :=
        x' <- ret (F &* r.(x) &+ B &* u);
        p' <- ret (F @* r.(P) @* (transpose F) @+ Q);
        ret (r, {| x := x'; P := p' |}),

      Def Method3 "Update" (r : rep) (H: SDM n) (R: SDM n) (z: Vt n) : rep * unit :=
        y' <- ret (z &- H &* r.(x));
        S' <- ret (H @* r.(P) @* transpose(H) @+ R);
        K' <- ret (r.(P) @* transpose(H) @* inversion(S'));
        x' <- ret (r.(x) &+ K' &* y');
        p' <- ret ((Id @- K' @* H) @* r.(P));
        ret ({| x := x'; P := p' |}, tt)
   }%methDefParsing.

  Axiom magic : forall {A}, unit -> A.

  Definition SharpenedKalman :
    FullySharpened KalmanSpec.
  Proof.
    start sharpening ADT.
    unfold StringId, StringId0, StringId1.

    Open Scope string_scope.

    Definition no_change_in_rep (or : KalmanState n) (nr : KalmanState n) :=
      or = nr.

    Notation SSM n := (Mt (ME := E) (Matrix := SparseMatrix) n n).

    Axiom sparsify: forall {n}, SDM n -> SSM n.
    Axiom sparsify_correct: forall n: nat, forall M : SDM n, M @= sparsify M.
    Axiom densify: forall {n}, SSM n -> SDM n.
    Axiom densify_correct: forall n: nat, forall M : SSM n, M @= densify M.
    (* Axiom dense_sparse_correct: forall n : nat, forall M1 M2 : SDM n, *)
    (*       M1 @* M2 = densify(M1 @* sparsify M2). *)

    Record SparseKalmanState (n: nat) := {
      Sx : Vt n;
      SP : SSM n;
    }.

    Definition use_a_sparse_P (or : KalmanState n) (nr : SparseKalmanState n) :=
      or.(x) = nr.(Sx) /\ or.(P) @= nr.(SP).

    Arguments Mtimes : simpl never.
    (* Arguments DenseMatrix : simpl never. *)

    hone representation using use_a_sparse_P.

    Ltac cleanup :=
      repeat match goal with
             | [ H: _ /\ _ |- _ ] => destruct H
             | _ => progress subst
             | _ => progress (cbv iota)
             | _ => progress simpl
             (* | _ => simplify with monad laws *)
             | _ => progress unfold no_change_in_rep in *
             end.

    { (* Init *)
      cleanup.
      simplify with monad laws.
      unfold use_a_sparse_P.
      refine pick val {| Sx := _; SP := _ |}.
      finish honing.
      simpl.
      split.
      reflexivity.
      assert (forall M, M @= sparsify (n := n) M) by (apply (magic tt)).
      apply H0.
    }

    { (* Predict *)
      cleanup. (* FIXME how do I prevent 'block' from getting simplified? *)
      (* replace block with ret by (apply (magic tt)). *)

      (* simplify_with_applied_monad_laws_1. (* Jason: tips on this? *) *)
      (* simplify_with_applied_monad_laws_1. (* Jason: tips on this? *) *)

      simplify with monad laws.
      cleanup.
      unfold use_a_sparse_P in *.
      cleanup.
      refine pick val r_n; try solve [intuition].
      simplify with monad laws.
      assert (densify (r_n.(SP)) = r_o.(P)) by (apply (magic tt)).
      rewrite <- !H2.
      rewrite !H0.
      finish honing.
    }

    { (* Update *)
      cleanup.
      (* replace block with ret by (apply (magic tt)). *)
      simplify with monad laws.
      cleanup.
      unfold use_a_sparse_P in *.
      simpl.
      refine pick val {| Sx := _; SP := _ |}.
      simplify with monad laws.
      finish honing.
      simpl.
      cleanup.
      assert (densify (r_n.(SP)) = r_o.(P)) by (apply (magic tt)).
      rewrite <- !H2.
      rewrite !H0.
      split.
      reflexivity.

      assert (forall M, M @= sparsify (n := n) M) by (apply (magic tt)).
      apply H3.
    }

    finish_SharpeningADT_WithoutDelegation.
    
  Defined.

  Definition KalmanImpl : ComputationalADT.cADT (KalmanSig _) :=
    Eval simpl in projT1 SharpenedKalman.

  Print KalmanImpl.

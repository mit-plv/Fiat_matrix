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
        FiatHelpers.

Variable E: MatrixElem.
Notation SDM n := (Mt (ME := E) (Matrix := DenseMatrix) n n).
Notation SSM n := (Mt (ME := E) (Matrix := SparseMatrix) n n).

Axiom Vt: forall n: nat, Type.

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

Arguments Mtimes : simpl never.
(* Arguments DenseMatrix : simpl never. *)

Theorem refine_change_type A B:
  forall (a : Comp A) (f: A -> Comp B) (cast: A -> B) (cast_back: B -> A),
    (forall x, refine (f x) (f (cast_back (cast x)))) -> 
    refine (x <- a; f x)
           (x <- (y <- a; ret (cast y));
              f (cast_back x)).
Proof.
  intros.
  rewrite <- refine_bind_bind'.
  unfold refine.
  Transparent computes_to. 
  unfold computes_to.
  Transparent Bind.
  unfold Bind.
  intros. intros. 
  inversion H0; subst.
  exists x.
  split.
  - apply H1.
  - inversion H1; subst.
    unfold Ensembles.In in H3.
    inversion H3; subst; clear H3.
    inversion H4; subst; clear H4. 
    rewrite H.
    unfold Ensembles.In. inversion H3; subst.
    assumption.
Qed.

Section Test. 
Definition P1 := x <- { x | x > 0}; y <- ret (x*2); ret (x + y).
Theorem Ref : {P' : Comp nat |   refine P1 P'}.
Proof.
  unfold P1.
  eexists.
  refine pick val 3; auto.
  simplify with monad laws.
  reflexivity.
Defined.
Print exist.
Print proj1_sig.
Print proj2_sig.

Eval cbv [proj1_sig Ref] in  proj1_sig Ref. 
Compute proj1_sig Ref.

(*  unfold refine .
  
  Transparent computes_to. 
  unfold computes_to.
  Transparent Bind.
  unfold Bind.
  
  About Ensembles.Ensemble. 
  Unset Printing Notations.
  
  ** work to do: add decompose, and incorporate into the following opt code. 
  *)
End Test. 
Section KalmanFilter.
  Variable n : nat.

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
        ret (r, {| x := x'; P := p' |}),

      Def Method3 "Update" (r : rep) (H: SDM n) (R: SDM n) (z: Vt n) : rep * unit :=
        y' <<- z &- H &* r.(x);
        S' <<- H @* r.(P) @* transpose(H) @+ R;
        K' <<- r.(P) @* transpose(H) @* inversion(S');
        x' <<- r.(x) &+ K' &* y';
        p' <<- (Id @- K' @* H) @* r.(P);
        ret ({| x := x'; P := p' |}, tt)
    }%methDefParsing.

  Ltac reveal_body_evar :=
    match goal with
    | [ H := ?x : methodType _ _ _ |- _ ] => is_evar x; progress unfold H
    (* | [ H := ?x : constructorType _ _ |- _ ] => is_evar x; progress unfold H *)
    end.
   
  Ltac cleanup :=
    repeat match goal with
           | [ H: _ /\ _ |- _ ] => destruct H
           | _ => progress subst
           | _ => progress (cbv iota)
           | _ => progress simpl
           | _ => simplify with monad laws
           end.

  Axiom magic : forall {A}, unit -> A.

  Record SparseKalmanState :=
    { Sx : Vt n;
      SP : SSM n }.

  Definition use_a_sparse_P (or : KalmanState) (nr : SparseKalmanState) :=
    or.(x) = nr.(Sx) /\ or.(P) @= nr.(SP).

  Definition SharpenedKalman :
    FullySharpened KalmanSpec.
  Proof.
    start sharpening ADT.
    unfold StringId, StringId0, StringId1.

    Open Scope string_scope.

    Axiom sparsify: forall {n}, SDM n -> SSM n.
    Axiom sparsify_correct: forall n: nat, forall M : SDM n, M @= sparsify M.
    Axiom densify: forall {n}, SSM n -> SDM n.
    Axiom densify_correct: forall n: nat, forall M : SSM n, M @= densify M.
    Axiom matrix_eq_commutes :
      forall (m n: nat) ME M1 M2 (m1: @Mt ME M1 m n) (m2: @Mt ME M2 m n),
        m1 @= m2 -> m2 @= m1.
    Axiom solveR: forall {n}, SDM n -> SDM n -> SDM n.
    Axiom solveR_correct: forall n: nat, forall M1 M2:SDM n,
      M1 @* (inversion M2) = solveR M2 M1.
    Axiom multi_assoc: forall n: nat, forall M1 M2 M3 : SDM n,
          (M1 @* M2) @* M3 = M1 @* (M2 @* M3).
    Axiom Cholesky_DC: forall {n}, SDM n -> SDM n.
    Axiom solveR_lower: forall {n}, SDM n -> SDM n -> SDM n.
    Axiom solveR_upper: forall {n}, SDM n -> SDM n -> SDM n.
    Axiom Cholesky_DC_correct: forall n:nat, forall M1 M2 : SDM n, 
        solveR M1 M2 = solveR_upper (transpose (Cholesky_DC M1)) (solveR_lower (Cholesky_DC M1) M2). 
    
    Hint Resolve sparsify_correct densify_correct matrix_eq_commutes solveR_correct multi_assoc: matrices.

    hone representation using use_a_sparse_P;
      unfold use_a_sparse_P in *; cleanup; try reveal_body_evar.

    { (* Init *)
      refine pick val {| Sx := _; SP := _ |}.
      - finish honing.
      - simpl; auto with matrices.
    }

    { (* Predict *)
      unfold use_a_sparse_P in *; cleanup.

      assert (r_o.(P) = densify (r_n.(SP))) by (apply (magic tt)).
      rewrite !H0, !H2.

      refine blocked ret.
      (*rewrite blocked_ret_is_ret.
      simplify with monad laws.*)
      refine blocked ret.
      
      refine pick val r_n.
      - simplify with monad laws; finish honing.
      - eauto with matrices.
    }

    { (* Update *)
      unfold H.

      assert (r_o.(P) = densify (r_n.(SP))) by (apply (magic tt)).
      rewrite !H0, !H2.

      refine blocked ret.
      refine blocked ret.
      rewrite multi_assoc. 
      rewrite solveR_correct. 
      rewrite Cholesky_DC_correct. 
      repeat refine blocked ret.

      refine pick val {| Sx := bvar2; SP := sparsify bvar3 |}.
      - simplify with monad laws; finish honing.
      - simpl; eauto with matrices.
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
a  (* Proof. *)
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

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
        MyHelpers.


Variable E: MatrixElem.
Notation SDM n := (Mt (ME := E) (Matrix := DenseMatrix) n n).
Notation SSM n := (Mt (ME := E) (Matrix := SparseMatrix) n n).

Axiom Vt: forall n: nat, Type.
Definition transpose {n} (A : SDM n) :=
  @Mfill E DenseMatrix n n (fun i j => Mget A j i).
Axiom MVtimes : forall {n}, SDM n -> Vt n -> Vt n.
Axiom inversion : forall {n}, SDM n -> SDM n.
Infix "&*" := MVtimes (at level 40, left associativity) : matrix_scope.
Axiom Vplus : forall {n}, Vt n -> Vt n -> Vt n.
Infix "&+" := Vplus (at level 50, left associativity) : matrix_scope.
Axiom Vminus : forall {n}, Vt n -> Vt n -> Vt n.
Infix "&-" := Vminus (at level 50, left associativity) : matrix_scope.
Definition Id {n} := I n E DenseMatrix.

Arguments Mtimes : simpl never.
(* Arguments DenseMatrix : simpl never. *)

Opaque DenseMatrix. 
  
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
        garbage <<- K' @* K' @+ S';
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

    Definition sparsify {n} (A: SDM n) := @Mfill E SparseMatrix n n (fun i j => Mget A i j). 
    Lemma sparsify_correct: forall n: nat, forall M : SDM n, M @= sparsify M.
    Proof.
      intros.
      unfold sparsify.
      unfold "@=".
      intros. 
      rewrite Mfill_correct; try assumption.
      reflexivity.
    Qed.

    (* can be optimized *) 
    Definition densify {n} (A: SSM n) := @Mfill E DenseMatrix n n (fun i j => Mget A i j). 
    Lemma densify_correct: forall n: nat, forall M : SSM n, M @= densify M.
    Proof.
      intros.
      unfold densify.
      unfold "@=".
      intros.
      rewrite Mfill_correct; try assumption.
      reflexivity.
    Qed.
    Lemma densify_correct_rev: forall n: nat, forall M : SSM n,  densify M @= M.
    Proof.
      intros.
      unfold densify.
      unfold "@=".
      intros.
      rewrite Mfill_correct; try assumption.
      reflexivity.
    Qed.
    
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
    Axiom ABv_assoc: forall n:nat, forall A B: SDM n, forall v : Vt n,
      MVtimes (A @* B) v =  MVtimes A (MVtimes B v). 
    Axiom Cholesky_DC_correct: forall n:nat, forall M1 M2 : SDM n, 
        solveR M1 M2 = solveR_upper (transpose (Cholesky_DC M1)) (solveR_lower (Cholesky_DC M1) M2). 
    Axiom Densify_correct: forall n:nat, forall M : SDM n, forall S : SSM n,
            M @= S -> M = densify S.
    Axiom Densify_correct_rev: forall n:nat, forall M : SDM n, forall S : SSM n,
            M = densify S -> M @= S.
    Axiom dense_sparse_mul: forall {n}, SDM n -> SSM n -> SDM n.
    Axiom dense_sparse_mul_correct: forall {n}, forall A: SDM n, forall B: SSM n, 
            dense_sparse_mul A B = A @* densify B. 
    Axiom sparse_dense_mul: forall {n}, SSM n -> SDM n -> SDM n.
    Axiom sparse_dense_mul_correct: forall {n}, forall A: SSM n, forall B: SDM n, 
            sparse_dense_mul A B = densify A @*  B.
    Axiom dense_sparse_mul_to_sparse: forall {n}, SDM n -> SSM n -> SSM n.
    Axiom dense_sparse_mul_to_sparse_correct: forall {n}, forall A: SDM n, forall B: SSM n, 
            sparsify (dense_sparse_mul A B) = dense_sparse_mul_to_sparse A B. 
    Hint Resolve sparsify_correct densify_correct densify_correct_rev matrix_eq_commutes solveR_correct multi_assoc Densify_correct Densify_correct_rev dense_sparse_mul_correct sparse_dense_mul_correct dense_sparse_mul_to_sparse_correct: matrices.
    
    hone representation using use_a_sparse_P;
      unfold use_a_sparse_P in *; cleanup; try reveal_body_evar.

    Ltac clearit r_o r_n :=
        repeat match goal with
               | [ H: ?X r_o = _ _ |- context [?X r_o]] => rewrite !H
               | [ |- context [?X r_o] ] =>
                 let type_field := type of (X r_o) in
                 let type_new_state := type of (r_n) in
                 let field := fresh "field" in
                 let g := fresh "g" in
                 let f := fresh "f" in 
                 evar (field: Type);
                 evar (g: type_new_state -> field);
                 evar (f : field -> type_field);
                 assert (X r_o = f (g r_n)) by (subst g; subst f; eauto with matrices);
                 subst field;
                 subst g;
                 subst f
               end.
    Ltac guess_pick_val :=
        let x := fresh "x" in
        let SP := fresh "SP" in
         evar (x: Vt n); evar (SP: SSM n); refine pick val {| Sx := x; SP := SP |}; subst x; subst SP; try (split; simpl; eauto with matrices).
    Ltac end_template :=
        repeat refine blocked ret; try (simplify with monad laws); finish honing.
    Ltac Cholesky_Optimizer :=
      rewrite solveR_correct, Cholesky_DC_correct.
   
    Ltac ABv_Optimizer :=
      rewrite ABv_assoc. 

    Ltac sparse_mul_Optimizer :=
      rewrite <- ?dense_sparse_mul_correct, <- ?sparse_dense_mul_correct, ?dense_sparse_mul_to_sparse_correct. 

    Ltac Optimizers :=
      repeat (Cholesky_Optimizer || ABv_Optimizer || sparse_mul_Optimizer).
    
    Ltac ref_block :=
      repeat (refine blocked ret; Optimizers).

    Ltac Optimize1 :=
      etransitivity;
      [repeat Optimizers; try (erewrite refine_smaller; [ | intros; Optimize1; higher_order_reflexivity]);
      higher_order_reflexivity | ]; simpl.

    Ltac singleStepUnfolding :=
      repeat ((erewrite decompose_computation_left by eauto) || (erewrite decompose_computation_right by eauto) || (erewrite decompose_computation_left_unit by eauto) ||(erewrite decompose_computation_right_unit by eauto) || (erewrite decompose_computation_unit_unit by eauto) ||  (erewrite decompose_computation_unit_compose by eauto)) .
    
    Ltac Unfolding :=
       etransitivity;
       [singleStepUnfolding;
        try
          (erewrite refine_smaller;
           [ | intros;  Unfolding; higher_order_reflexivity ]);
        higher_order_reflexivity| ];
       simpl.

    Ltac converts_to_blocked_ret :=
      etransitivity;
      [try rewrite <- blet_equal_blocked_ret;
       try
         (erewrite refine_smaller;
          [ | intros; converts_to_blocked_ret; higher_order_reflexivity]);
       higher_order_reflexivity | ];
      simpl.

         
    Ltac removeDup :=
      etransitivity; [
        repeat
          ((try
              (etransitivity;
               [ erewrite refine_trivial_bind by eauto; higher_order_reflexivity | ]))       || 
        match goal with
        | [ H :  NoSubst (?Y = _)|- refine (x0 <<- ?Y; _) _] =>
          etransitivity;
          [ erewrite refine_substitute by eauto; higher_order_reflexivity | ]
        | [H : NoSubst (_ = ?Y) |- refine (x0 <<- ?Y; _) _] =>
           etransitivity;
          [ rewrite <- H; higher_order_reflexivity | ]
        | _  => refine blocked ret
        end);
        higher_order_reflexivity | ];
      simpl;
      converts_to_blocked_ret.

    Ltac RemoveUseless :=
      try
        (etransitivity;
         [ erewrite refine_smaller;
           [ | intros; RemoveUseless; higher_order_reflexivity];
           higher_order_reflexivity | ]);
      simpl; etransitivity;
      [ first [erewrite refine_trivial_bind2; eauto; progress higher_order_reflexivity|higher_order_reflexivity]  | ];
      simpl.
    

      Ltac substitute_all :=
        etransitivity;
        [repeat rewrite refine_substitute;
         higher_order_reflexivity | ]; simpl.

      Ltac magic A :=
        let t := type of A in
        let g := fresh "g" in
        let f := fresh "f" in
        let xxx := fresh "xxx" in
        evar (g : Type);
        evar (f: t -> ?g);
        match goal with
        | [|- refine (ret ?B) _] => assert (?f A = B) by (subst f; remember A as xxx; exists); eapply refine_substitute2 with (f := f) (a := A)
        | [|- refineEquiv (ret ?B) _] => assert (?f A = B) by (subst f; remember A as xxx; exists); eapply refine_substitute2 with (f := f) (a := A)
        end.
      
      Ltac match_formula X larger_layer:=
        lazymatch X with
        | ?A ?B =>
          tryif (is_variable B) then
            match_formula A (S O)
          else magic B
        | _ =>
          tryif (assert (larger_layer = S O) by auto) then fail 0
          else tryif (assert (X = ()) by auto) then fail 0
          else tryif (is_variable X) then fail 0
          else  magic X
        end.
      
      Ltac move_ret_to_blet_helper :=
        match goal with
        | [ |- context[ret (?X, ?Y)]] =>
          first [ match_formula X 0 | match_formula Y 0]
        end.

      Ltac move_ret_to_blet :=
        etransitivity;
        [etransitivity; [repeat move_ret_to_blet_helper| simpl]; try (erewrite refine_smaller; [ | intros; move_ret_to_blet ; higher_order_reflexivity]);
         higher_order_reflexivity | ]; simpl.

      Ltac Optimize_single_method r_o r_n:=
        clearit r_o r_n;
      
        etransitivity; [
        repeat refine blocked ret;
        guess_pick_val;
        try simplify with monad laws;
        higher_order_reflexivity;
        simpl | ];

        converts_to_blocked_ret;
        substitute_all;

        move_ret_to_blet;
        
        Optimize1;
        Unfolding;
        RemoveUseless;
        removeDup;

        end_template. 
      {
        Optimize_single_method r_o r_n.
      }

      {
        Optimize_single_method r_o r_n.
      }
      

      { (* Update *) 
        Optimize_single_method r_o r_n.
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

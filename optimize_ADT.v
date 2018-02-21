Require Import MyHelpers.
Require Import Matrix.
Require Import MatrixLemmas.
Require Import Coq.Setoids.Setoid.
Require Import FiatHelpers.
Require Import Coq.Strings.String.

Ltac clearit r_o r_n :=
    try apply Densify_correct_rev;
    repeat match goal with
           | [ H: ?X r_o @= _ _ |- context [?X r_o]] => rewrite !H
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
             setoid_replace (X r_o) with (f (g r_n)) by (subst g; subst f; eauto with matrices);
             subst field;
             subst g;
             subst f
           end.

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
      tryif (unify larger_layer (S O)) then fail 0
      else tryif (unify X ()) then fail 0
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

  Ltac clear_a_Meq_pick r_o r_n:=
    match goal with
    | [|- refine (_ <- _; _ <- _; _) _] => erewrite pick_change_condition; [| let X := fresh "X" in let H := fresh "H" in intros X H; clearit r_o r_n; apply H]; refine pick val _; [ | apply eq_Mt_refl]; simplify with monad laws
    end.

  Ltac split_on_and :=
    match goal with
      | [ |- _ /\ _] => split
    end.

  Ltac guess_pick_val r_o r_n:=
        unshelve erewrite refine_pick_val; [ econstructor | | try (repeat split_on_and; simpl; clearit r_o r_n; try apply eq_Mt_refl; eauto with matrices)].

  Ltac Optimize_single_method r_o r_n:=
    
    etransitivity; [
      substitute_all;
      repeat clear_a_Meq_pick r_o r_n;
      guess_pick_val r_o r_n;
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

  Ltac unfold_all_strings :=
      repeat match goal with
             | [ |- context[?x]] =>
               let A := type of x in
               assert (A = string) by auto;
               unfold x
             | [ H : ?A = ?A |- _] => clear H
             end.

  Ltac find_ro_rn_then_optimize OldType NewType :=
    match goal with
    | [r_o: OldType, r_n: NewType |- _] => Optimize_single_method r_o r_n
    | [ |- _] => Optimize_single_method OldType OldType
    end.
  
  Ltac Optimize_ADT OldType NewType relation:=
    start sharpening ADT;
    unfold_all_strings;
    hone representation using relation;
    unfold relation in *; cleanup; try reveal_body_evar; 
    try find_ro_rn_then_optimize OldType NewType;
    cbv beta;
    expose_rets_hidden_under_blets;
    finish_SharpeningADT_WithoutDelegation.

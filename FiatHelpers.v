Require Export
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements
  Fiat.Computation.Core.

Definition _blocked_ret : { x: forall A, A -> Comp A | x = ret }.
Proof. exists Return; reflexivity. Qed.

Definition blocked_ret {A} := (proj1_sig _blocked_ret A).
Arguments blocked_ret [A] _ _.
Notation "x <<- a ; y" := (Bind (blocked_ret a%comp) (fun x => y%comp))
                            (at level 81, a at level 200, y at level 81).

Definition blocked_let {A B} (a: A) (f: A -> B) := let x := a in f x.
Arguments blocked_let : simpl never.

Notation "'blet' x := a 'in' y" :=
  (blocked_let a (fun x => y))
    (at level 81, a at level 200, y at level 81,
     format "'[v' 'blet'  x  :=  a  'in' '/' y ']'").

Add Parametric Morphism {A B} : (@blocked_let A B)
    with signature (eq ==> pointwise_relation _ eq ==> eq)
      as blet_morphism.
Proof.
  unfold pointwise_relation; simpl; intros * H.
  unfold blocked_let; rewrite H; reflexivity.
Qed.

Lemma blet_ret_commute {A B} :
  forall (a: A) (f: A -> B),
    blocked_let a (fun x => ret (f x)) = ret (blocked_let a f).
Proof.
  unfold blocked_let; reflexivity.
Qed.

Global Opaque blocked_let.

Lemma blocked_ret_is_ret :
  blocked_ret = ret.
Proof. exact (proj2_sig _blocked_ret). Qed.

Ltac unblock :=
  rewrite blocked_ret_is_ret at 1.

Lemma bound_blocked_ret_is_bound_ret {A B} (a: A) (f: A -> Comp B) :
  Bind (blocked_ret a) f = Bind (ret a) f.
Proof. rewrite blocked_ret_is_ret; reflexivity. Qed.

Lemma unfold_blocked_ret X Y (f : X -> Comp Y) x y
  : refine (f x) y
    -> refine (Bind (blocked_ret x) f) y.
Proof. rewrite blocked_ret_is_ret; apply refine_bind_unit_helper. Qed.

Lemma blocked_ret_to_let {A B} :
  forall aa (x y : A -> Comp B),
    refine (x aa) (y aa) ->
    refine (a <- blocked_ret aa; x a) (blet a := aa in y a).
Proof.
  intros; apply unfold_blocked_ret; simpl; assumption.
Qed.

Ltac add_let_in_head term new_head expr :=
  let rec aux head_and_args restore_args_fn :=
      lazymatch head_and_args with
      | ?term ?arg => aux term (fun term' => restore_args_fn (term' arg))
      | ?head => constr:(blet x := expr in restore_args_fn (new_head x))
      end in
  let tt := type of term in
  let term' := aux term (fun y: tt => y) in
  let reduced := (eval cbv beta in term') in
  constr:(reduced).

(** Example:
    Axiom f : nat -> nat -> nat.
    Axiom g : nat -> nat -> nat -> nat.
    let tt := add_let_in_head (f 1 2) (g) (5) in
    pose tt. (* blet x := 5 in g x 1 2 *) *)

Definition NoSubst (P: Prop) := P.

Ltac args term :=
  match term with
  | ?term ?a1 ?a2 => let all_but_last := args (term a1) in
                    constr:(all_but_last, a2)
  | _ ?a => constr:(a)
  | _ => constr:(tt)
  end.

Ltac refine_blocked_ret_cleanup hd' const :=
  cbv beta;
  unfold hd' in *; clear hd';
  let bvar := fresh "bvar" in
  let bvar_eqn := fresh "bvar_eqn" in
  set const as bvar;
  assert (NoSubst (bvar = const)) as bvar_eqn by reflexivity;
  clearbody bvar;
  apply blocked_ret_to_let.

Tactic Notation "refine" "blocked" "ret" :=
  lazymatch goal with
  | [  |- refine (Bind (blocked_ret ?const) _) ?comp] =>
    let old_evar := head comp in
    let old_evar_type := type of old_evar in
    let const_type := type of const in
    let new_evar := fresh in
    evar (new_evar: const_type -> old_evar_type);
      let refined := add_let_in_head comp new_evar const in
      first [ unify comp refined |
              let aa := args comp in
              fail 1 "Unification of" comp "and" refined
                   "failed.  Make sure that" const
                   "can be written as a function of" aa ];
      refine_blocked_ret_cleanup new_evar const
  end.

Ltac expose_rets_hidden_under_blets :=
  hone representation using eq;
  subst; simpl; try simplify with monad laws;
  repeat setoid_rewrite blet_ret_commute;
  [ refine pick eq;
    try simplify with monad laws;
    try rewrite <- surjective_pairing;
    try finish honing.. | ].

Ltac finish_SharpeningADT_WithoutDelegation ::=
  eapply FullySharpened_Finish;
  [ FullySharpenEachMethod
      (@Vector.nil ADTSig)
      (@Vector.nil Type)
      (ilist.inil (B := fun nadt => ADT (delegateeSig nadt)));
    try simplify with monad laws; simpl; try refine pick eq; try simplify with monad laws;
    try first [ simpl]; try rewrite <- surjective_pairing;
    (* Guard setoid rewriting with [refine_if_If] to only occur when there's
    actually an [if] statement in the goal.  This prevents [setoid_rewrite] from
    uselessly descending into folded definitions. *)
    repeat match goal with
             | [ |- context [ if _ then _ else _ ] ] =>
               setoid_rewrite refine_if_If at 1
           end;
    repeat first [
             higher_order_reflexivity
           | simplify with monad laws
           | Implement_If_Then_Else
           | Implement_If_Opt_Then_Else ]
  | extract_delegate_free_impl
  | simpl; higher_order_reflexivityT ].



(* ========================= *)
Require Import Fiat.Computation.Refinements.Tactics. 

Lemma decompose_computation_left {A B C D E F}:
  forall (a: A) (b: B) (d: D) (e: E) (op2: A -> B -> C) (op: C -> D -> E) (com: E -> Comp F), 
    e = op (op2 a b) d -> refineEquiv (y <<- e; com(y)) (  x <<- op2 a b; y <<- op x d; com(y)) .
Proof.
  intros.
  split.
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + rewrite <- H.
      econstructor.  
    + unfold Ensembles.In.
      inversion H0. inversion H0'.
      rewrite H1 in *.
      rewrite H2 in *.
      rewrite H.
      assumption. 
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + unfold Ensembles.In.
      econstructor.
    + econstructor.
      split; eauto.
Qed.


Lemma decompose_computation_right {A B C D E F}:
  forall (a: A) (b: B) (d: D) (e: E) (op2: A -> B -> C) (op: D -> C -> E) (com: E -> Comp F), 
    e = op d (op2 a b) -> refineEquiv (y <<- e; com(y)) (  x <<- op2 a b; y <<- op d x; com(y)) .
Proof.
  intros.
  split.
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + rewrite <- H.
      econstructor.  
    + unfold Ensembles.In.
      inversion H0. inversion H0'.
      rewrite H1 in *.
      rewrite H2 in *.
      rewrite H.
      assumption. 
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + unfold Ensembles.In.
      econstructor.
    + econstructor.
      split; eauto.
Qed.


Lemma decompose_computation_right_unit {A B C D E}:
  forall (a: A) (b: B) (d: D) (op2: A -> C) (op: B -> C -> D) (com: D -> Comp E), 
    d = op b (op2 a) -> refineEquiv (y <<- d; com(y)) (  x <<- op2 a; y <<- op b x; com(y)) .
Proof.
  intros.
  split.
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + rewrite <- H.
      econstructor.  
    + unfold Ensembles.In.
      inversion H0. inversion H0'.
      rewrite H1 in *.
      rewrite H2 in *.
      rewrite H.
      assumption. 
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + unfold Ensembles.In.
      econstructor.
    + econstructor.
      split; eauto.
Qed.


Lemma decompose_computation_left_unit {A B C D E}:
  forall (a: A) (b: B) (d: D) (op2: A -> C) (op: C -> B -> D) (com: D -> Comp E), 
    d = op (op2 a) b -> refineEquiv (y <<- d; com(y)) (  x <<- op2 a; y <<- op x b; com(y)) .
Proof.
  intros.
  split.
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + rewrite <- H.
      econstructor.  
    + unfold Ensembles.In.
      inversion H0. inversion H0'.
      rewrite H1 in *.
      rewrite H2 in *.
      rewrite H.
      assumption. 
  - intros.
    rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + unfold Ensembles.In.
      econstructor.
    + econstructor.
      split; eauto.
Qed.


Lemma decompose_computation_unit_unit {A C D E}:
  forall (a: A) (d: D) (op2: A -> C) (op: C -> D) (com: D -> Comp E), 
    d = op (op2 a) -> refineEquiv (y <<- d; com(y)) (  x <<- op2 a; y <<- op x; com(y)) .
Proof.
  intros; split.
  - repeat intro. computes_to_inv. rewrite blocked_ret_is_ret in *.
    repeat (econstructor; try eauto).
    unfold Ensembles.In.
    inversion H0. inversion H0'.
    rewrite <- H1.
    rewrite H.
    reflexivity.
  - intros. rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    repeat (econstructor; try eauto).
Qed.


Lemma decompose_computation_unit_compose {A B C D E}:
  forall (a: A) (b: B) (d: D) (op2: A -> B -> C) (op: C -> D) (com: D -> Comp E), 
    d = op (op2 a b) -> refineEquiv (y <<- d; com(y)) (x <<- op2 a b; y <<- op x; com(y)) .
Proof.
  intros; split.
  - repeat intro. computes_to_inv. rewrite blocked_ret_is_ret in *.
    repeat (econstructor; try eauto).
    unfold Ensembles.In.
    inversion H0. inversion H0'.
    rewrite H.
    rewrite <- H1.
    reflexivity. 
  - intros. rewrite H.
    repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    repeat (econstructor; try eauto).
Qed.

Lemma refine_smaller (A B: Type) (C: A) (f g: A -> Comp B):
        (forall x, refineEquiv (f x) (g x))
        -> refineEquiv (x <<- C; f x) (x <<- C; g x).
Proof. 
  intros.
  assert (refineEquiv (f C) (g C)) by apply H.
  rewrite blocked_ret_is_ret in *.
  erewrite refineEquiv_bind_unit.
  erewrite refineEquiv_bind_unit.
  apply H. 
Qed.

Lemma refine_trivial_bind {A B}:
      forall (a: A) (b: Comp B),
             refineEquiv (x <<- a; b) (b).
Proof.
  intros.
  rewrite blocked_ret_is_ret in *.
  split.
  - repeat intro.
    computes_to_inv.
    econstructor.
    split.
    + econstructor.
    + assumption.
  -  repeat intro.
     inversion H.
     inversion H0.
     assumption.
Qed.

Lemma refine_trivial_bind2 {A B}:
  forall (a: A) (f: A -> Comp B) (g: Comp B),
      (forall x: A, (f x) = g) -> refineEquiv (x <<- a; f x) (g).
Proof.
  intros.
  rewrite blocked_ret_is_ret in *.
  split; repeat intro; computes_to_inv; repeat (econstructor; eauto).
  - unfold Ensembles.In.
    rewrite H. assumption.
  - rewrite H in H0'.  assumption.
Qed.

Lemma refine_substitute {A B}:
      forall (a: A) (f: A -> Comp B),
             refineEquiv (x <<- a; f x) (f a).
Proof.
  intros.
  rewrite blocked_ret_is_ret in *.
  split.
  - repeat intro.
    computes_to_inv.
    econstructor.
    split.
    + econstructor.
    + assumption.
  -  repeat intro.
     inversion H.
     inversion H0.
     inversion H1.
     eauto. 
Qed.

Lemma refine_substitute2:
        forall A B, forall (a: A) (f: A -> B),
            refineEquiv (ret (f a))  (x <<- a; ret (f x)) .
Proof.
  intros.
  rewrite refine_substitute.
  higher_order_reflexivity.
Qed.

Lemma blet_equal_blocked_ret {A B}:
      forall (a: A) (f: A -> Comp B),
             refineEquiv (x <<- a; f x) (blet x := a in f x).
Proof.
  intros.
  rewrite blocked_ret_is_ret in *.
  split.
  - repeat intro.
    computes_to_inv.
    econstructor.
    split.
    + econstructor.
    + assumption.
  - repeat intro.
    inversion H.
    inversion H0.
    inversion H1.
    eauto.
Qed. 


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

(* Ltac add_let_in_head2 term new_head expr :=
  let rec aux head_and_args restore_args_fn :=
      lazymatch head_and_args with
      | ?term ?arg => aux term (fun term' => restore_args_fn (term' arg))
      | ?head => constr:(x <<- expr; restore_args_fn (new_head x))
      end in
  let tt := type of term in
  let term' := aux term (fun y: tt => y) in
  let reduced := (eval cbv beta in term') in
  constr:(reduced).

Ltac refine_blocked_ret_cleanup2 hd' const :=
  cbv beta;
  unfold hd' in *; clear hd';
  let bvar := fresh "bvar" in
  let bvar_eqn := fresh "bvar_eqn" in
  set const as bvar;
  assert (NoSubst (bvar = const)) as bvar_eqn by reflexivity;
  clearbody bvar;
  etransitivity; [| rewrite refine_substitute; higher_order_reflexivity];
  etransitivity; [rewrite refine_substitute; higher_order_reflexivity |].
  
  

Tactic Notation "refine" "blocked" "ret2" :=
  lazymatch goal with
  | [  |- refine (Bind (blocked_ret ?const) _) ?comp] =>
    let old_evar := head comp in
    let old_evar_type := type of old_evar in
    let const_type := type of const in
    let new_evar := fresh in
    evar (new_evar: const_type -> old_evar_type);
    let refined := add_let_in_head2 comp new_evar const in
    first [ unify comp refined |
            let aa := args comp in
            fail 1 "Unification of" comp "and" refined
                 "failed.  Make sure that" const
                 "can be written as a function of" aa ];
    refine_blocked_ret_cleanup2 new_evar const
  end.

  
Lemma decompose_function {A B C D}:
  forall (a: A) (f: A -> C) (g: A -> B) (h: B -> C) (com: C -> Comp D), 
    f(a) = h(g(a)) -> refineEquiv (y <<- f(a); com(y)) (x <<- g(a); y <<- h(x); com(y)) .
Proof.
  intros.
  split.
  - intros.
    rewrite H.
    repeat intro.
    
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + inversion H0. rewrite H1.
      eassumption.
    + eassumption.
  - repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *. 
    econstructor.
    econstructor.
    + rewrite H in H0.
      repeat (econstructor; try eauto).
    + rewrite H in H0.
      repeat (econstructor; try eauto).
Qed.


Lemma decompose_function2:
  forall (I O P Q D: Type) (i: I) (f: I -> O) (g: I -> P) (h: I -> Q) (op: P -> Q -> O) (com: O -> Comp D), 
    f(i) = op (g i) (h i) -> refineEquiv (y <<- f(i); com(y)) (x0 <<- g(i); x1 <<- h(i); y <<- op x0 x1; com(y)) .

Proof.
  intros; split.
  - repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    rewrite H.
    econstructor.
    econstructor.
    + eauto. inversion H0. inversion H0'. 
      rewrite H1, H2.
      eassumption.
    + eassumption.
  - repeat intro.
    computes_to_inv.
    rewrite blocked_ret_is_ret in *.
    econstructor.
    econstructor.
    + rewrite H in H0.
      unfold  Ensembles.In.
      eexists.
    + econstructor.
      econstructor.
      * eexists.
      * econstructor.
        econstructor.
        -- exists.
        -- rewrite <- H.
           unfold  Ensembles.In.
           inversion H0.
           rewrite H1.
           assumption.
Qed.*)
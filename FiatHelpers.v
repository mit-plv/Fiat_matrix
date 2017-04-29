Require Export
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

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


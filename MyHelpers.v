Require Import PeanoNat.
Require Import List.
Require Import Coq.omega.Omega.
Require Import FiatHelpers.

Section ListHelpers.
  Lemma nth_default_0: forall A: Type, forall a b : A, forall l: list A, 
        nth_default b (a::l) 0 = a.
  Proof. 
    intros a l. 
    reflexivity. 
  Qed. 

  Lemma nth_default_nil: forall A: Type, forall b : A, forall i, 
          nth_default b nil i = b.
  Proof. 
    intros A0. intros b. intros i. 
    unfold nth_default. 
    unfold nth_error. 
    destruct i. 
    - reflexivity. 
    - reflexivity. 
  Qed. 

  Lemma nth_default_S: forall A: Type, forall a b : A, forall l: list A, forall i, 
            nth_default b (a :: l) (S i) = nth_default b l i.
  Proof. 
    intros A0 a b l i. 
    unfold nth_default. 
    unfold nth_error. 
    reflexivity. 
  Qed. 


  Lemma nth_default_map : forall A B X d d0 i, forall f: A -> B, 
        f (d) = d0 -> nth_default d0 (map f X) i =  f (nth_default d X i). 
  Proof. 
    intros A B X.  
    induction X as [| v X IHX]. 
    - intros d d0 i0 f H. simpl. rewrite nth_default_nil. rewrite nth_default_nil. rewrite H. reflexivity. 
    - intros d d0 i0 f H. destruct i0. 
      + rewrite nth_default_0. simpl. rewrite nth_default_0. reflexivity. 
      + rewrite nth_default_S. simpl. rewrite nth_default_S. apply IHX. 
        apply H.
  Qed.

  Lemma nth_default_map_in_range : forall A B X d d0 i, forall f: A -> B, 
        i < length X -> nth_default d0 (map f X) i =  f (nth_default d X i). 
  Proof. 
    intros A B X.  
    induction X as [| v X IHX]. 
    - intros d d0 i0 f H. inversion H. 
    - intros d d0 i0 f H. destruct i0. 
      + rewrite nth_default_0. simpl. rewrite nth_default_0. reflexivity. 
      + rewrite nth_default_S. simpl. rewrite nth_default_S. apply IHX. 
        simpl in H. omega. 
  Qed.
End ListHelpers.

Ltac elim_bool:=
  repeat match goal with
         | [ |- context [Nat.eqb ?x ?y]] => let eq := fresh "eq" in destruct (x =? y) eqn: eq
         | [H: ?x =? ?y = false |- _] => apply Nat.eqb_neq in H
         | [H: ?x =? ?y = true |- _] => apply Nat.eqb_eq in H
         | [H: ?x <? ?y = true |- _] => apply Nat.ltb_lt in H
         | [H: ?x <? ?y = false |- _] => apply Nat.ltb_ge in H
         | [H: ?x <=? ?y = true |- _] => apply Nat.leb_le in H
         | [H: ?x <=? ?y = false |- _] => apply Nat.leb_gt in H
         end.

Ltac is_variable A :=
  match goal with
  | [ B :_ |- _] =>
    let eq := fresh "eq" in
    assert (eq: A = B) by auto; clear eq
  end.

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


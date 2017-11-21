Require Import PeanoNat.

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
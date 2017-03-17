Require Import ZArith.
Require Import Matrix.

Module ZElem : MatrixElem.
  Definition t := Z.

  Definition zero := 0%Z.
  Definition one := 1%Z.

  Definition opp := Z.opp.
  Definition plus : t -> t -> t := Z.add.
  Definition minus : t -> t -> t := Z.sub.
  Definition times : t -> t -> t := Z.mul.

  Theorem ring : ring_theory zero one plus times minus opp eq.
  Proof.
    apply Zth.
  Qed.

  Module Import Notations.      (* TODO CPC *)
    Infix "*e" := times (at level 30).
    Infix "+e" := plus (at level 60).
    Infix "-e" := minus (at level 60).
  End Notations.
End ZElem.

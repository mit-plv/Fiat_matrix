Require Import ZArith.
Require Import Matrix.

Definition ZElem : MatrixElem :=
  {| MEt := Z;

     MEzero := 0%Z;
     MEone := 1%Z;

     MEopp := Z.opp;
     MEplus := Z.add;
     MEminus := Z.sub;
     MEtimes := Z.mul;

     MEring := Zth |}.

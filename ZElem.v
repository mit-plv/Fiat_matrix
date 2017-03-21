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

Definition DenseMatrix {ME: MatrixElem} : Matrix.
 unshelve eapply {| Mt m n := list (list MEt);
                    Mget m n mx i j := List.nth_default MEzero (List.nth_default nil mx j) i;
                    Mtimes m n p m1 m2 := (* Implementation of multiplication *) |};
   simpl; intros.
 (* Proof of correctness of multiplication here *)
Defined.


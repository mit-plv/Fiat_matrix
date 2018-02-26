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
        MyHelpers
        MatrixLemmas
        optimize_ADT.

Section Perceptron.
  Variable n : nat.
  Context {ME : MatrixElem}.
  Definition eqq : MEt -> MEt -> bool := fun x y => MEeqdec x y.
  
  Parameter pos: 0 < n.
  
  Hint Resolve pos. 
    
  Record THETA :=
    { theta : Vt n;
      theta0: MEt }.
  
  Definition PerceptronSig : ADTSig :=
    ADTsignature {
      Constructor "Init" : THETA -> rep,
      Method "Predict"   : rep * (Vt n)  -> rep * MEt,
      Method "Update"    : rep * (Vt n) * (MEt) -> rep * unit
    }.

  Definition PerceptronSpec : ADT PerceptronSig :=
    Def ADT {
      rep := THETA,

      Def Constructor1 "Init" (init_state: THETA): rep := ret init_state,,

      Def Method1 "Predict" (r : THETA) (x: Vt n) : rep * (MEt) :=
        ans <<- (Mget ((transpose (r.(theta))) @* x) 0 0) +e r.(theta0);
        ret (r, ans),

      Def Method2 "Update" (r : THETA) (x: Vt n) (y: MEt): rep * unit :=
        tr <<- transpose r.(theta);
        prod <<- tr @* x;
        ans <<- Mget prod 0 0 +e r.(theta0);
        neq <<- if eqq ans y then 0 else 1;
        theta' <<- if neq =? 1 then r.(theta) @+ x else r.(theta);
        theta0' <<- if neq =? 1 then r.(theta0) +e y else r.(theta0); 
        ret ({|theta := theta'; theta0 := theta0'|}, tt)
        }%methDefParsing.
  
  Record THETA_ :=
    { theta_ : Vt n;
      theta0_ : MEt }.

  Definition use_same (or : THETA) (nr : THETA_) :=
    or.(theta) @= nr.(theta_) /\ or.(theta0) = nr.(theta0_).

  Definition SharpenedPerceptron :
    FullySharpened PerceptronSpec.
  Proof.
    Optimize_ADT THETA THETA_ use_same.
  Defined. 

  Definition PerceptronImpl : ComputationalADT.cADT PerceptronSig :=
    Eval simpl in projT1 SharpenedPerceptron.

  Print PerceptronImpl.

End Perceptron.

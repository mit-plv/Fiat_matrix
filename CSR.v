Require Import List.
Require Import Setoid.
Require Import PeanoNat.
Require Import Coq.omega.Omega. 
Require Import Matrix. 
Require Import Coq.setoid_ring.Ring.
Require Import Coq.setoid_ring.Ring_theory.

Record AA := {
  x: nat;
  y:nat;
}.



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



Section A.
 Variable ME : MatrixElem.
 Add Ring Aring : MEring.


Record CSR_Matrix {ME: MatrixElem} {m n : nat} :=
{
  A : list MEt; 
  IA : list nat; 
  JA : list nat; 
  Content_IA_0: nth_default 0 IA 0 = 0; 
  Content_IA_i: forall i : nat, i < m -> nth_default 0 IA i <= nth_default 0 IA (i + 1); 
  Content_JA_i: forall i: nat, nth_default 0 JA i < n;
  Content_JA: forall i j j': nat, i < m -> nth_default 0 IA i < j -> j <= nth_default 0 IA (i + 1)
                                  -> nth_default 0 IA i < j' -> j' <= nth_default 0 IA (i + 1)
                                -> j < j' -> nth_default 0 JA j < nth_default 0 JA (j'); 
  
}. 

Fixpoint get_v_CSR {ME: MatrixElem} (m n: nat) (M: @CSR_Matrix ME m n) (b a j: nat) :=
  match b with 
  | 0 => MEzero
  | S b' => if (b =? a) then MEzero
            else if (nth_default 0 M.(JA) b <? j) then MEzero
            else if (nth_default 0 M.(JA) b =? j) then nth_default MEzero M.(A) b
            else get_v_CSR m n M b' a j 
  end. 

Definition Mget_CSR {ME: MatrixElem} (m n i j: nat) (M: @CSR_Matrix ME m n):= 
if andb (i <? m) (j <? n) then
  get_v_CSR m n M (nth_default 0 M.(IA) (i + 1)) (nth_default 0 M.(IA) i) j
else
  MEzero.



Record CSC_Matrix {ME: MatrixElem} {m n : nat} :=
{
  B : list MEt; 
  IB : list nat; 
  JB : list nat; 
  Content_IB_0: nth_default 0 IB 0 = 0; 
  Content_IB_i: forall i : nat, i < n -> nth_default 0 IB i <= nth_default 0 IB (i + 1); 
  Content_JB_i: forall i: nat, nth_default 0 JB i < m;
  Content_JB: forall i j j': nat, i < n -> nth_default 0 IB i < j -> j <= nth_default 0 IB (i + 1)
                                  -> nth_default 0 IB i < j' -> j' <= nth_default 0 IB (i + 1)
                                -> j < j' -> nth_default 0 JB j < nth_default 0 JB (j'); 
  }. 

Fixpoint get_v_CSC {ME: MatrixElem} (m n: nat) (M: @CSC_Matrix ME m n) (b a i: nat) :=
  match b with 
  | 0 => MEzero
  | S b' => if (b =? a) then MEzero
            else if (nth_default 0 M.(JB) b <? i) then MEzero
            else if (nth_default 0 M.(JB) b =? i) then nth_default MEzero M.(B) b
            else get_v_CSC m n M b' a i 
  end. 

Definition Mget_CSC {ME: MatrixElem} (m n i j: nat) (M: @CSC_Matrix ME m n):= 
if andb (i <? m) (j <? n) then
  get_v_CSC m n M (nth_default 0 M.(IB) (j + 1)) (nth_default 0 M.(IB) j) i
else
  MEzero.

Fixpoint mul_CSR_CSC_row_col_eff_rec {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (x y : nat) (a b time: nat) := 
match time with 
| 0 => MEzero
| S time' => 
if b =? y then MEzero
else if a =? x then MEzero
else if ((nth_default 0 M1.(JA) a) <? (nth_default 0 M2.(JB) b)) then
        mul_CSR_CSC_row_col_eff_rec m n p M1 M2 x y a (b-1) time'
else if (nth_default 0 M2.(JB) b =? nth_default 0 M1.(JA) a) then
        nth_default MEzero M1.(A) a *e nth_default MEzero M2.(B) b +e mul_CSR_CSC_row_col_eff_rec m n p M1 M2 x y (a-1) (b-1) time'
else    mul_CSR_CSC_row_col_eff_rec m n p M1 M2 x y (a-1) b time'
 end. 


Definition mul_CSR_CSC_row_col_eff {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (i j: nat) := 
  mul_CSR_CSC_row_col_eff_rec m n p M1 M2 (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j) 
                                          (nth_default 0 M1.(IA) (i + 1)) (nth_default 0 M2.(IB) (j + 1))
                                          (nth_default 0 M1.(IA) (i + 1) + nth_default 0 M2.(IB) (j + 1)).  


Fixpoint mul_CSR_CSC_row_col_eff_rec_le {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (x y : nat) (a b time k: nat) := 
match time with 
| 0 => MEzero
| S time' => 
if b =? y then MEzero
else if a =? x then MEzero
else if ((nth_default 0 M1.(JA) a) <? (nth_default 0 M2.(JB) b)) then
        mul_CSR_CSC_row_col_eff_rec_le m n p M1 M2 x y a (b-1) time' k
else if (nth_default 0 M2.(JB) b =? nth_default 0 M1.(JA) a) then
  if (nth_default 0 M2.(JB) b <? k) then
        nth_default MEzero M1.(A) a *e nth_default MEzero M2.(B) b +e mul_CSR_CSC_row_col_eff_rec_le m n p M1 M2 x y (a-1) (b-1) time' k
  else
      mul_CSR_CSC_row_col_eff_rec_le m n p M1 M2 x y (a-1) (b-1) time' k
else    mul_CSR_CSC_row_col_eff_rec_le m n p M1 M2 x y (a-1) b time' k
 end. 


Definition mul_CSR_CSC_row_col_eff_le {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (i j k: nat) := 
  mul_CSR_CSC_row_col_eff_rec_le m n p M1 M2 (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j) 
                                          (nth_default 0 M1.(IA) (i + 1)) (nth_default 0 M2.(IB) (j + 1))
                                          (nth_default 0 M1.(IA) (i + 1) + nth_default 0 M2.(IB) (j + 1)) k.  


Fixpoint mul_CSR_CSC_row_col_eff_rec_eq {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (x y : nat) (a b time k: nat) := 
match time with 
| 0 => MEzero
| S time' => 
if b =? y then MEzero
else if a =? x then MEzero
else if ((nth_default 0 M1.(JA) a) <? (nth_default 0 M2.(JB) b)) then
        mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2 x y a (b-1) time' k
else if (nth_default 0 M2.(JB) b =? nth_default 0 M1.(JA) a) then
  if (nth_default 0 M2.(JB) b =? k) then
        nth_default MEzero M1.(A) a *e nth_default MEzero M2.(B) b +e mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2 x y (a-1) (b-1) time' k
  else
      mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2 x y (a-1) (b-1) time' k
else    mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2 x y (a-1) b time' k
 end. 

Definition mul_CSR_CSC_row_col_eff_eq {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (i j k: nat) := 
  mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2 (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j) 
                                          (nth_default 0 M1.(IA) (i + 1)) (nth_default 0 M2.(IB) (j + 1))
                                          (nth_default 0 M1.(IA) (i + 1) + nth_default 0 M2.(IB) (j + 1)) k.  




Lemma mul_CSR_CSC_row_col_eff_correct_base: 
    forall m n p M1 M2 i j, mul_CSR_CSC_row_col_eff_le m n p M1 M2 i j 0 = MEzero. 
Proof. 
  intros. 
  unfold mul_CSR_CSC_row_col_eff_le. 
  remember (nth_default 0 (IA M1) (i + 1) + nth_default 0 (IB M2) (j + 1)) as time. 
  clear Heqtime. 
  remember (nth_default 0 (IA M1) (i + 1)) as a. 
  remember (nth_default 0 (IB M2) (j + 1)) as b. 
  clear Heqa. clear Heqb. 
  generalize dependent b. 
  generalize dependent a. 
  induction time as [| time IHt]; intros. 
  - cbn. reflexivity. 
  - cbn. destruct (b =? nth_default 0 (IB M2) j); destruct (a =? nth_default 0 (IA M1) i); try destruct (match nth_default 0 (JB M2) b with
    | 0 => false
    | S m' => nth_default 0 (JA M1) a <=? m'
    end); try destruct ((nth_default 0 M2.(JB) b =? nth_default 0 M1.(JA) a)); try apply IHt; try reflexivity. 
Qed. 




Lemma mul_CSR_CSC_row_col_eff_correct_induct: 
    forall m n p M1 M2 i j k, 
    mul_CSR_CSC_row_col_eff_le m n p M1 M2 i j k +e mul_CSR_CSC_row_col_eff_eq m n p M1 M2 i j k
    = mul_CSR_CSC_row_col_eff_le m n p M1 M2 i j (S k). 
Proof. 
  intros. 
  unfold mul_CSR_CSC_row_col_eff_le. unfold mul_CSR_CSC_row_col_eff_eq. 
  remember (nth_default 0 (IA M1) (i + 1) + nth_default 0 (IB M2) (j + 1)) as time. 
  clear Heqtime. 
  remember (nth_default 0 (IA M1) (i + 1)) as a. 
  remember (nth_default 0 (IB M2) (j + 1)) as b. 
  clear Heqa. clear Heqb. 
  generalize dependent b. 
  generalize dependent a. 
  induction time as [| time IHt]; intros. 
  - cbn. ring. 
  - cbn.
    destruct (b =? nth_default 0 (IB M2) j); try ring. 
    destruct (a =? nth_default 0 (IA M1) i); try ring. 
    destruct (match nth_default 0 (JB M2) b with
  | 0 => false
  | S m' => nth_default 0 (JA M1) a <=? m'
  end); try apply IHt. 
    destruct (nth_default 0 (JB M2) b =? nth_default 0 (JA M1) a).
    + destruct (  match k with
    | 0 => false
    | S m' => nth_default 0 (JB M2) b <=? m'
    end) eqn : eq1. 
      * assert (nth_default 0 (JB M2) b < k). 
        { apply leb_iff. cbn. apply eq1. }
        assert (nth_default 0 (JB M2) b =? k = false). 
        { apply Nat.eqb_neq. omega. }
        assert (nth_default 0 (JB M2) b <=? k = true). 
        { apply leb_iff. omega. }
        rewrite H0. rewrite H1. 
        rewrite <- IHt. ring. 
      * assert (nth_default 0 (JB M2) b <? k = false). 
        { apply eq1. }
        apply Nat.ltb_nlt in H.
        clear eq1. 
        destruct (nth_default 0 (JB M2) b =? k) eqn: eq2. 
        --- apply Nat.eqb_eq in eq2. assert (nth_default 0 (JB M2) b <=? k = true). 
            { apply leb_iff. omega. }
            rewrite H0. rewrite <- IHt. ring. 
        --- apply Nat.eqb_neq in eq2. assert (nth_default 0 (JB M2) b <=? k = false). 
            { apply leb_iff_conv. omega. }
            rewrite H0. apply IHt. 
    + apply IHt.
Qed. 




Lemma mul_CSR_CSC_row_col_eff_rec_eq_caseb0: 
    forall m n p M1 M2 i j a  time k, 
    i < m -> j < p -> k < n -> a <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    ->  mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2
        (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j)
        (a + (nth_default 0 M1.(IA) i)) ((nth_default 0 M2.(IB) j)) time k
    = MEzero. 
Proof.
  intros.
  cbn. unfold mul_CSR_CSC_row_col_eff_rec_eq. 
  destruct time; try reflexivity. 
  destruct (nth_default 0 (IB M2) j); try reflexivity. 
  assert (S n0 =? S n0 = true). { apply Nat.eqb_eq. reflexivity. }
  rewrite H3. reflexivity.
Qed. 

Lemma mul_CSR_CSC_row_col_eff_rec_eq_casea0: 
    forall m n p M1 M2 i j b  time k, 
    i < m -> j < p -> k < n -> b <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    ->  mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2
        (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j)
        ((nth_default 0 M1.(IA) i)) (b + (nth_default 0 M2.(IB) j)) time k
    = MEzero. 
Proof.
  intros.
  cbn. unfold mul_CSR_CSC_row_col_eff_rec_eq. 
  destruct time; try reflexivity. 
  destruct (b + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j); try reflexivity. 
  assert (nth_default 0 (IA M1) i =? nth_default 0 (IA M1) i = true). 
  { apply Nat.eqb_eq. reflexivity. } rewrite H3. reflexivity. 
Qed. 

Lemma mul_CSR_CSC_row_col_eff_rec_eq_case0: 
    forall m n p M1 M2 i j a b time k, 
    i < m -> j < p -> k < n -> a <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    -> b <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    -> a = 0
        \/ b = 0 -> 
      mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2
        (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j)
        (a + (nth_default 0 M1.(IA) i)) (b + (nth_default 0 M2.(IB) j)) time k
    = MEzero. 
Proof. 
  intros. 
  unfold mul_CSR_CSC_row_col_eff_rec_eq. 
  destruct (time); try reflexivity.
  inversion H4. 
  - destruct (b + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j); try reflexivity. 
    assert (a + nth_default 0 (IA M1) i =? nth_default 0 (IA M1) i = true). 
    { apply Nat.eqb_eq. omega. }
    rewrite H6. reflexivity.
  - assert (b + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j = true). 
    { apply Nat.eqb_eq. omega. }
    rewrite H6. reflexivity.
Qed. 


Lemma mul_CSR_CSC_row_col_eff_rec_eq_case1: 
    forall m n p M1 M2 i j a b time k, 
    i < m -> j < p -> k < n -> a <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    -> b <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    -> nth_default 0 M1.(JA) (a + (nth_default 0 M1.(IA) i)) < k 
        \/ nth_default 0 M2.(JB) (b + (nth_default 0 M2.(IB) j)) < k -> 
      mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2
        (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j)
        (a + (nth_default 0 M1.(IA) i)) (b + (nth_default 0 M2.(IB) j)) time k
    = MEzero. 
Proof. 
  intros. 
  destruct b; try apply mul_CSR_CSC_row_col_eff_rec_eq_caseb0; try assumption.
  destruct a; try apply mul_CSR_CSC_row_col_eff_rec_eq_casea0; try assumption.
  generalize dependent time. 
  generalize dependent a. 
  induction b as [| b IHb]. 
  - induction a as [| a IHa]; intros. 
    + cbn. unfold mul_CSR_CSC_row_col_eff_rec_eq. 
      destruct time; try reflexivity. 
      destruct (S (nth_default 0 (IB M2) j) =? nth_default 0 (IB M2) j); try reflexivity. 
      destruct (S (nth_default 0 (IA M1) i) =? nth_default 0 (IA M1) i); try reflexivity. 
      destruct (nth_default 0 (JA M1) (S (nth_default 0 (IA M1) i)) <?
  nth_default 0 (JB M2) (S (nth_default 0 (IB M2) j))). Focus 1. 
      assert (S (nth_default 0 (IB M2) j) - 1 = nth_default 0 (IB M2) j). { omega. }
      rewrite H5. assert (S (nth_default 0 (IA M1) i) = 1 + nth_default 0 (IA M1) i). { omega. }
      rewrite H6. apply mul_CSR_CSC_row_col_eff_rec_eq_caseb0; try assumption. 
      
      destruct (nth_default 0 (JB M2) (S (nth_default 0 (IB M2) j)) =?
  nth_default 0 (JA M1) (S (nth_default 0 (IA M1) i))) eqn : eq. Focus 2. 
      assert (S (nth_default 0 (IA M1) i) - 1 = nth_default 0 (IA M1) i). { omega. }
      assert (S (nth_default 0 (IB M2) j) = 1 + nth_default 0 (IB M2) j). { omega. }
      rewrite H5. rewrite H6. apply mul_CSR_CSC_row_col_eff_rec_eq_casea0; try assumption. 
      
      assert (nth_default 0 (JB M2) (S (nth_default 0 (IB M2) j)) =? k = false). 
      { apply Nat.eqb_eq in eq. apply Nat.eqb_neq. 
        replace (1 + nth_default 0 (IA M1) i) with (S (nth_default 0 (IA M1) i)) in H4; try omega. 
        replace (1 + nth_default 0 (IB M2) j) with (S (nth_default 0 (IB M2) j)) in H4; try omega. 
      }
      rewrite H5. clear H5. 
      replace (S (nth_default 0 (IA M1) i) - 1) with (nth_default 0 (IA M1) i) by omega. 
      replace (S (nth_default 0 (IB M2) j) - 1) with (0 + nth_default 0 (IB M2) j) by omega. 
      apply mul_CSR_CSC_row_col_eff_rec_eq_casea0; try assumption. 
      assert (nth_default 0 (IB M2) j <= nth_default 0 (IB M2) (j + 1)). 
      { apply M2.(Content_IB_i). assumption. }
      omega. 
    + cbn. unfold mul_CSR_CSC_row_col_eff_rec_eq. 
      destruct time; try reflexivity. 
      destruct (S (nth_default 0 (IB M2) j) =? nth_default 0 (IB M2) j); try reflexivity. 
      destruct (S (S (a + nth_default 0 (IA M1) i)) =? nth_default 0 (IA M1) i); try reflexivity. 
      destruct (nth_default 0 (JA M1) (S (S (a + nth_default 0 (IA M1) i))) <?
  nth_default 0 (JB M2) (S (nth_default 0 (IB M2) j))). Focus 1. 
      assert (S (nth_default 0 (IB M2) j) - 1 = nth_default 0 (IB M2) j). { omega. }
      assert (S (S (a + nth_default 0 (IA M1) i)) = (a + 2) + nth_default 0 (IA M1) i). { omega. }
      rewrite H5. rewrite H6. apply mul_CSR_CSC_row_col_eff_rec_eq_caseb0; try assumption.
      omega. 

      destruct (nth_default 0 (JB M2) (S (nth_default 0 (IB M2) j)) =?
  nth_default 0 (JA M1) (S (S (a + nth_default 0 (IA M1) i)))) eqn : eq. Focus 2.
      assert (S (S (a + nth_default 0 (IA M1) i)) - 1 = S a + nth_default 0 (IA M1) i). { omega. }
      rewrite H5. apply IHa; try assumption; try omega. 
      inversion H4; try omega. 
      left. assert (nth_default 0 (JA M1) (S a + nth_default 0 (IA M1) i) < nth_default 0 (JA M1) (S (S a) + nth_default 0 (IA M1) i)). 
      { replace (S (S a) + nth_default 0 (IA M1) i) with ((S a + nth_default 0 (IA M1) i) + 1) by omega. 
        apply M1.(Content_JA) with (i := i); try assumption; try omega. } 
      omega. 
      
      assert (nth_default 0 (JB M2) (S (nth_default 0 (IB M2) j)) =? k = false). 
      { apply Nat.eqb_eq in eq. apply Nat.eqb_neq. 
        replace (S (S a) + nth_default 0 (IA M1) i) with (S (S (a + nth_default 0 (IA M1) i))) in H4; try omega. 
        replace (1 + nth_default 0 (IB M2) j) with (S (nth_default 0 (IB M2) j)) in H4; try omega. 
      }
      rewrite H5. clear H5. 
      replace (S (S (a + nth_default 0 (IA M1) i)) - 1) with ((a + 1) + nth_default 0 (IA M1) i) by omega. 
      replace (S (nth_default 0 (IB M2) j) - 1) with (nth_default 0 (IB M2) j) by omega. 
      apply mul_CSR_CSC_row_col_eff_rec_eq_caseb0; try assumption. 
      omega.
  - induction a as [| a IHa]; intros. 
    + cbn. unfold mul_CSR_CSC_row_col_eff_rec_eq. 
      destruct time; try reflexivity. 
      destruct (S (S (b + nth_default 0 (IB M2) j)) =? nth_default 0 (IB M2) j); try reflexivity. 
      destruct (S (nth_default 0 (IA M1) i) =? nth_default 0 (IA M1) i); try reflexivity. 
      destruct (nth_default 0 (JA M1) (S (nth_default 0 (IA M1) i)) <?
  nth_default 0 (JB M2) (S (S (b + nth_default 0 (IB M2) j)))). Focus 1. 
      assert (S (S (b + nth_default 0 (IB M2) j)) - 1 = S b + nth_default 0 (IB M2) j). { omega. }
      assert (S (nth_default 0 (IA M1) i) = 1 + nth_default 0 (IA M1) i). { omega. }
      rewrite H5. rewrite H6. apply IHb; try omega. 
      inversion H4; try omega. 
      right. assert (nth_default 0 (JB M2) (S b + nth_default 0 (IB M2) j) < nth_default 0 (JB M2) (S (S b) + nth_default 0 (IB M2) j)). 
      { replace (S (S b) + nth_default 0 (IB M2) j) with ((S b + nth_default 0 (IB M2) j) + 1) by omega. 
        apply M2.(Content_JB) with (i := j); try omega. }
      omega. 
      
      destruct (nth_default 0 (JB M2) (S (S (b + nth_default 0 (IB M2) j))) =?
  nth_default 0 (JA M1) (S (nth_default 0 (IA M1) i))) eqn : eq. Focus 2.
      replace (S (nth_default 0 (IA M1) i) - 1) with (nth_default 0 (IA M1) i) by omega. 
      replace (S (S (b + nth_default 0 (IB M2) j))) with ((b + 2) + nth_default 0 (IB M2) j) by omega. 
      apply mul_CSR_CSC_row_col_eff_rec_eq_casea0; try omega. 
      
      assert (nth_default 0 (JB M2) (S (S (b + nth_default 0 (IB M2) j))) =? k = false). 
      { apply Nat.eqb_eq in eq. apply Nat.eqb_neq.  
        replace (1 + nth_default 0 (IA M1) i) with (S (nth_default 0 (IA M1) i)) in H4; try omega. 
        replace (S (S b) + nth_default 0 (IB M2) j) with (S (S (b + nth_default 0 (IB M2) j))) in H4; try omega. 
      }
      rewrite H5. clear H5. 
      replace (S (nth_default 0 (IA M1) i) - 1) with (nth_default 0 (IA M1) i) by omega. 
      replace (S (S (b + nth_default 0 (IB M2) j)) - 1) with ((b + 1) + nth_default 0 (IB M2) j) by omega. 
      apply mul_CSR_CSC_row_col_eff_rec_eq_casea0; try omega. 
    + cbn. unfold mul_CSR_CSC_row_col_eff_rec_eq. 
      destruct time; try reflexivity. 
      destruct (S (S (b + nth_default 0 (IB M2) j)) =? nth_default 0 (IB M2) j); try reflexivity. 
      destruct (S (S (a + nth_default 0 (IA M1) i)) =? nth_default 0 (IA M1) i); try reflexivity. 
      destruct (nth_default 0 (JA M1) (S (S (a + nth_default 0 (IA M1) i))) <?
     nth_default 0 (JB M2) (S (S (b + nth_default 0 (IB M2) j)))). Focus 1. 
      replace (S (S (b + nth_default 0 (IB M2) j)) - 1) with (S b + nth_default 0 (IB M2) j) by omega. 
      replace (S (S (a + nth_default 0 (IA M1) i))) with ( S (S a) + nth_default 0 (IA M1) i) by omega. 
      apply IHb; try omega. 
      inversion H4; try omega. 
      right. assert (nth_default 0 (JB M2) (S b + nth_default 0 (IB M2) j) < nth_default 0 (JB M2) (S (S b) + nth_default 0 (IB M2) j)). 
      { replace (S (S b) + nth_default 0 (IB M2) j) with ((S b + nth_default 0 (IB M2) j) + 1) by omega. 
        apply M2.(Content_JB) with (i := j); try omega. }
      omega. 
      
      destruct (nth_default 0 (JB M2) (S (S (b + nth_default 0 (IB M2) j))) =?
  nth_default 0 (JA M1) (S (S (a + nth_default 0 (IA M1) i)))) eqn : eq. Focus 2.
      replace (S (S (a + nth_default 0 (IA M1) i)) - 1) with (S a + nth_default 0 (IA M1) i) by omega. 
      replace (S (S (b + nth_default 0 (IB M2) j))) with (S (S b) + nth_default 0 (IB M2) j) by omega. 
      apply IHa; try omega. 
      inversion H4; try omega. 
      left. assert (nth_default 0 (JA M1) (S a + nth_default 0 (IA M1) i) < nth_default 0 (JA M1) (S (S a) + nth_default 0 (IA M1) i)). 
      { replace (S (S a) + nth_default 0 (IA M1) i) with ((S a + nth_default 0 (IA M1) i) + 1) by omega. 
        apply M1.(Content_JA) with (i := i); try omega. }
      omega. 
      
      assert (nth_default 0 (JB M2) (S (S (b + nth_default 0 (IB M2) j))) =? k = false). 
      { apply Nat.eqb_eq in eq. apply Nat.eqb_neq.  
        replace (S (S a) + nth_default 0 (IA M1) i) with (S (S (a + nth_default 0 (IA M1) i))) in H4; try omega. 
        replace (S (S b) + nth_default 0 (IB M2) j) with (S (S (b + nth_default 0 (IB M2) j))) in H4; try omega. 
      }
      rewrite H5. clear H5. 
      replace (S (S (a + nth_default 0 (IA M1) i)) - 1) with (S a + nth_default 0 (IA M1) i) by omega. 
      replace (S (S (b + nth_default 0 (IB M2) j)) - 1) with (S b + nth_default 0 (IB M2) j) by omega. 
      apply IHb; try omega. inversion H4. 
      * left. assert (nth_default 0 (JA M1) (S a + nth_default 0 (IA M1) i) < nth_default 0 (JA M1) (S (S a) + nth_default 0 (IA M1) i)). 
      { replace (S (S a) + nth_default 0 (IA M1) i) with ((S a + nth_default 0 (IA M1) i) + 1) by omega. 
        apply M1.(Content_JA) with (i := i); try omega. }
      omega. 
      * right. assert (nth_default 0 (JB M2) (S b + nth_default 0 (IB M2) j) < nth_default 0 (JB M2) (S (S b) + nth_default 0 (IB M2) j)). 
      { replace (S (S b) + nth_default 0 (IB M2) j) with ((S b + nth_default 0 (IB M2) j) + 1) by omega. 
        apply M2.(Content_JB) with (i := j); try omega. }
      omega. 
Qed. 


Lemma Quick_get_CSR_correct: 
  forall m n i k M1 a, 
    i < m -> k < n -> 1 <= a
    -> a <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    -> nth_default 0 M1.(JA) (a + (nth_default 0 M1.(IA) i)) = k
    -> nth_default MEzero M1.(A) (a + (nth_default 0 M1.(IA) i)) = Mget_CSR m n i k M1. 
Proof. 
  intros. 
  assert (forall x, 
      x <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i) - a
      -> nth_default MEzero M1.(A) (a + (nth_default 0 M1.(IA) i)) 
        = get_v_CSR m n M1 (a + x + (nth_default 0 M1.(IA) i)) (nth_default 0 M1.(IA) i) k). 
  { 
    induction x0 as [| x IHx]. 
    - intros. 
      unfold get_v_CSR.
      cbn. destruct (a + 0 + nth_default 0 (IA M1) i) eqn : eq.
      + assert ( a + 0 + nth_default 0 (IA M1) i > 0). { omega. } rewrite eq in H5. inversion H5. 
      + assert (  match k with
  | 0 => false
  | S m' => nth_default 0 (JA M1) (S n0) <=? m'
  end = false). { destruct k; try reflexivity. apply leb_iff_conv. 
                  rewrite <- eq. replace (a + 0 + nth_default 0 (IA M1) i) with (a + nth_default 0 (IA M1) i) by omega. 
                  omega. }
        rewrite H5. 
        assert (nth_default 0 (JA M1) (S n0) = k). 
        { rewrite <- eq. replace (a + 0 + nth_default 0 (IA M1) i) with (a + nth_default 0 (IA M1) i) by omega.
          assumption. }
        rewrite H6. assert (k =? k = true). { apply Nat.eqb_eq. reflexivity. }
        rewrite H7. clear H7. clear H6. rewrite <- eq. 
        replace (a + 0 + nth_default 0 (IA M1) i) with (a + nth_default 0 (IA M1) i) by omega. 
        assert (a + nth_default 0 (IA M1) i =? nth_default 0 (IA M1) i = false). 
        { apply Nat.eqb_neq. omega. }
        rewrite H6. reflexivity. 
    - intros. 
      unfold get_v_CSR. 
      destruct (a + S x + nth_default 0 (IA M1) i) eqn: eq. 
      + assert (a + S x + nth_default 0 (IA M1) i > 0). { omega. }
        rewrite eq in H5. inversion H5. 
      + assert (nth_default 0 (JA M1) (S n0) > k). 
        { rewrite <- eq. rewrite <- H3. 
          apply M1.(Content_JA) with (i:=i); try omega. }
        assert (nth_default 0 (JA M1) (S n0) <? k = false). 
        { apply Nat.ltb_nlt. omega. }
        rewrite H6. 
        assert (nth_default 0 (JA M1) (S n0) =? k = false). 
        { apply Nat.eqb_neq. omega. }
        rewrite H7. 
        assert (S n0 =? nth_default 0 (IA M1) i = false). 
        { apply Nat.eqb_neq. omega. }
        rewrite H8. assert (n0 = a + x + nth_default 0 (IA M1) i). { omega. }
        rewrite H9. apply IHx. omega. }
  unfold Mget_CSR. 
  replace (andb (i <? m)  (k <? n)) with true. 
  - replace (nth_default 0 (IA M1) (i + 1)) with (a + ((nth_default 0 (IA M1) (i + 1) - (nth_default 0 (IA M1) (i)) - a)) + nth_default 0 (IA M1) i) by omega.
    apply H4. omega. 
  - symmetry. apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. 
Qed. 



Lemma Quick_get_CSC_correct: 
  forall n p j k M2 b, 
    j < p -> k < n -> 1 <= b
    -> b <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    -> nth_default 0 M2.(JB) (b + (nth_default 0 M2.(IB) j)) = k
    -> nth_default MEzero M2.(B) (b + (nth_default 0 M2.(IB) j)) = Mget_CSC n p k j M2. 
Proof. 
  intros. 
  assert (forall x, 
      x <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j) - b
      -> nth_default MEzero M2.(B) (b + (nth_default 0 M2.(IB) j)) 
        = get_v_CSC n p M2 (b + x + (nth_default 0 M2.(IB) j)) (nth_default 0 M2.(IB) j) k). 
  { 
    induction x0 as [| x IHx]. 
    - intros. 
      unfold get_v_CSC.
      cbn. destruct (b + 0 + nth_default 0 (IB M2) j) eqn : eq.
      + assert ( b + 0 + nth_default 0 (IB M2) j > 0). { omega. } rewrite eq in H5. inversion H5. 
      + assert (  match k with
  | 0 => false
  | S m' => nth_default 0 (JB M2) (S n0) <=? m'
  end = false). { destruct k; try reflexivity. apply leb_iff_conv. 
                  rewrite <- eq. replace (b + 0 + nth_default 0 (IB M2) j) with (b + nth_default 0 (IB M2) j) by omega. 
                  omega. }
        rewrite H5. 
        assert (nth_default 0 (JB M2) (S n0) = k). 
        { rewrite <- eq. replace (b + 0 + nth_default 0 (IB M2) j) with (b + nth_default 0 (IB M2) j) by omega.
          assumption. }
        rewrite H6. assert (k =? k = true). { apply Nat.eqb_eq. reflexivity. }
        rewrite H7. clear H7. clear H6. rewrite <- eq. 
        replace (b + 0 + nth_default 0 (IB M2) j) with (b + nth_default 0 (IB M2) j) by omega. 
        assert (b + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j = false). 
        { apply Nat.eqb_neq. omega. }
        rewrite H6. reflexivity. 
    - intros. 
      unfold get_v_CSC. 
      destruct (b + S x + nth_default 0 (IB M2) j) eqn: eq. 
      + assert (b + S x + nth_default 0 (IB M2) j > 0). { omega. }
        rewrite eq in H5. inversion H5. 
      + assert (nth_default 0 (JB M2) (S n0) > k). 
        { rewrite <- eq. rewrite <- H3. 
          apply M2.(Content_JB) with (i:=j); try omega. }
        assert (nth_default 0 (JB M2) (S n0) <? k = false). 
        { apply Nat.ltb_nlt. omega. }
        rewrite H6. 
        assert (nth_default 0 (JB M2) (S n0) =? k = false). 
        { apply Nat.eqb_neq. omega. }
        rewrite H7. 
        assert (S n0 =? nth_default 0 (IB M2) j = false). 
        { apply Nat.eqb_neq. omega. }
        rewrite H8. assert (n0 = b + x + nth_default 0 (IB M2) j). { omega. }
        rewrite H9. apply IHx. omega. }
  unfold Mget_CSC. 
  replace (andb (k <? n)  (j <? p)) with true. 
  - replace (nth_default 0 (IB M2) (j + 1)) with (b + ((nth_default 0 (IB M2) (j + 1) - (nth_default 0 (IB M2) (j)) - b)) + nth_default 0 (IB M2) j) by omega.
    apply H4. omega. 
  - symmetry. apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. 
Qed. 



Lemma Quick_get_CSR_zero_condition0: 
  forall m n i k M1 a, 
    i < m -> k < n -> a = 0
    -> a < (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    -> nth_default 0 M1.(JA) ((a + 1) + (nth_default 0 M1.(IA) i)) > k
    -> MEzero = Mget_CSR m n i k M1. 
Proof. 
  intros. 
  assert (forall x, 
    x <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i) - a
    -> MEzero
      = get_v_CSR m n M1 (a + x + (nth_default 0 M1.(IA) i)) (nth_default 0 M1.(IA) i) k).
  {
    induction x0 as [| x IHx]. 
    - intros. unfold get_v_CSR. cbn. 
      destruct (a + 0 + nth_default 0 (IA M1) i) eqn : eq; try reflexivity.  
      assert (S n0 =? nth_default 0 (IA M1) i = true). 
      { apply Nat.eqb_eq. omega. }
      rewrite H5. reflexivity. 
    - intros. unfold get_v_CSR. 
      destruct (a + S x + nth_default 0 (IA M1) i) eqn : eq; try reflexivity. 
      destruct (S n0 =? nth_default 0 (IA M1) i); try reflexivity. 
      assert (nth_default 0 (JA M1) (S n0) > k). 
      { 
        assert (nth_default 0 (JA M1) (S n0) >= nth_default 0 (JA M1) (a + 1 + nth_default 0 (IA M1) i)). 
        { 
          rewrite <- eq. 
          destruct (a + S x + nth_default 0 (IA M1) i =? a + 1 + nth_default 0 (IA M1) i) eqn: eq2. 
          + apply Nat.eqb_eq in eq2. rewrite eq2. omega. 
          + apply beq_nat_false in eq2. apply Nat.lt_le_incl. apply M1.(Content_JA) with ( i:= i); try omega. }
        omega. }
      destruct (nth_default 0 (JA M1) (S n0) <? k); try reflexivity. 
      assert (nth_default 0 (JA M1) (S n0) =? k = false). 
      { apply Nat.eqb_neq. omega. }
      rewrite H6. replace n0 with (a + x + nth_default 0 (IA M1) i) by omega. 
      apply IHx; omega. 
    }
    unfold Mget_CSR. 
    replace (andb (i <? m)  (k <? n)) with true. 
    - replace (nth_default 0 (IA M1) (i + 1)) with (a + ((nth_default 0 (IA M1) (i + 1) - (nth_default 0 (IA M1) (i)) - a)) + nth_default 0 (IA M1) i) by omega.
    apply H4. omega. 
  - symmetry. apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. 
Qed. 


Lemma Quick_get_CSC_zero_condition0: 
  forall n p j k M2 b, 
    j < p -> k < n -> b = 0
    -> b < (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    -> nth_default 0 M2.(JB) ((b + 1) + (nth_default 0 M2.(IB) j)) > k
    -> MEzero = Mget_CSC n p k j M2. 
Proof. 
  intros.
  assert (forall x, 
    x <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j) - b
    -> MEzero
      = get_v_CSC n p M2 (b + x + (nth_default 0 M2.(IB) j)) (nth_default 0 M2.(IB) j) k).
  {
    induction x0 as [| x IHx]. 
    - intros. unfold get_v_CSC. cbn. 
      destruct (b + 0 + nth_default 0 (IB M2) j) eqn : eq; try reflexivity.  
      assert (S n0 =? nth_default 0 (IB M2) j = true). 
      { apply Nat.eqb_eq. omega. }
      rewrite H5. reflexivity. 
    - intros. unfold get_v_CSC. 
      destruct (b + S x + nth_default 0 (IB M2) j) eqn : eq; try reflexivity. 
      destruct (S n0 =? nth_default 0 (IB M2) j); try reflexivity. 
      assert (nth_default 0 (JB M2) (S n0) > k). 
      { 
        assert (nth_default 0 (JB M2) (S n0) >= nth_default 0 (JB M2) (b + 1 + nth_default 0 (IB M2) j)). 
        { 
          rewrite <- eq. 
          destruct (b + S x + nth_default 0 (IB M2) j =? b + 1 + nth_default 0 (IB M2) j) eqn: eq2. 
          + apply Nat.eqb_eq in eq2. rewrite eq2. omega. 
          + apply beq_nat_false in eq2. apply Nat.lt_le_incl. apply M2.(Content_JB) with ( i:= j); try omega. }
        omega. }
      destruct (nth_default 0 (JB M2) (S n0) <? k); try reflexivity. 
      assert (nth_default 0 (JB M2) (S n0) =? k = false). 
      { apply Nat.eqb_neq. omega. }
      rewrite H6. replace n0 with (b + x + nth_default 0 (IB M2) j) by omega. 
      apply IHx; omega. 
    }
    unfold Mget_CSC. 
    replace (andb (k <? n)  (j <? p)) with true. 
    - replace (nth_default 0 (IB M2) (j + 1)) with (b + ((nth_default 0 (IB M2) (j + 1) - (nth_default 0 (IB M2) (j)) - b)) + nth_default 0 (IB M2) j) by omega.
    apply H4. omega. 
  - symmetry. apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. 
Qed. 


Lemma Quick_get_CSR_zero_condition1: 
  forall m n i k M1 a, 
    i < m -> k < n -> 1 <= a
    -> a < (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    -> nth_default 0 M1.(JA) ((a + 1) + (nth_default 0 M1.(IA) i)) > k
    -> nth_default 0 M1.(JA) (a + (nth_default 0 M1.(IA) i)) < k
    -> MEzero = Mget_CSR m n i k M1. 
Proof. 
  intros.
  assert (forall x, 
    x <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i) - a
    -> MEzero
      = get_v_CSR m n M1 (a + x + (nth_default 0 M1.(IA) i)) (nth_default 0 M1.(IA) i) k).
  {
    induction x0 as [| x IHx]. 
    - intros. unfold get_v_CSR. cbn. 
      destruct (a + 0 + nth_default 0 (IA M1) i) eqn : eq; try reflexivity.  
      destruct (S n0 =? nth_default 0 (IA M1) i); try reflexivity. 
      assert (  match k with
  | 0 => false
  | S m' => nth_default 0 (JA M1) (S n0) <=? m'
  end = true). 
      { destruct k; try omega. apply leb_iff. rewrite <- eq. 
        replace (a + 0 + nth_default 0 (IA M1) i) with (a + nth_default 0 (IA M1) i) by omega. 
        omega. }
      rewrite H6. reflexivity. 
    - intros. unfold get_v_CSR. 
      destruct (a + S x + nth_default 0 (IA M1) i) eqn : eq; try reflexivity. 
      destruct (S n0 =? nth_default 0 (IA M1) i); try reflexivity. 
      assert (nth_default 0 (JA M1) (S n0) > k). 
      { 
        assert (nth_default 0 (JA M1) (S n0) >= nth_default 0 (JA M1) (a + 1 + nth_default 0 (IA M1) i)). 
        { 
          rewrite <- eq. 
          destruct (a + S x + nth_default 0 (IA M1) i =? a + 1 + nth_default 0 (IA M1) i) eqn: eq2. 
          + apply Nat.eqb_eq in eq2. rewrite eq2. omega. 
          + apply beq_nat_false in eq2. apply Nat.lt_le_incl. apply M1.(Content_JA) with ( i:= i); try omega. }
        omega. }
      destruct (nth_default 0 (JA M1) (S n0) <? k); try reflexivity. 
      assert (nth_default 0 (JA M1) (S n0) =? k = false). 
      { apply Nat.eqb_neq. omega. }
      rewrite H7. replace n0 with (a + x + nth_default 0 (IA M1) i) by omega. 
      apply IHx; omega. 
    }
    unfold Mget_CSR. 
    replace (andb (i <? m)  (k <? n)) with true. 
    - replace (nth_default 0 (IA M1) (i + 1)) with (a + ((nth_default 0 (IA M1) (i + 1) - (nth_default 0 (IA M1) (i)) - a)) + nth_default 0 (IA M1) i) by omega.
    apply H5. omega. 
  - symmetry. apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. 
Qed. 




Lemma Quick_get_CSC_zero_condition1: 
  forall n p j k M2 b, 
    j < p -> k < n -> 1 <= b
    -> b < (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    -> nth_default 0 M2.(JB) ((b + 1) + (nth_default 0 M2.(IB) j)) > k
    -> nth_default 0 M2.(JB) (b + (nth_default 0 M2.(IB) j)) < k
    -> MEzero = Mget_CSC n p k j M2. 
Proof. 
  intros.
  assert (forall x, 
    x <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j) - b
    -> MEzero
      = get_v_CSC n p M2 (b + x + (nth_default 0 M2.(IB) j)) (nth_default 0 M2.(IB) j) k).
  {
    induction x0 as [| x IHx]. 
    - intros. unfold get_v_CSC. cbn. 
      destruct (b + 0 + nth_default 0 (IB M2) j) eqn : eq; try reflexivity.  
      destruct (S n0 =? nth_default 0 (IB M2) j); try reflexivity. 
      assert (  match k with
  | 0 => false
  | S m' => nth_default 0 (JB M2) (S n0) <=? m'
  end = true). 
      { destruct k; try omega. apply leb_iff. rewrite <- eq. 
        replace (b + 0 + nth_default 0 (IB M2) j) with (b + nth_default 0 (IB M2) j) by omega. 
        omega. }
      rewrite H6. reflexivity. 
    - intros. unfold get_v_CSC. 
      destruct (b + S x + nth_default 0 (IB M2) j) eqn : eq; try reflexivity. 
      destruct (S n0 =? nth_default 0 (IB M2) j); try reflexivity. 
      assert (nth_default 0 (JB M2) (S n0) > k). 
      { 
        assert (nth_default 0 (JB M2) (S n0) >= nth_default 0 (JB M2) (b + 1 + nth_default 0 (IB M2) j)). 
        { 
          rewrite <- eq. 
          destruct (b + S x + nth_default 0 (IB M2) j =? b + 1 + nth_default 0 (IB M2) j) eqn: eq2. 
          + apply Nat.eqb_eq in eq2. rewrite eq2. omega. 
          + apply beq_nat_false in eq2. apply Nat.lt_le_incl. apply M2.(Content_JB) with ( i:= j); try omega. }
        omega. }
      destruct (nth_default 0 (JB M2) (S n0) <? k); try reflexivity. 
      assert (nth_default 0 (JB M2) (S n0) =? k = false). 
      { apply Nat.eqb_neq. omega. }
      rewrite H7. replace n0 with (b + x + nth_default 0 (IB M2) j) by omega. 
      apply IHx; omega. 
    }
    unfold Mget_CSC. 
    replace (andb (k <? n)  (j <? p)) with true. 
    - replace (nth_default 0 (IB M2) (j + 1)) with (b + ((nth_default 0 (IB M2) (j + 1) - (nth_default 0 (IB M2) (j)) - b)) + nth_default 0 (IB M2) j) by omega.
    apply H5. omega. 
  - symmetry. apply Bool.andb_true_iff. split; apply Nat.ltb_lt; omega. 
Qed. 



Ltac urgh :=
   repeat match goal with
        | [ H: _ =? _ = true |- _ ] => rewrite Nat.eqb_eq in H
        | [ |- _ =? _ = true ] => rewrite Nat.eqb_eq
        | [ H: _ <? _ = true |- _ ] => apply Nat.ltb_lt in H
        | [ |- _ <? _ = true] => apply Nat.ltb_lt
        | [ H: _ <? _ = false |- _ ] => apply Nat.ltb_nlt in H
        | [ |- _ <? _ = false] => apply Nat.ltb_nlt
        | [ H: _ <=? _ = false |- _ ] => apply leb_iff_conv in H
        | [ |- _ <=? _ = false] => apply leb_iff_conv
        | [ H: _ <=? _ = true |- _ ] => apply leb_iff in H
        | [ |- _ <=? _ = true] => apply leb_iff
        | [ H: _ =? _ = false |- _ ] => apply Nat.eqb_neq in H
        | [ |- _ =? _ = false] => apply Nat.eqb_neq
        end.

Lemma mul_CSR_CSC_row_col_eff_rec_eq_case2: 
    forall m n p M1 M2 i j a b time k, 
    i < m -> j < p -> k < n -> 1 <= a -> a <= (nth_default 0 M1.(IA) (i + 1)) - (nth_default 0 M1.(IA) i)
    -> 1 <= b -> b <= (nth_default 0 M2.(IB) (j + 1)) - (nth_default 0 M2.(IB) j)
    -> a + b <= time -> nth_default 0 M1.(JA) (a + (nth_default 0 M1.(IA) i)) >= k 
        /\ nth_default 0 M2.(JB) (b + (nth_default 0 M2.(IB) j)) >= k -> 
      mul_CSR_CSC_row_col_eff_rec_eq m n p M1 M2
        (nth_default 0 M1.(IA) i) (nth_default 0 M2.(IB) j)
        (a + (nth_default 0 M1.(IA) i)) (b + (nth_default 0 M2.(IB) j)) time k
    = (Mget_CSR m n i k M1) *e (Mget_CSC n p k j M2).
Proof. 
  intros. 
  generalize dependent a. 
  generalize dependent b. 
  induction time as [| time IHtime].
  - intros. omega. 
  - intros. 
    unfold mul_CSR_CSC_row_col_eff_rec_eq. 
    assert (b + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j = false).
    { 
      apply Nat.eqb_neq. omega. 
    }
    rewrite H8. clear H8. 
    assert (a + nth_default 0 (IA M1) i =? nth_default 0 (IA M1) i = false).
    { 
      apply Nat.eqb_neq. omega. 
    }
    rewrite H8. clear H8. 
    destruct (nth_default 0 (JA M1) (a + nth_default 0 (IA M1) i) <?
   nth_default 0 (JB M2) (b + nth_default 0 (IB M2) j)) eqn: eq. Focus 1. 

    destruct (b - 1 =? 0) eqn: eq1. 
    + urgh. 
      replace (b + nth_default 0 (IB M2) j - 1) with (0 + nth_default 0 (IB M2) j) by omega. 
      rewrite <- Quick_get_CSC_zero_condition0 with (b := 0); urgh; try replace (0 + 1) with b by omega; try omega.  
      destruct time; try ring. 
      assert (0 + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j = true) by (urgh; omega). 
      rewrite H8. ring. 
    + destruct (k <=? nth_default 0 (JB M2) ((b - 1) + nth_default 0 (IB M2) j)) eqn: eq2.
      --- replace (b + nth_default 0 (IB M2) j - 1) with ((b-1) + nth_default 0 (IB M2) j) by omega.
          urgh. rewrite IHtime; try omega; try ring. 
      --- urgh.  rewrite <- Quick_get_CSC_zero_condition1 with (b := (b-1)); try replace (b - 1 + 1) with b by omega; try omega.
          replace (b + nth_default 0 (IB M2) j - 1) with ((b-1) + nth_default 0 (IB M2) j) by omega.
            rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega; try ring. 
     
    + urgh. 
      destruct (nth_default 0 (JB M2) (b + nth_default 0 (IB M2) j) =?
  nth_default 0 (JA M1) (a + nth_default 0 (IA M1) i)) eqn: eq2. Focus 2.
      
      urgh. destruct (a - 1 =? 0) eqn: eq3.
      * urgh. replace (a + nth_default 0 (IA M1) i - 1) with (0 + nth_default 0 (IA M1) i) by omega. 
        rewrite <- Quick_get_CSR_zero_condition0 with (a := 0); urgh; try replace (0 + 1) with a by omega; try omega.  
        destruct time; try ring. 
        destruct (b + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j); try ring. 
        assert (0 + nth_default 0 (IA M1) i =? nth_default 0 (IA M1) i = true) by (urgh; omega).
        rewrite H8. ring. Focus 2. 
      * destruct (k <=? nth_default 0 (JA M1) ((a - 1) + nth_default 0 (IA M1) i)) eqn: eq1.
      --- replace (a + nth_default 0 (IA M1) i - 1) with ((a-1) + nth_default 0 (IA M1) i) by omega.
          urgh. rewrite IHtime; try omega; try ring. Focus 2. 
      --- urgh.  rewrite <- Quick_get_CSR_zero_condition1 with (a := (a-1)); try replace (a - 1 + 1) with a by omega; try omega.
          replace (a + nth_default 0 (IA M1) i - 1) with ((a-1) + nth_default 0 (IA M1) i) by omega.
            rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega; try ring.
    
    urgh. destruct (nth_default 0 (JB M2) (b + nth_default 0 (IB M2) j) =? k) eqn: eq1. 
    * urgh. rewrite Quick_get_CSR_correct with (k := k); try omega.
      urgh. rewrite Quick_get_CSC_correct with (k := k); try omega.
      replace (a + nth_default 0 (IA M1) i - 1) with ((a - 1) + nth_default 0 (IA M1) i) by omega.
      replace (b + nth_default 0 (IB M2) j - 1) with ((b - 1) + nth_default 0 (IB M2) j) by omega.
      destruct (a - 1 =? 0) eqn: eq3; urgh. 
      --- replace (a - 1) with 0 by omega. rewrite mul_CSR_CSC_row_col_eff_rec_eq_casea0; try omega; try ring. 
      --- rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega; try ring. 
          left. 
          assert (nth_default 0 (JA M1) (a - 1 + nth_default 0 (IA M1) i) < nth_default 0 (JA M1) (a + nth_default 0 (IA M1) i)). 
          { apply M1.(Content_JA) with (i:=i); try omega. }
          omega. 
    * replace (a + nth_default 0 (IA M1) i - 1) with ((a - 1) + nth_default 0 (IA M1) i) by omega.
      replace (b + nth_default 0 (IB M2) j - 1) with ((b - 1) + nth_default 0 (IB M2) j) by omega.
      urgh. destruct (b - 1 =? 0) eqn: eq3. 
      --- urgh. 
          rewrite <- Quick_get_CSC_zero_condition0 with (b := 0); urgh; try replace (0 + 1) with b by omega; try omega.  
          destruct time; try ring. 
          assert (b - 1 + nth_default 0 (IB M2) j =? nth_default 0 (IB M2) j = true) by (urgh; omega). 
          rewrite H8. ring.
      
      --- destruct (k <=? nth_default 0 (JB M2) ((b - 1) + nth_default 0 (IB M2) j)) eqn: eq4. Focus 2. 
      
      urgh. rewrite <- Quick_get_CSC_zero_condition1 with (b := (b-1)); try replace (b - 1 + 1) with b by omega; try omega.
      rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega; try ring.


      urgh. destruct (a - 1 =? 0) eqn: eq5. Focus 1. 
      
      urgh. 
      rewrite <- Quick_get_CSR_zero_condition0 with (a := 0); urgh; try replace (0 + 1) with a by omega; try omega.  
      replace (a - 1) with 0 by omega. rewrite mul_CSR_CSC_row_col_eff_rec_eq_casea0; try omega. ring. 
      
      urgh. 
      destruct (k <=? nth_default 0 (JA M1) ((a - 1) + nth_default 0 (IA M1) i)) eqn: eq6. Focus 2.
      urgh. 
      rewrite <- Quick_get_CSR_zero_condition1 with (a := (a-1)); try replace (a - 1 + 1) with a by omega; try omega.
      rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega; try ring.
      
      urgh. rewrite IHtime; try omega. ring. 
Qed. 


Theorem mul_CSR_CSC_row_col_eff_eq_correct:
forall m n p M1 M2 i j k, 
i < m -> j < p -> k < n -> 
 mul_CSR_CSC_row_col_eff_eq m n p M1 M2 i j k = (Mget_CSR m n i k M1) *e (Mget_CSC n p k j M2).
Proof. 
  intros. unfold mul_CSR_CSC_row_col_eff_eq. 
  assert (nth_default 0 (IA M1) i <= nth_default 0 (IA M1) (i + 1)). 
  { apply M1.(Content_IA_i). omega. } 
  replace (nth_default 0 (IA M1) (i + 1)) with ((nth_default 0 (IA M1) (i + 1) - nth_default 0 (IA M1) (i)) + nth_default 0 (IA M1) i) by omega.
  
  assert (nth_default 0 (IB M2) j <= nth_default 0 (IB M2) (j + 1)). 
  { apply M2.(Content_IB_i). omega. } 
  replace (nth_default 0 (IB M2) (j + 1)) with ((nth_default 0 (IB M2) (j + 1) - nth_default 0 (IB M2) (j)) + nth_default 0 (IB M2) j) by omega.

  
  destruct (nth_default 0 (IA M1) (i + 1) - nth_default 0 (IA M1) i =? 0) eqn: eq1. Focus 1. 
  urgh. rewrite eq1. rewrite mul_CSR_CSC_row_col_eff_rec_eq_casea0; try omega. 
  unfold Mget_CSR. assert (andb (i <? m) (k <? n) = true). 
  { apply Bool.andb_true_iff. split; urgh; omega. }
  rewrite H4. unfold get_v_CSR. 
  destruct (nth_default 0 (IA M1) (i + 1)); try ring. 
  assert (S n0 =? nth_default 0 (IA M1) i = true). 
  { urgh. omega. }
  rewrite H5. ring. 
  
  destruct (nth_default 0 (IB M2) (j + 1) - nth_default 0 (IB M2) j =? 0) eqn: eq2. Focus 1. 
  urgh. rewrite eq2. rewrite mul_CSR_CSC_row_col_eff_rec_eq_caseb0; try omega. 
  unfold Mget_CSC. assert (andb (k <? n) (j <? p) = true). 
  { apply Bool.andb_true_iff. split; urgh; omega. }
  rewrite H4. unfold get_v_CSC. 
  destruct (nth_default 0 (IB M2) (j + 1)); try ring. 
  assert (S n0 =? nth_default 0 (IB M2) j = true). 
  { urgh. omega. }
  rewrite H5. ring. 
  
  remember (nth_default 0 (IA M1) (i + 1) - nth_default 0 (IA M1) i) as a. 
  remember (nth_default 0 (IB M2) (j + 1) - nth_default 0 (IB M2) j) as b. 
  
  urgh. 
  destruct (nth_default 0 (JA M1) (a + nth_default 0 (IA M1) i) <? k) eqn: eq3. Focus 1. 
  urgh. rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega. 
  unfold Mget_CSR. assert (andb (i <? m) (k <? n) = true). 
  { apply Bool.andb_true_iff. split; urgh; omega. }
  rewrite H4. unfold get_v_CSR. 
  destruct (nth_default 0 (IA M1) (i + 1)); try ring. 
  destruct (S n0 =? nth_default 0 (IA M1) i); try ring. 
  assert (nth_default 0 (JA M1) (S n0) <? k = true). 
  { urgh. replace (S n0) with (a + nth_default 0 (IA M1) i) by omega. apply eq3. }
  rewrite H5. ring. 
  
  urgh. 
  destruct (nth_default 0 (JB M2) (b + nth_default 0 (IB M2) j) <? k) eqn: eq4. Focus 1. 
  urgh. rewrite mul_CSR_CSC_row_col_eff_rec_eq_case1; try omega. 
  unfold Mget_CSC. assert (andb (k <? n) (j <? p) = true). 
  { apply Bool.andb_true_iff. split; urgh; omega. }
  rewrite H4. unfold get_v_CSC. 
  destruct (nth_default 0 (IB M2) (j + 1)); try ring. 
  destruct (S n0 =? nth_default 0 (IB M2) j); try ring. 
  assert (nth_default 0 (JB M2) (S n0) <? k = true). 
  { urgh. replace (S n0) with (b + nth_default 0 (IB M2) j) by omega. apply eq4. }
  rewrite H5. ring.
  
  
  rewrite mul_CSR_CSC_row_col_eff_rec_eq_case2; try omega; try ring. 
  split; try urgh; try omega. 
Qed. 



Theorem mul_CSR_CSC_row_col_eff_le_correct:
forall m n p M1 M2 i j k, 
i < m -> j < p -> k <= n -> 
 mul_CSR_CSC_row_col_eff_le m n p M1 M2 i j k = sum k (fun k => (Mget_CSR m n i k M1) *e (Mget_CSC n p k j M2)).
Proof. 
  intros. 
  induction k as [| k IHk].
  - cbn. apply mul_CSR_CSC_row_col_eff_correct_base. 
  - cbn. rewrite <- IHk; try omega. 
    rewrite <- mul_CSR_CSC_row_col_eff_correct_induct. 
    rewrite mul_CSR_CSC_row_col_eff_eq_correct; try omega. reflexivity. 
Qed. 


Lemma mul_CSR_CSC_row_col_eff_rec_le_equal:
forall m n p M1 M2 x y a b time, 
 mul_CSR_CSC_row_col_eff_rec_le m n p M1 M2 x y a b time n = mul_CSR_CSC_row_col_eff_rec m n p M1 M2 x y a b time.
Proof. 
  intros. 
  generalize dependent a. 
  generalize dependent b. 
  induction time as [| time IHtime]; intros. 
  - cbn. reflexivity. 
  - simpl. destruct (b =? y0); try reflexivity. 
    destruct (a =? x0); try reflexivity. 
    destruct (nth_default 0 (JA M1) a <? nth_default 0 (JB M2) b); try apply IHtime.
    destruct (nth_default 0 (JB M2) b =? nth_default 0 (JA M1) a); try apply IHtime. 
    assert (nth_default 0 (JB M2) b <? n = true). 
    { urgh. apply M2.(Content_JB_i). }
    rewrite H. rewrite IHtime. reflexivity. 
Qed. 

Theorem mul_CSR_CSC_row_col_eff_correct: 
forall m n p M1 M2 i j, 
i < m -> j < p -> 
 mul_CSR_CSC_row_col_eff m n p M1 M2 i j = sum n (fun k => (Mget_CSR m n i k M1) *e (Mget_CSC n p k j M2)).
Proof. 
  intros. 
  assert (mul_CSR_CSC_row_col_eff m n p M1 M2 i j = mul_CSR_CSC_row_col_eff_le m n p M1 M2 i j n). 
  { unfold mul_CSR_CSC_row_col_eff. unfold mul_CSR_CSC_row_col_eff_le. rewrite mul_CSR_CSC_row_col_eff_rec_le_equal. reflexivity. }
  rewrite H1. apply mul_CSR_CSC_row_col_eff_le_correct; omega. 
Qed. 




Definition mul_CSR_CSC_row_col {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (i j: nat) := 
  mul_CSR_CSC_row_col_eff m n p M1 M2 i j. 

Fixpoint mul_CSR_CSC_row {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (i j: nat) := 
match j with
| 0 => nil
| S j' => mul_CSR_CSC_row_col m n p M1 M2 i (p - j) :: mul_CSR_CSC_row m n p M1 M2 i j'
end. 

Fixpoint mul_CSR_CSC_to_dense_ {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) (i : nat) := 
match i with
| 0 => nil
| S i' => mul_CSR_CSC_row m n p M1 M2 (m - i) p:: mul_CSR_CSC_to_dense_ m n p M1 M2 i'
end. 

Definition mul_CSR_CSC_to_dense {ME: MatrixElem} (m n p: nat) (M1: @CSR_Matrix ME m n)
                              (M2: @CSC_Matrix ME n p) := 
  mul_CSR_CSC_to_dense_ m n p M1 M2 m.




Lemma mul_CSR_CSC_correct_row: forall m n p M1 M2 k i,
  k <= m -> i < k -> nth_default nil (mul_CSR_CSC_to_dense_ m n p M1 M2 k) i
   = mul_CSR_CSC_row m n p M1 M2 (m - k + i) p. 
Proof. 
  intros. 
  generalize dependent i. 
  induction k as [| k IHk]; intros. 
  - inversion H0. 
  - destruct i. 
    + cbn. rewrite <- plus_n_O. reflexivity. 
    + assert (m - S k + S i = m - k + i). { omega. } rewrite H1. 
      apply IHk; try omega. 
Qed. 

Lemma mul_CSR_CSC_correct_entry: forall m n p M1 M2 i k j,
  i < m -> k <= p -> j < k -> nth_default MEzero (mul_CSR_CSC_row m n p M1 M2 i k) j
   = mul_CSR_CSC_row_col m n p M1 M2 i (p - k + j). 
Proof. 
  intros. 
  generalize dependent j. 
  induction k as [| k IHk]; intros. 
  - inversion H1. 
  - destruct j. 
    + cbn. rewrite <- plus_n_O. reflexivity. 
    + assert (p - S k + S j = p - k + j). { omega. } rewrite H2. 
      apply IHk; try omega. 
Qed. 

Lemma mul_CSR_CSC_correct': forall m n p M1 M2 i j,
  i < m -> j < p -> nth_default MEzero (nth_default nil (mul_CSR_CSC_to_dense m n p M1 M2) i) j
   = mul_CSR_CSC_row_col m n p M1 M2 i j. 
Proof. 
  intros. 
  unfold mul_CSR_CSC_to_dense. rewrite mul_CSR_CSC_correct_row; try omega. 
  rewrite mul_CSR_CSC_correct_entry; try omega. 
  assert (m - m + i = i). { omega. } 
  assert (p - p + j = j). { omega. } 
  rewrite H1. rewrite H2. reflexivity. 
Qed. 


Theorem mul_CSR_CSC_correct: forall m n p M1 M2 i j,
  i < m -> j < p -> nth_default MEzero (nth_default nil (mul_CSR_CSC_to_dense m n p M1 M2) i) j
   = sum n (fun k => (Mget_CSR m n i k M1) *e (Mget_CSC n p k j M2)).
Proof. 
  intros. 
  rewrite mul_CSR_CSC_correct'; try assumption. 
  unfold mul_CSR_CSC_row_col. rewrite mul_CSR_CSC_row_col_eff_correct; try omega. 
  reflexivity. 
Qed. 
Require Import List.
Require Import PeanoNat.
Axiom A: Type. 
Axiom A_plus : A -> A -> A. 
Axiom A_mul : A -> A -> A. 
Infix "+" := A_plus.
Infix "*" := A_mul.
Axiom A_plus_commu: forall a b : A, a + b = b + a. 
Axiom A_plus_assoc: forall a b c: A, (a + b) + c = a + (b + c).
Axiom A_dist: forall a b c: A, a * (b + c) = (a * b) + (a * c).
Axiom A_times_commu: forall a b : A, a * b = b * a. 
Axiom A_times_assoc: forall a b c: A, (a * b) * c = a * (b * c).

Axiom zero: A. 
Axiom A_plus_zero_r: forall a : A, a + zero = a. 
Axiom A_plus_zero_l: forall a : A, zero + a = a. 
Axiom A_times_zero_l: forall a : A, zero * a = zero. 
Axiom A_times_zero_r: forall a : A, a * zero = zero. 


Definition Matrix:= list (list A).

Definition Vector := list A. 

Definition get (M : Matrix) (r c : nat) : A := 
  nth_default zero (nth_default nil M r) c. 

Definition get_r (M : Matrix) (r : nat) : Vector := 
  nth_default nil M r. 

Definition get_v (V : Vector) (r: nat) : A := 
  nth_default zero V r. 


Fixpoint dot (l1 : list A) (l2 : list A) : A :=
  match l1 with
  | nil => zero
  | t :: l1' => t * (nth_default zero l2 0)
                + dot (l1') (tl l2)
  end.  

Fixpoint Vector_plus (l1 : Vector) (l2 : Vector) : Vector :=
  match l1 with
  | nil => l2
  | t :: l1' => (t + nth_default zero l2 0) :: Vector_plus (l1') (tl l2)
  end. 

Definition Matrix_Vector_mul (M : Matrix) (V : Vector) : Vector :=
  map (dot V) M.


Fixpoint col_M (M : Matrix) : nat :=
  match M with 
  | nil => 0
  | t :: M' => max (length t) (col_M M')
end. 

Definition row_M (M : Matrix) : nat :=
  length M.

Fixpoint append_col_left (V : Vector) (M : Matrix) : Matrix := 
  match V with 
  | nil => map (fun (r : list A) => zero :: r) M 
  | v :: V' => (v :: get_r M 0) :: append_col_left (V') (tl M) 
  end. 

Fixpoint transpose (M : Matrix) : Matrix := 
  match M with 
  | nil => nil
  | t :: M' => append_col_left t (transpose M')
end.

Definition Scalar_Vector_mul (c : A) (V : Vector) : Vector :=
  map (fun x => c * x) V.

Definition Vector_Matrix_mul (V : Vector) (M : Matrix) : Vector :=
  map (dot V) (transpose M).

Definition Vector_Matrix_mul_ (M : Matrix) (V : Vector) : Vector :=
  map (dot V) (transpose M).

Definition Matrix_Matrix_mul (M1 : Matrix) (M2 : Matrix) : Matrix :=
  map (Vector_Matrix_mul_ M2) M1.


Lemma append_col_left_row_M : forall V : Vector, forall M : Matrix, 
  row_M (append_col_left V M) = max (length V) (row_M M). 
Proof. 
  intros V. 
  induction V as [| v V' IHV]. 
  - intros M. simpl. unfold row_M. rewrite map_length. reflexivity. 
  - intros M. simpl. destruct (row_M M) eqn : eq. 
    + unfold row_M in eq. apply length_zero_iff_nil in eq. rewrite eq. 
      simpl. rewrite IHV with (M := nil). simpl. rewrite Nat.max_0_r. 
      reflexivity.
    + apply eq_S. rewrite IHV. unfold row_M. unfold row_M in eq. 
      assert(H: (length (tl M)) = pred (length M)). 
      {simpl. unfold tl. destruct M eqn :eq2. 
        * inversion eq. 
        * simpl. reflexivity. }
      rewrite H. rewrite eq. simpl. reflexivity. 
Qed. 

Lemma matrix_transpose_cr: forall M : Matrix, 
  col_M M = row_M (transpose M). 
Proof. 
  intros M. 
  induction M as [| r M' IHM]. 
  - simpl. reflexivity. 
  - simpl. rewrite append_col_left_row_M. rewrite <- IHM. reflexivity. 
Qed. 

Lemma matrix_transpose_first_col: forall M : Matrix, forall V : Vector, forall i : nat, 
  get (append_col_left V M) i 0 = nth_default zero V i. 
Proof. 
  intros M V. 
  generalize dependent M. 
  induction V as [| v V' IHV]. 
  - intros M i. 
    simpl. assert (H: nth_default zero nil i = zero).
    {unfold nth_default. unfold nth_error. destruct i. + reflexivity. + reflexivity. } 
    rewrite H. 
    unfold get. unfold nth_default. 
    destruct (nth_error (map (fun r : list A => zero :: r) M) i) eqn : eq. 
    + apply nth_error_In in eq. apply in_map_iff in eq. inversion eq. 
      inversion H0. rewrite <- H1. simpl. reflexivity. 
    + simpl. reflexivity. 
  - intros M. destruct i eqn : eq. 
    + simpl. unfold get. unfold nth_default. unfold nth_error. reflexivity. 
    + simpl. unfold get. unfold nth_default. unfold nth_error. simpl. 
      apply IHV. 
Qed. 

Lemma append_col_left_index : forall M : Matrix, forall V : Vector, forall i j : nat, 
  get M i j = get (append_col_left V M) i (S j). 
Proof. 
  intros M V. 
  generalize dependent M. 
  induction V as [| v V' IHV]. 
  - intros M i j. simpl. unfold get. unfold nth_default. 
    destruct (nth_error (map (fun r : list A => zero :: r) M) i) eqn: eq. 
    + destruct (nth_error M i) eqn : eq2. 
      * apply map_nth_error with (f:= (fun r : list A => zero :: r)) in eq2.
        rewrite eq2 in eq. inversion eq. simpl. reflexivity. 
      * apply nth_error_None in eq2. 
        rewrite <- map_length with (f := (fun r : list A => zero :: r)) in eq2. 
        apply nth_error_None in eq2. rewrite eq2 in eq. inversion eq. 
    + apply nth_error_None in eq.
      rewrite map_length in eq. 
      apply nth_error_None in eq.
      rewrite eq. unfold nth_error. destruct j. * reflexivity.  * reflexivity. 
  - intros M i j. 
    destruct i as [| i']. 
    + unfold get. unfold nth_default. destruct (nth_error M 0) eqn : eq.
      *  destruct (nth_error (append_col_left (v :: V') M) 0) eqn : eq2. 
        --- unfold append_col_left in eq2. simpl in eq2. inversion eq2. 
            simpl. unfold nth_error in eq. unfold get_r. unfold nth_default.
            destruct (nth_error M 0) eqn : eq3. 
            +++ inversion eq3. rewrite H1 in eq. inversion eq. reflexivity. 
            +++ inversion eq3. rewrite H1 in eq. inversion eq. 
        --- inversion eq2.
      * apply nth_error_None in eq. inversion eq. apply length_zero_iff_nil in H0. 
        rewrite H0. simpl. unfold get_r. unfold nth_default. unfold nth_error. 
        reflexivity. 
    + unfold get. 
      assert (H: (nth_default nil (append_col_left (v :: V') M) (S i')) = (nth_default nil (append_col_left (V') (tl M)) i')).
      { unfold nth_default. unfold append_col_left. simpl. reflexivity. }
      assert (H1 : nth_default nil M (S i') = nth_default nil (tl M) i').
      {unfold nth_default. unfold tl. simpl.  destruct M. 
        * destruct i'. 
          --- reflexivity.  --- reflexivity. 
        * reflexivity. }
      rewrite H. rewrite H1. apply IHV. 
Qed. 

Theorem matrix_transpose_ij: forall M : Matrix, forall i j : nat, 
  get M i j = get (transpose M) j i. 
Proof. 
  intros M. 
  induction M as [| r M' IHM].
  - intros i j. 
    simpl. unfold get. unfold nth_default. 
    assert (H1 : forall B : Type, nth_error (@ nil (B)) i = None).
    {unfold nth_error. destruct i eqn : eq. 
      + reflexivity. +reflexivity. }
    assert (H2 : forall B : Type, nth_error (@ nil (B)) j = None).
    {unfold nth_error. destruct j eqn : eq. 
      + reflexivity. +reflexivity. }
    rewrite H1. rewrite H2. rewrite H2. rewrite H1. reflexivity. 
  - intros i j. 
    simpl. destruct i eqn : eqi. 
    + rewrite matrix_transpose_first_col. unfold get. unfold nth_default. unfold nth_error. 
      reflexivity. 
    + assert (H: get (r :: M') (S n) j = get M' n j). 
      {unfold get. unfold nth_default. unfold nth_error. reflexivity. }
      rewrite H. rewrite IHM. apply append_col_left_index.
Qed. 

Theorem dot_commu: forall v1 v2 : Vector, 
  dot v1 v2 = dot v2 v1. 
Proof. 
  intros v1. 
  induction v1 as [| a v1' IHv1]. 
  - intros v2. induction v2 as [| b v2' IHv2]. 
    + reflexivity. 
    + simpl. rewrite <- IHv2. simpl. rewrite A_plus_zero_r.
      unfold nth_default. unfold nth_error. rewrite A_times_zero_r. 
      reflexivity. 
  - intros v2. simpl. rewrite IHv1. 
    unfold tl. destruct v2. 
    + simpl. rewrite A_plus_zero_r. unfold nth_default. unfold nth_error. 
      rewrite A_times_zero_r. reflexivity. 
    + simpl. unfold nth_default. unfold nth_error. rewrite A_times_commu. 
      reflexivity. 
Qed. 

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

Theorem Vector_plus_commu: forall l1 l2, 
  Vector_plus l1 l2 = Vector_plus l2 l1. 
Proof. 
  intros l1. 
  induction l1 as [| a l1' IHl1]. 
  - intros l2. 
    simpl. induction l2 as [| b l2' IHl2].
    + reflexivity. 
    + simpl. unfold nth_default. unfold nth_error. rewrite A_plus_zero_r.
      rewrite <- IHl2. reflexivity.
  - intros l2. simpl. rewrite IHl1. 
    induction l2 as [| b l2' IHl2]. 
    + simpl. unfold nth_default. unfold nth_error. rewrite A_plus_zero_r. 
      reflexivity. 
    + simpl. rewrite nth_default_0. rewrite nth_default_0.
      rewrite A_plus_commu. reflexivity. 
Qed. 


Theorem Vector_plus_assoc: forall l1 l2 l3, 
  Vector_plus (Vector_plus l1 l2) l3 = Vector_plus l1 (Vector_plus l2 l3). 
Proof. 
  intros l1. 
  induction l1 as [| a l1' IHl1]. 
  - simpl. reflexivity. 
  - simpl. intros l2. induction l2 as [| b l2' IHl2].
    + simpl. intros l3. assert (H: Vector_plus l1' nil = Vector_plus nil l1'). 
      {apply Vector_plus_commu. }
      rewrite H. simpl. assert (H1: nth_default zero nil 0 = zero).
      {reflexivity. }
      rewrite H1. rewrite A_plus_zero_r. reflexivity. 
    + simpl. intros l3. rewrite nth_default_0. rewrite nth_default_0.
      rewrite IHl1. rewrite A_plus_assoc. reflexivity. 
Qed. 

Theorem Vector_scalar_dist: forall l1 l2: Vector, forall c: A, 
  Scalar_Vector_mul c (Vector_plus l1 l2) = Vector_plus (Scalar_Vector_mul c l1) (Scalar_Vector_mul c l2).
Proof. 
  intros l1. 
  induction l1 as [| a l1' IHl1]. 
  - intros l2 c. 
    simpl. reflexivity. 
  - intros l2 c. 
    simpl. rewrite IHl1. rewrite A_dist. 
    destruct l2. 
    + simpl. rewrite Vector_plus_commu. simpl. 
      unfold nth_default. unfold nth_error. rewrite A_times_zero_r. 
      reflexivity. 
    + simpl. rewrite nth_default_0. rewrite nth_default_0. reflexivity. 
Qed. 

Theorem Vector_scalar_assoc: forall l1 l2: Vector, forall c: A, 
  dot (Scalar_Vector_mul c l1) l2 = c * (dot l1 l2).
Proof. 
  intros l1. 
  induction l1 as [| t l1' IHl1]. 
  - intros l2 c. simpl. rewrite A_times_zero_r. reflexivity. 
  - intros l2 c. simpl. rewrite IHl1. rewrite A_times_assoc. rewrite A_dist. 
    reflexivity. 
Qed. 

Theorem dot_dist: forall l1 l2 l3: Vector,
  dot (Vector_plus l1 l2) l3 = (dot l1 l3) + (dot l2 l3). 
Proof. 
  intros l1 l2 l3.
  generalize dependent l2.
  generalize dependent l1.
  induction l3 as [| a l3' IHl3]. 
  - intros l1 l2. rewrite dot_commu. simpl. 
    rewrite dot_commu. simpl. 
    rewrite dot_commu. simpl. 
    rewrite A_plus_zero_l. 
    reflexivity. 
  - intros l1 l2. 
    destruct l1. 
    + destruct l2. 
      * simpl. rewrite A_plus_zero_l. reflexivity. 
      * simpl. rewrite nth_default_0. rewrite A_plus_zero_l. reflexivity. 
    + destruct l2. 
      * simpl. rewrite nth_default_0. unfold nth_default. unfold nth_error. 
        rewrite A_plus_zero_r. rewrite A_plus_zero_r.
        rewrite Vector_plus_commu. simpl. reflexivity. 
      * simpl. rewrite nth_default_0. rewrite nth_default_0.
        rewrite IHl3. rewrite A_times_commu. rewrite A_dist. 
        rewrite A_plus_assoc. 
        assert (H: a * a1 + (dot l1 l3' + dot l2 l3') = dot l1 l3' + (a1 * a + dot l2 l3')).
        {rewrite <- A_plus_assoc. rewrite A_times_commu. 
        assert (H1 : a1 * a + dot l1 l3' =  dot l1 l3' + a1 * a). 
        {rewrite A_plus_commu. reflexivity. }
        rewrite H1. apply A_plus_assoc. }
        rewrite H. rewrite A_times_commu. rewrite <- A_plus_assoc. 
        reflexivity. 
Qed.  

Lemma vec_times_mac_induct_lemma: forall v v' : Vector, forall M : Matrix, forall a : A,
  map (dot (a :: v)) (append_col_left v' M) = Vector_plus (Scalar_Vector_mul a v') (map (dot (v)) M).
Proof. 
  intros v v' M.
  generalize dependent v'. 
  generalize dependent v. 
  induction M as [| v2 M' IHM]. 
  - intros v v'. generalize dependent v. induction v' as [| b v' IHv]. 
    + intros v a. simpl. unfold Vector_Matrix_mul. simpl. reflexivity. 
    + intros v a. unfold append_col_left. 
      assert (H: forall f : Vector -> A, forall a v, map f (a::v) = (f a) :: (map f v)). 
      { simpl. reflexivity. }
      rewrite H. rewrite IHv. simpl. unfold get_r. unfold nth_default. 
      unfold nth_error. rewrite dot_commu. simpl. reflexivity. 
  - intros v v' a. destruct v' as [| b v'].
    + assert (H: append_col_left nil (v2 :: M') = (zero :: v2) :: (append_col_left nil M')). 
      { simpl. reflexivity. }
      rewrite H. assert (H1: forall f : Vector -> A, forall a v, map f (a::v) = (f a) :: (map f v)). 
      { simpl. reflexivity. }
      rewrite H1. rewrite IHM. simpl. 
      assert (H3: nth_default zero (zero :: v2) 0 = zero). 
      { reflexivity. }
      rewrite H3. rewrite A_times_zero_r. rewrite A_plus_zero_l. 
      reflexivity. 
    + unfold append_col_left. 
      assert (H: forall f : Vector -> A, forall a v, map f (a::v) = (f a) :: (map f v)). 
      { simpl. reflexivity. }
      rewrite H. rewrite IHM. simpl. rewrite nth_default_0. 
      rewrite nth_default_0. unfold get_r. rewrite nth_default_0. 
      reflexivity. 
Qed. 

Lemma vec_times_mac_induct: forall v v' : Vector, forall M : Matrix, forall a : A,
  Vector_Matrix_mul (a :: v) (v' :: M) = Vector_plus (Scalar_Vector_mul a v') (Vector_Matrix_mul v M).
Proof. 
  intros v v' M a. 
  unfold Vector_Matrix_mul. unfold transpose. rewrite vec_times_mac_induct_lemma.
  reflexivity. 
Qed. 

Lemma mac_times_vec_induct: forall v v' : Vector, forall M : Matrix,
  Matrix_Vector_mul (v' :: M) v = (dot v' v) :: Matrix_Vector_mul M v.
Proof. 
  intros v v' M.
  simpl. rewrite dot_commu. reflexivity. 
Qed. 

Theorem vector_matrix_vector_assoc: forall v1 v2: Vector, forall M : Matrix, 
  dot (Vector_Matrix_mul v1 M) v2 = dot v1 (Matrix_Vector_mul M v2). 
Proof. 
  intros v1 v2 M. 
  generalize dependent v2. 
  generalize dependent v1. 
  induction M as [| v M' IHM]; intros v1 v2. 
  - simpl. rewrite dot_commu. reflexivity. 
  - destruct v1 eqn : eq. 
    + simpl. unfold Vector_Matrix_mul. 
      assert (H : forall M, map (dot nil) M = repeat zero (length M)). 
      { intros M. induction M as [| v3 M2 IHM2]; simpl in *.
        * reflexivity. 
        * rewrite IHM2. reflexivity.  }
      rewrite H. 
      assert (H2: forall n v, dot (repeat zero n) v = zero). 
      { intros n. induction n as [| n' IHn]. 
        * intros v0. simpl. reflexivity. 
        * intros v0. simpl. rewrite IHn. rewrite A_times_zero_l. 
          rewrite A_plus_zero_l. reflexivity. }
      rewrite H2. reflexivity. 
    + rewrite vec_times_mac_induct. rewrite mac_times_vec_induct. 
      rewrite dot_dist. simpl. unfold nth_default. unfold nth_error. 
      rewrite IHM. rewrite  Vector_scalar_assoc. reflexivity. 
Qed. 




Definition iso_v (v1 v2 : Vector) := 
  forall i, get_v v1 i = get_v v2 i. 

Theorem equal_iso_v: forall v, 
  iso_v v v. 
Proof. 
  intros v. 
  induction v as [| a v' IHv]. 
  - unfold iso_v. intros i. reflexivity. 
  - unfold iso_v. intros i. destruct i as [| i']. 
    + reflexivity. 
    + unfold get_v. unfold nth_default. unfold nth_error. apply IHv. 
Qed. 

Theorem symme_iso_v: forall v1 v2, 
  iso_v v1 v2 -> iso_v v2 v1.
Proof. 
  intros v1 v2 H. 
  unfold iso_v. 
  intros i. 
  symmetry. rewrite H. reflexivity.
Qed. 

Theorem trans_iso_v: forall v1 v2 v3, 
  iso_v v1 v2 -> iso_v v2 v3 -> iso_v v1 v3.
Proof. 
  intros v1 v2 v3 H1 H2. 
  unfold iso_v. intros i. 
  rewrite H1. rewrite H2. reflexivity. 
Qed. 

Lemma Scalar_Vector_mul_extract : forall v c i, 
  get_v (Scalar_Vector_mul c v) i = c * (get_v v i).
Proof. 
  intros v. induction v as [| a v' IHv]. 
  - intros c0 i. simpl. unfold get_v. unfold nth_default. unfold nth_error. 
    destruct i. 
    + rewrite A_times_zero_r. reflexivity. 
    + rewrite A_times_zero_r. reflexivity. 
  - intros c0 i. destruct i as [| i].
    + simpl. unfold get_v. unfold nth_default. unfold nth_error. 
      reflexivity. 
    + simpl. unfold get_v. unfold nth_default. unfold nth_error. 
      apply IHv. 
Qed. 

Theorem scalar_mul_iso_v : forall v1 v2 c, 
  iso_v v1 v2 -> iso_v (Scalar_Vector_mul c v1) (Scalar_Vector_mul c v2).
Proof. 
  intros v1 v2 c H. 
  unfold iso_v. intros i. rewrite Scalar_Vector_mul_extract. rewrite Scalar_Vector_mul_extract. 
  rewrite H. reflexivity. 
Qed. 

Lemma Vector_plus_extract : forall v1 v2 i, 
  get_v (Vector_plus v1 v2) i = (get_v v1 i) + (get_v v2 i). 
Proof. 
  intros v. 
  induction v as [| a v' IHv]. 
  - intros v2 i. 
    simpl. destruct i. 
    + unfold get_v. unfold nth_default. unfold nth_error. rewrite A_plus_zero_l. 
      reflexivity. 
    + unfold get_v. unfold nth_default. unfold nth_error. rewrite A_plus_zero_l. 
      reflexivity. 
  - intros v2 i. 
    destruct v2 as [| b v2]. 
    + simpl. rewrite Vector_plus_commu. simpl. 
      unfold nth_default. unfold nth_error. rewrite A_plus_zero_r. 
      destruct i as [| i]. 
      * unfold get_v. unfold nth_default. unfold nth_error. 
        rewrite A_plus_zero_r. reflexivity. 
      * unfold get_v. unfold nth_default. unfold nth_error. 
        rewrite A_plus_zero_r. reflexivity. 
    + simpl. destruct i as [| i]. 
      * rewrite nth_default_0. unfold get_v. 
        rewrite nth_default_0. rewrite nth_default_0. rewrite nth_default_0.
        reflexivity. 
      * rewrite nth_default_0. 
        assert (H1: forall a v i, get_v (a::v) (S i) = get_v v i). 
        { intros a0 v i0. unfold get_v. unfold nth_default. unfold nth_error.
          reflexivity. }
        rewrite H1. rewrite H1. rewrite H1. apply IHv. 
Qed. 

Theorem vec_plus_iso_v : forall v1 v1' v2 v2', 
  iso_v v1 v1' -> iso_v v2 v2' -> iso_v (Vector_plus v1 v2) (Vector_plus v1' v2').
Proof. 
  intros v1 v1' v2 v2' H1 H2. 
  unfold iso_v. 
  intros i. 
  rewrite Vector_plus_extract. 
  rewrite Vector_plus_extract. 
  rewrite H1. rewrite H2. reflexivity. 
Qed. 

Theorem tl_iso_v : forall v1 v2, 
  iso_v v1 v2 -> iso_v (tl v1) (tl v2).
Proof. 
  intros v1. 
  induction v1 as [| a v1 IHv1]. 
  - intros v2 H. 
    simpl. 
    unfold iso_v. 
    intros i. destruct v2 as [| b v2]. 
    + simpl. reflexivity. 
    + simpl. unfold iso_v in H. 
      assert (H1 : get_v (v2) i = get_v (b :: v2) (S i)). 
      { unfold get_v. unfold nth_default. unfold nth_error. reflexivity. }
      rewrite H1. rewrite <- H. unfold get_v. unfold nth_default. 
      unfold nth_error.
      destruct i. 
      * reflexivity. * reflexivity. 
  - intros v2 H. 
    simpl. destruct v2 as [| b v2]. 
    + simpl. unfold iso_v. intros i. 
      assert (H1 : get_v v1 i = get_v (a :: v1) (S i)). 
      { unfold get_v. unfold nth_default. unfold nth_error. reflexivity. }
      rewrite H1. rewrite H. unfold get_v. unfold nth_default. 
      unfold nth_error.
      destruct i. 
      * reflexivity. * reflexivity. 
    + simpl. unfold iso_v. intros i. 
      assert (H1 : get_v v1 i = get_v (a :: v1) (S i)). 
      { unfold get_v. unfold nth_default. unfold nth_error. reflexivity. }
      assert (H2 : get_v v2 i = get_v (b :: v2) (S i)). 
      { unfold get_v. unfold nth_default. unfold nth_error. reflexivity. }
      rewrite H1. rewrite H2. rewrite H. reflexivity.
Qed.  

Lemma dot_iso_v_one_side : forall v1 v1' v,  
  iso_v v1 v1' -> dot v v1 = dot v v1'.
Proof. 
  intros v1 v1' v. 
  generalize dependent v1'. 
  generalize dependent v1.
  induction v as [| a v IHv]. 
  + intros v1 v1'. intros H. simpl. reflexivity. 
  + intros v1 v1'. intros H. 
    simpl. rewrite H. apply tl_iso_v in H. apply IHv in H. 
    rewrite H. reflexivity. 
Qed. 

Theorem dot_iso_v : forall v1 v1' v2 v2', 
  iso_v v1 v1' -> iso_v v2 v2' -> dot v1 v2 = dot v1' v2'.
Proof. 
  intros v1 v1' v2 v2' H1 H2. 
  apply dot_iso_v_one_side with (v := v1) in H2.
  rewrite H2. 
  rewrite dot_commu. 
  assert (H : dot v1' v2' = dot v2' v1'). { rewrite dot_commu. reflexivity. }
  rewrite H. apply dot_iso_v_one_side with (v:=v2') in H1. 
  rewrite H1. reflexivity. 
Qed. 


Lemma matrix_matrix_mul_get_r: forall X Y : Matrix, forall i : nat, 
  iso_v (get_r (Matrix_Matrix_mul X Y) i) (Vector_Matrix_mul (get_r X i) Y).
Proof. 
  intros X. 
  unfold Matrix_Matrix_mul. 
  unfold Vector_Matrix_mul_. 
  unfold Vector_Matrix_mul. 
  induction X as [| v X IHX].
  - intros Y i. 
    simpl. unfold iso_v. 
    intros i0. 
    unfold get_r. rewrite nth_default_nil. rewrite nth_default_nil. 
    simpl. 
    assert (H : forall i0, forall X : Matrix, nth_default zero (map (fun _ : list A => zero) X) i0 = zero). 
    { intros i1. 
      induction i1 as [| i1 IHi1]. 
      - intros X. destruct X. 
        + simpl. unfold nth_default. unfold nth_error. reflexivity. 
        + simpl. rewrite nth_default_0. reflexivity. 
      - intros X. destruct X. 
        + simpl. unfold nth_default. unfold nth_error. reflexivity. 
        + simpl. rewrite nth_default_S. apply IHi1.
    } 
    rewrite H. unfold get_v. rewrite nth_default_nil. reflexivity. 
  - intros Y i. unfold iso_v. 
    intros i0. destruct i as [| i]. 
    + simpl. unfold get_r. rewrite nth_default_0. rewrite nth_default_0. 
      reflexivity. 
    + unfold get_r. rewrite nth_default_S. rewrite <- IHX. 
      rewrite map_cons. rewrite nth_default_S. reflexivity. 
Qed. 

Lemma matrix_vector_mul_get_v: forall X v i, 
  get_v (Matrix_Vector_mul X v) i = dot (get_r X i) v. 
Proof. 
  intros X. 
  unfold Matrix_Vector_mul. 
  unfold get_r. 
  induction X as [| v' X IHX].
  - intros V i. rewrite nth_default_nil. simpl. unfold get_v. 
    rewrite nth_default_nil. reflexivity. 
  - intros v i. destruct i as [| i]. 
    + rewrite nth_default_0. simpl. unfold get_v. rewrite nth_default_0. 
      rewrite dot_commu. reflexivity. 
    + rewrite nth_default_S. simpl. unfold get_v. rewrite nth_default_S.
      rewrite IHX. reflexivity. 
Qed. 

Theorem matrix_matrix_vector_assoc: forall v: Vector, forall X Y: Matrix, 
  iso_v (Matrix_Vector_mul (Matrix_Matrix_mul X Y) v) (Matrix_Vector_mul X (Matrix_Vector_mul Y v)).
Proof. 
  intros v X Y. 
  unfold iso_v. intros i. 
  rewrite matrix_vector_mul_get_v. 
  rewrite matrix_vector_mul_get_v.
  rewrite <- vector_matrix_vector_assoc. 
  assert (H: iso_v (get_r (Matrix_Matrix_mul X Y) i) (Vector_Matrix_mul (get_r X i) Y)). 
  { apply matrix_matrix_mul_get_r. }
  apply dot_iso_v_one_side with (v := v) in H. 
  rewrite dot_commu. rewrite H. rewrite dot_commu. reflexivity. 
Qed. 



Lemma matrix_mul_extract: forall X Y i j, 
  get (Matrix_Matrix_mul X Y) i j = dot (get_r X i) (get_r (transpose Y) j).
Proof. 
  intros X Y i j. 
  unfold Matrix_Matrix_mul.
  unfold Vector_Matrix_mul_.
  unfold get.
  assert (H: forall L: Matrix, forall k p k1, nth_default zero (nth_default nil L k1) k = nth_default zero (nth_default (repeat zero p) L k1) k).
  { intros L. 
    induction L as [| v L IHL]. 
    - intros k p k1. 
      rewrite nth_default_nil. rewrite nth_default_nil. rewrite nth_default_nil. 
      generalize dependent k. 
      induction p as [| p IHp].
      + intros k. simpl. rewrite nth_default_nil. reflexivity. 
      + intros k. destruct k as [|k]. 
        * simpl. rewrite nth_default_0. reflexivity. 
        * simpl. rewrite nth_default_S. apply IHp. 
    - intros k p k1. 
      destruct k1 as [| k1]. 
      + simpl. rewrite nth_default_0. rewrite nth_default_0. reflexivity. 
      + rewrite nth_default_S. rewrite nth_default_S. apply IHL. 
  }
  rewrite H with (p := length (transpose Y)). 
  rewrite nth_default_map with (X := X) (d := nil) . 
  - rewrite nth_default_map with (X := (transpose Y)) (d := nil).
    + reflexivity. 
    + rewrite dot_commu. simpl. reflexivity. 
  - simpl. 
    assert (H1 : forall Z, map (fun _ : list A => zero) Z = repeat zero (length Z)). 
    {
      intros Z. induction Z as [| v Z IHZ].
      + simpl. reflexivity. 
      + simpl. rewrite IHZ. reflexivity. 
    }
    apply H1. 
Qed. 

Theorem vector_matrix_matrix_assoc: forall v: Vector, forall X Y: Matrix, 
  iso_v (Vector_Matrix_mul v (Matrix_Matrix_mul X Y)) (Vector_Matrix_mul (Vector_Matrix_mul v X) Y).
Proof. 
  intros v X Y. 
  unfold iso_v. intros i. 
  assert (H : Vector_Matrix_mul v (Matrix_Matrix_mul X Y) = Matrix_Vector_mul (transpose (Matrix_Matrix_mul X Y)) v). 
  { reflexivity. }
  rewrite H. rewrite matrix_vector_mul_get_v.
  assert (H1 : Vector_Matrix_mul (Vector_Matrix_mul v X) Y = Matrix_Vector_mul (transpose Y) (Vector_Matrix_mul v X)).
  { reflexivity. }
  rewrite H1. rewrite matrix_vector_mul_get_v.
  assert (H3: dot (get_r (transpose Y) i) (Vector_Matrix_mul v X) = dot (Vector_Matrix_mul v X) (get_r (transpose Y) i) ). 
  { apply dot_commu. }
  rewrite H3. rewrite vector_matrix_vector_assoc. 
  assert (H4: iso_v (get_r (transpose (Matrix_Matrix_mul X Y)) i) (Matrix_Vector_mul X (get_r (transpose Y) i))).
  { unfold iso_v. intros j. assert (H4 : get_v (get_r (transpose (Matrix_Matrix_mul X Y)) i) j = get (Matrix_Matrix_mul X Y) j i). 
    { rewrite matrix_transpose_ij. reflexivity. }
    rewrite H4. rewrite matrix_vector_mul_get_v. apply matrix_mul_extract. }
  rewrite dot_commu. apply dot_iso_v. 
  - apply equal_iso_v. 
  - apply H4. 
Qed. 

Definition iso_m (M1 M2 : Matrix) := 
  forall i j, get M1 i j = get M2 i j. 


Theorem equal_iso_m: forall M, 
  iso_m M M. 
Proof. 
  intros M. 
  unfold iso_m. 
  reflexivity. 
Qed. 

Theorem symme_iso_m: forall M1 M2, 
  iso_m M1 M2 -> iso_m M2 M1.
Proof. 
  intros M1 M2 H. 
  unfold iso_m. 
  symmetry. apply H. 
Qed. 

Theorem trans_iso_m: forall M1 M2 M3, 
  iso_m M1 M2 -> iso_m M2 M3 -> iso_m M1 M3.
Proof. 
  intros M1 M2 M3 H1 H2. 
  unfold iso_m. 
  intros i j. 
  rewrite H1. rewrite H2. 
  reflexivity. 
Qed.


Theorem iso_m_to_iso_v : forall M1 M2, 
  iso_m M1 M2 -> forall i, iso_v (get_r M1 i) (get_r M2 i). 
Proof. 
  intros M1 M2 H i.
  unfold iso_v. 
  intros j.
  unfold iso_m in H. 
  unfold get in H. 
  unfold get_v. unfold get_r. 
  rewrite H. 
  reflexivity. 
Qed. 


Theorem iso_v_to_iso_m : forall M1 M2, 
  (forall i, iso_v (get_r M1 i) (get_r M2 i)) -> iso_m M1 M2. 
Proof. 
  intros M1 M2 H.
  unfold iso_m. 
  intros x y.
  unfold get. 
  unfold iso_v in H. 
  unfold get_v in H. 
  unfold get_r in H. 
  apply H.  
Qed. 

Theorem transpose_iso_m: forall M1 M2, 
  iso_m M1 M2 -> iso_m (transpose M1) (transpose M2). 
Proof. 
  intros M1 M2 H. 
  unfold iso_m. 
  intros i j. 
  rewrite <- matrix_transpose_ij. 
  rewrite <- matrix_transpose_ij. 
  apply H. 
Qed. 

Theorem Matrix_Vector_mul_iso_m: forall M M' v v', 
  iso_m M M' -> iso_v v v' -> iso_v (Matrix_Vector_mul M v) (Matrix_Vector_mul M' v'). 
Proof. 
  intros M M' v v' H1 H2. 
  unfold iso_v. 
  intros i. 
  rewrite matrix_vector_mul_get_v. rewrite matrix_vector_mul_get_v. 
  assert (H : iso_v (get_r M i) (get_r M' i)). 
  { apply iso_m_to_iso_v with (i := i) in H1. apply H1. }
  apply dot_iso_v with (v2:=v) (v2' := v') in H.
  - rewrite H. reflexivity. 
  - apply H2. 
Qed. 


Theorem Vector_Matrix_mul_iso_m: forall M M' v v', 
  iso_m M M' -> iso_v v v' -> iso_v (Vector_Matrix_mul v M) (Vector_Matrix_mul v' M').
Proof. 
  intros M M' v v' H1 H2. 
  unfold iso_v. 
  intros i. 
  unfold Vector_Matrix_mul. 
  apply transpose_iso_m in H1. 
  apply Matrix_Vector_mul_iso_m with (v:=v) (v':=v') in H1.
  + apply H1. 
  + apply H2. 
Qed. 

Lemma Matrix_Matrix_mul_iso_m_r: forall X Y Y', 
  iso_m Y Y' -> iso_m (Matrix_Matrix_mul X Y) (Matrix_Matrix_mul X Y').
Proof. 
  intros X Y Y' H. 
  apply iso_v_to_iso_m. 
  intros i. 
  assert (H1: iso_v (get_r (Matrix_Matrix_mul X Y) i) (Vector_Matrix_mul (get_r X i) Y)). 
  { apply matrix_matrix_mul_get_r. }
  apply trans_iso_v with (v2:= (Vector_Matrix_mul (get_r X i) Y)).
  - apply H1. 
  - assert (H2: iso_v (get_r (Matrix_Matrix_mul X Y') i) (Vector_Matrix_mul (get_r X i) Y')).
    { apply matrix_matrix_mul_get_r. }
    apply trans_iso_v with (v2:= (Vector_Matrix_mul (get_r X i) Y')).
    + apply Vector_Matrix_mul_iso_m with (v := (get_r X i)) (v' := (get_r X i)) in H.
      * apply H. 
      * apply equal_iso_v. 
    + apply symme_iso_v. apply H2. 
Qed. 

Lemma Matrix_Matrix_mul_iso_m_l: forall X X' Y, 
  iso_m X X' -> iso_m (Matrix_Matrix_mul X Y) (Matrix_Matrix_mul X' Y).
Proof. 
  intros X X' Y H. 
  apply iso_v_to_iso_m. 
  intros i. 
  assert (H1: iso_v (get_r (Matrix_Matrix_mul X Y) i) (Vector_Matrix_mul (get_r X i) Y)). 
  { apply matrix_matrix_mul_get_r. }
  assert (H2: iso_v (get_r (Matrix_Matrix_mul X' Y) i) (Vector_Matrix_mul (get_r X' i) Y)).
  { apply matrix_matrix_mul_get_r. }
  apply trans_iso_v with (v2 := (Vector_Matrix_mul (get_r X i) Y)). 
  - apply H1. 
  - apply trans_iso_v with (v2:= (Vector_Matrix_mul (get_r X' i) Y)). 
    + apply Vector_Matrix_mul_iso_m. 
      * apply equal_iso_m. 
      * apply iso_m_to_iso_v. apply H. 
    + apply symme_iso_v. apply H2. 
Qed. 

Theorem Matrix_Matrix_mul_iso_m: forall X X' Y Y', 
  iso_m X X' -> iso_m Y Y' -> iso_m (Matrix_Matrix_mul X Y) (Matrix_Matrix_mul X' Y').
Proof. 
  intros X X' Y Y'. 
  intros H1 H2. 
  apply trans_iso_m with (M2 := Matrix_Matrix_mul X' Y).
  - apply Matrix_Matrix_mul_iso_m_l. apply H1. 
  - apply Matrix_Matrix_mul_iso_m_r. apply H2. 
Qed. 


Theorem matrix_times_assoc: forall X Y Z: Matrix, 
  iso_m (Matrix_Matrix_mul (Matrix_Matrix_mul X Y) Z) (Matrix_Matrix_mul X (Matrix_Matrix_mul Y Z)).
Proof. 
  intros X Y Z. 
  apply iso_v_to_iso_m.
  intros i. 
  apply trans_iso_v with (v2 := Vector_Matrix_mul (get_r X i) (Matrix_Matrix_mul Y Z)).
  - apply trans_iso_v with (v2 := Vector_Matrix_mul (get_r (Matrix_Matrix_mul X Y) i) Z).
    + apply matrix_matrix_mul_get_r. 
    + apply trans_iso_v with (v2:=  (Vector_Matrix_mul (Vector_Matrix_mul (get_r X i) Y) Z)).
      * assert (H : iso_v (get_r (Matrix_Matrix_mul X Y) i) (Vector_Matrix_mul (get_r X i) Y)). 
        { apply matrix_matrix_mul_get_r. }
        apply Vector_Matrix_mul_iso_m with (M := Z) (M' := Z) in H.
        --- apply H. 
        --- apply equal_iso_m. 
      * apply symme_iso_v. apply vector_matrix_matrix_assoc.
  - apply symme_iso_v. apply matrix_matrix_mul_get_r.
Qed.  
  
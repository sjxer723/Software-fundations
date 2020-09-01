Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

(* ################################################################# *)
(** * Relations *)
(*集合X上的二元关系指所有的由两个X中的元素参数化的命题，即有关一对X中元素的命题*)
Definition relation (X: Type) := X -> X -> Prop.

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
(*然而我们不直接写成Inductive le:relation nat 是想将第一个参数nat放在:左侧
提供更友好的归纳法则*)

(* ################################################################# *)
(** * Basic Properties *)
(* ----------------------------------------------------------------- *)
(** *** Partial Functions *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., [R x y1]
    and [R x y2] together imply [y1 = y2]. *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.

(** **** Exercise: 2 stars, standard, optional (total_relation_not_partial) *)
Theorem total_relation_not_a_partial_function:
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0=1) as Nonsense. {
    apply Hc with (x:=0).
    -apply total_0_0.
    -apply total_n_m. apply total_0_0.
  }
  discriminate Nonsense.
Qed.

(** **** Exercise: 2 stars, standard, optional (empty_relation_partial) *)
Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros.
  inversion H.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Reflexive Relations *)
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.
(* ----------------------------------------------------------------- *)
(** *** Transitive Relations *)
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** Exercise: 2 stars, standard, optional (le_trans_hard_way)*)
Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  -apply le_S. apply Hnm.
  -apply le_S. apply IHHm'o.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (lt_trans'') *)
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  -inversion Hmo.
  -apply le_S.
   inversion Hmo.
   +rewrite<-H0. apply Hnm.
   +apply IHo'. apply H0.
Qed.
(** [] *)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

(** **** Exercise: 1 star, standard, optional (le_S_n)  *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros.
  inversion H.
  -reflexivity.
  -apply le_trans with (a:=n) (b:=S n) (c:=m).
   +apply le_S. apply le_n.
   +apply H1.
Qed.
(** [] *)



(** **** Exercise: 1 star, standard, optional (le_Sn_n)  *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not.
  intros.
  induction n.
  -inversion H.
  -apply le_S_n in H. apply IHn in H. apply H.
Qed.
(** [] *)
(* ----------------------------------------------------------------- *)
(** *** Symmetric and Antisymmetric Relations *)
(** A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercise: 2 stars, standard, optional (le_not_symmetric)  *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not.
  intros.
  assert(1<=0) as Nonsense. {
   apply H.
   apply le_S.
   apply le_n.
  }
  inversion Nonsense.
Qed.
(** [] *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, standard, optional (le_antisymmetric)  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros.
  induction H0.
  -reflexivity.
  -assert(S m <= m ) as Nonsense. {
   apply le_trans with (a:=S m) (b:=b) (c:=m).
   + apply H.
   + apply H0.
  }
  apply le_Sn_n in Nonsense.
  destruct Nonsense.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (le_step)  *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros.
  inversion H.
  -rewrite<- H1 in H0. apply le_S_n. apply H0.
  -rewrite<- H2 in H0. apply le_S_n in H0.
   assert(S n<= p). {
    apply le_trans with (a:= S n) (b:=m0) (c:=p) .
    +apply H1. +apply H0.
  }
  apply le_trans with (a:=n) (b:=S n) (c:= p).
  +apply le_S. apply le_n.
  +apply H3.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Equivalence Relations *)
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* ----------------------------------------------------------------- *)
(** *** Partial Orders and Preorders *)
(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.

(* ################################################################# *)
(** * Reflexive, Transitive Closure *)
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - intro H. induction H.
    + (* le_n *) apply rt_refl.
    + apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.


Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.


Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

(** **** Exercise: 2 stars, standard, optional (rsc_trans)  *)
Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros.
  induction H.
  -apply H0.
  -apply IHclos_refl_trans_1n in H0.
   apply (rt1n_trans R x y z).
   +apply Hxy.
   +apply H0.
Qed.
  
(** [] *)

(** **** Exercise: 3 stars, standard, optional (rtc_rsc_coincide)  *)
Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros.
  split.
  -intros.
    induction H.
   +apply rsc_R. apply H.
   +apply rt1n_refl.
   +apply rsc_trans with y.
    *apply IHclos_refl_trans1.
    *apply IHclos_refl_trans2.
  -intros.
    induction H.
   +apply rt_refl.
   +apply rt_step in Hxy. apply rt_trans with y.
    *apply Hxy.
    *apply IHclos_refl_trans_1n.
Qed.
(** [] *)

(* Wed Jan 9 12:02:46 EST 2019 *)

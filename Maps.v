From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Check string_dec.
(*string_dec 的类型并不是bool，而是一个形如{x=y}+{x\neq y}的类型，叫做sumbool
一个sumbool类型的元素要么是x和y相等的证明，要么是x和y不等证明，目前可当做bool来考虑*)

(** Now we need a few basic properties of string equality... *)
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.
(*两个字符创在eqb_string意义上相等，当且仅当在=意义上相等,建立了互映的关系*)

(** The following useful property follows from an analogous
    lemma about strings: *)
Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y =true <-> x=y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [|Hs].
  - subst. split. reflexivity. reflexivity.
  - split.
    + intros H. inversion H.
    + intros. rewrite H in Hs. destruct Hs. reflexivity.
Qed. 
(** Similarly: *)
Theorem eqb_string_false_iff : forall x y :string,
    eqb_string x y= false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** This handy variant follows just by rewriting: *)

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A : Type) := string -> A.

(*t_empty 在应用到任何字符串时都会返回默认元素*)
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

(*由t_update可构造高阶函数，逐个修改键值，下面就构造出string到bool的映射，其中"foo"和"bar"映射到true
其他映射到false*)
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
     _ !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, standard, optional (t_apply_empty) *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros. reflexivity. Qed.
(** [] *)
(** **** Exercise: 2 stars, standard, optional (t_update_eq) *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update.
  assert(H: eqb_string x x =true). {rewrite eqb_string_true_iff. reflexivity. }
  rewrite H.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_neq) *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  assert(H1: eqb_string x1 x2 =false). { apply false_eqb_string. apply H. }
  rewrite H1.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_shadow)  *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x x0).
  -reflexivity.
  -reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (eqb_stringP)*)

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros.
  apply iff_reflect.
  rewrite eqb_string_true_iff.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (t_update_same) *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x x0) eqn: H1.
  -apply eqb_string_true_iff in H1. rewrite H1. reflexivity.
  -reflexivity.
Qed.
(** **** Exercise: 3 stars, standard, recommended (t_update_permute) *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x1 x) eqn: H1.
  - destruct (eqb_string x2 x) eqn: H2.
    + apply eqb_string_true_iff in H1. apply eqb_string_true_iff in H2.
      rewrite<-H1 in H2. rewrite H2 in H. destruct H. reflexivity.
    + reflexivity.
  - destruct (eqb_string x2 x) eqn: H2.
    + reflexivity.
    + reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

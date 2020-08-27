Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.

(** * Basics *)
(*当用inductive定义数据类型时，Coq会自动为该类型生成'归纳法则'，如果t是归纳定义的，
那么对应的归纳法则被称作t_ind*)

Check nat_ind.
(*  ===> nat_ind :
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)
(*证明P n 对所有的n都成立，一个充分条件时证明，P 0成立;对任意n,若P n成立，那么P (S n)成立*)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  -  reflexivity.
  -  simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, optional (plus_one_r')  

    Complete this proof without using the [induction] tactic. *)

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n' IHn'. rewrite<-IHn'.  rewrite plus_comm. simpl. 
    reflexivity.
Qed.
(** [] *)

Inductive yesno : Type :=
  | yes
  | no.

Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(** **** Exercise: 1 star, standard, optional (rgb) *)

Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.
(* ===> rgb_ind : forall P : rgb -> Prop,
                  P red ->
                  P green ->
                  P blue ->
                  forall y:rgb, P y*)
(** [] *)


Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind.
(* ===> (modulo a little variable renaming)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist),
            P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(** **** Exercise: 1 star, standard, optional (natlist1)  

    Suppose we had written the above definition a little
   differently: *)

Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l : natlist1) (n : nat).

Check natlist1_ind.
(** Now what will the induction principle look like? 
  natlist1_ind:
    forall P: natlist1 -> Prop,
      P nnil ->
      (forall (l:natlist1)
        P l -> forall n: nat,P (nsnocl l n)) ->
      forall n : natlist1, P n
[] *)

(** **** Exercise: 1 star, standard, optional (byntree_ind)  *)
Inductive byntree : Type :=
 | bempty
 | bleaf (yn : yesno)
 | nbranch (yn : yesno) (t1 t2 : byntree).
Check byntree_ind.
(**
  byntree_ind:
    forall P: byntree -> Prop,
      P bempty ->
      (forall (yn: yesno), P(bleaf yn)) ->
      (forall (yn: yesno), (t1: byntree),
       P t1 -> forall Pt2 -> P(nbranch yn t1 t2))->
      forall b: byntree P b
[] *)

(** **** Exercise: 1 star, standard, optional (ex_set)  *)
(*
    Here is an induction principle for an inductively defined
    set.

      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e

    Give an [Inductive] definition of [ExSet]: *)
Inductive ExSet : Type :=
  |conl (b:bool)
  |con2 (n:nat) (e:ExSet).
(** [] *)

(* ################################################################# *)
(** * Polymorphism *)
Inductive list (X:Type) : Type :=
  |nil: list X
  |cons: X-> list X -> list X.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.
(** [] *)

(** **** Exercise: 1 star, standard, optional (mytype)  

    Find an inductive definition that gives rise to the
    following induction principle:

      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m
*) 
Inductive mytype (X:Type) : Type :=
  |constr1 (x: X)
  |constr2 (n:nat)
  |constr3 (m: mytype X) (n:nat).
Check mytype_ind.
(** [] *)

(** **** Exercise: 1 star, standard, optional (foo)  

    Find an inductive definition that gives rise to the
    following induction principle:

      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2
*) 
(** [] *)

(** **** Exercise: 1 star, standard, optional (foo')  

    Consider the following inductive definition: *)

Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.
Check foo'_ind.
(** What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)

     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    P f->
                    P( C1 l f) ) ->
             foo' C2 ->
             forall f : foo' X,  P f.
*)

(** [] *)

(* ################################################################# *)
(** * Induction Hypotheses *)

(** Where does the phrase "induction hypothesis" fit into this story?*)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

(** ... or equivalently: *)

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

(** Now it is easier to see where [P_m0r] appears in the proof. *)

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [| m'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity.  Qed.

(** **** Exercise: 1 star, standard, optional (plus_explicit_prop) *)
Theorem plus_assoc'' : forall n m o : nat,
  n+(m+o)=(n+m)+o.
Proof.
  intros.
  induction n as [| n'].
  -rewrite plus_O_n. rewrite plus_O_n. reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

(* ################################################################# *)
(** * Induction Principles in [Prop] *)

Check even_ind.

Theorem ev_ev' : forall n, even n -> even' n.
Proof.
  apply even_ind.
  - apply even'_0.
  - intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.
Inductive le1 :nat-> nat -> Prop :=
  |le1_n (n:nat): le1 n n
  |le1_S (n m:nat)(H: le1 n m): le1 n (S m).
(*观察可以发现，两个构造子中左侧的参数n始终是相同的，于是可将其整体定义为一个
"一般参数",于是有如下的定义*)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).
Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)

(* ################################################################# *)
(** * Formal vs. Informal Proofs by Induction *)
Check nat_ind.
Print nat_ind.
Lemma evenb_ev : forall (n:nat),
  evenb n= true -> even n.
Proof.
  induction n; intros.
  - apply ev_0.
  - destruct n.
    +simpl in H. inversion H.
    +simpl in H. apply ev_SS.
Abort.
(*在上边关于自然数的归纳证明中，步长为1，然而我们并不能用even S n' 推出even n'
故我们需要修改自然数的归纳法则，将步长修改为2*)
Definition nat_ind2:forall (P :nat-> Prop),
  P 0 -> 
  P 1 ->
  (forall (n:nat), P n-> P(S(S n))) ->
  forall n:nat, P n:=
     fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n:nat) :=match n with
        |0 =>P0
        |1 => P1
        |S (S n') => PSS n' (f n')
         end.
Lemma evenb_ev: forall (n:nat), evenb n =true -> even n.
Proof.
  intros.
  induction n as [| | n'] using nat_ind2.
  -apply ev_0.
  -simpl in H. inversion H.
  -simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.
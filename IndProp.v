(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).


Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [even]. *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  even (double n).
Proof.
  intros n.
  induction n.
  -simpl. apply ev_0.
  -simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)


Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with [destruct]. *)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intros Heq. rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)
Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)  

    Prove the following result using [inversion].  For extra practice,
    prove it using the inversion lemma. *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as[ | [m [Hnm Hev]]].
  -discriminate H.
  -apply S_injective in Hnm. apply S_injective in Hnm.
   rewrite<- Hnm in Hev. apply evSS_ev'.
   apply Hev.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (even5_nonsense)  

    Prove the following result using [inversion]. *)

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [ | n' E'].
  inversion E' as [ | n'' E''].
  inversion E'' as [ | n''' E'''].
Qed.
(** [] *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.


Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.


Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m E1 E2.
  induction E1 as [|n' E1' IH].
  -simpl. apply E2.
  -simpl. apply ev_SS. apply IH.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (even'_ev)  

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [even]: *)

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

(** Prove that this definition is logically equivalent to the old
    one.  (You may want to look at the previous theorem when you get
    to the induction step.) *)

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intros n. split.
  -intros H. induction H.
   +apply ev_0.
   +apply ev_SS. apply ev_0.
   +apply ev_sum. apply IHeven'1. apply IHeven'2.
  -intros H. induction H.
   +apply even'_0.
   +destruct (n=?0) eqn: H1.
    *apply eqb_eq in H1. rewrite H1. apply even'_2.
    *assert(H2: S(S n)=2+n). { reflexivity. }
     rewrite H2. apply even'_sum. apply even'_2. apply IHeven.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  

    Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Lemma ev_2: forall n m,
  even (n+n+m)-> even m.
Proof.
  intros n m H1.
  induction n.
  -simpl in H1. apply H1.
  -simpl in H1.
   assert(H2:n+S n = S n+n). {rewrite <- plus_comm. reflexivity. }
   rewrite H2 in H1. simpl in H1.
   inversion H1. apply IHn.
   apply H0.
Qed.
Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m H1 H2.
  assert(H3: even (n+(n+m))). {apply ev_sum. apply H2. apply H1. }
  rewrite plus_assoc in H3.
  apply ev_2 in H3.
  apply H3.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)  

    This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros n m p H1 H2.
  assert(H: even((n+m)+(n+p))). {apply ev_sum. apply H1. apply H2. }
  rewrite plus_assoc in H.
  assert(H3: n+m=m+n). {apply plus_comm. }
  assert(H4: m+n+n=n+n+m). {rewrite<-plus_assoc. apply plus_comm. }
  rewrite H3 in H. rewrite H4 in H.
  assert(H5: n+n+m+p=n+n+(m+p)). {rewrite plus_assoc. reflexivity. }
  rewrite H5 in H.
  apply ev_2 in H.
  apply H.
Qed.
  
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [even])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation)  

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

(* FILL IN HERE 

    [] *)
Inductive total_relation:nat->nat -> Prop:=
   |total_0_0: total_relation 0 0
   |total_n_m n m(H:total_relation n m): total_relation n (S m)
   |total_m_n n m(H:total_relation n m): total_relation (S n) m.

(** **** Exercise: 2 stars, standard, optional (empty_relation)  

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(* FILL IN HERE 

    [] *)
Inductive empty_relation:nat->nat->Prop:= .

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n']. 
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises)  

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  -apply H.
  -apply le_S in IHle. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  -apply le_n.
  -apply le_S. apply IHn.
Qed.
  

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  -reflexivity.
  -apply le_S. apply IHle.
Qed.
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  -apply le_n.
  -apply (le_trans n (S n)).
    +apply le_S. apply le_n.
    +apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  -rewrite<-plus_n_O. apply le_n.
  -rewrite->plus_comm. simpl. apply le_S. rewrite->plus_comm.
   apply IHb.
Qed.
Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1<= m /\ n2<=m.
Proof.
  intros n1 n2 m H.
  induction H.
  -split.
    +apply le_plus_l.
    +rewrite plus_comm. apply le_plus_l.
  -destruct IHle. split.
    +apply le_S in H0. apply H0.
    +apply le_S in H1. apply H1.
Qed.
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros n1 n2 m H1.
 rewrite plus_n_Sm in H1.
 split.
 -rewrite plus_comm in H1. simpl in H1. rewrite plus_comm in H1.
  apply (le_trans (S n1) (S(n1+n2))).
    +apply n_le_m__Sn_le_Sm. apply le_plus_l.
    +apply H1.
 -apply plus_le in H1. destruct H1.
  apply H0.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros n m H.
  apply (le_trans (S n) m).
  -apply H.
  -apply le_S. apply le_n.
Qed.
 
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n.
  -intros m H. apply O_le_n.
  -intros m H. destruct m eqn:eq1.
    +discriminate H.
    +apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
Qed. 

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  -intros. inversion H.
    +unfold leb. reflexivity.
  -intros. inversion H.
    +simpl. rewrite <-leb_refl. reflexivity.
    +destruct n.
      *unfold leb. reflexivity.
      *apply Sn_le_Sm__n_le_m in H. simpl. apply IHm in H.
        apply H.
Qed.
(** Hint: This one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_correct.
  apply (le_trans n m).
  -apply H1.
  -apply H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split.
  -apply leb_complete.
  -apply leb_correct.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, recommended (R_provability)  

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.


Example R_try1:R 1 1 2.
Proof. apply c2. apply c3. apply c1. Qed.
(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) :=None.

Definition fR : nat -> nat -> nat:= plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o.
  split.
  -intros H. induction H.
   +simpl. reflexivity.
   +simpl. apply injective_S. apply IHR.
   +unfold fR. rewrite plus_comm. simpl. apply injective_S.
    unfold fR in IHR. rewrite plus_comm in IHR. apply IHR.
   +simpl in IHR. apply S_injective in IHR. unfold fR in IHR.
    rewrite plus_comm in IHR. simpl in IHR. apply S_injective in IHR.
    unfold fR. rewrite plus_comm. apply IHR.
   +unfold fR. rewrite plus_comm. unfold fR in IHR. apply IHR.
  -generalize dependent n.
   generalize dependent o.
   induction m.
   +intros n. induction n.
    *intros. unfold fR in H. simpl in H. rewrite->H. apply c1.
    *intros. simpl in H. simpl in IHn. destruct n0.
      { discriminate H. }
      { apply S_injective in H. apply c3. apply IHn in H. apply H. }
   +intros n. induction n.
    *intros. simpl in H. discriminate H.
    *intros. apply c2. simpl in H. apply S_injective in H. apply IHm in H.
     apply H.
Qed.
(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence)**)

Inductive subseq {X:Type}: list X -> list X -> Prop :=
  |emp_l l : subseq [] l
  |ll1 x l1 l2(H:subseq l1 l2): subseq l1 (x::l2)
  |ll2 x l1 l2(H:subseq l1 l2): subseq (x::l1) (x::l2).

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l. induction l.
  -apply emp_l.
  -apply ll2. apply IHl.
Qed.
Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  -apply emp_l.
  -simpl. apply ll1. apply IHsubseq.
  -simpl. apply ll2. apply IHsubseq.
Qed.
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros.
  Abort.

Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.
Example R_try1: R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
Qed.
Example R_try2: R 1 [1;2;1;0].
Proof.
  apply c3. apply c2. apply c3. apply c3. apply c2. apply c2. apply c2. apply c1.
Qed.

(** * Case Study: Regular Expressions *)
Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).
Arguments EmptySet{T}.
Arguments EmptyStr{T}.
Arguments Char{T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** We can easily translate this informal definition into an
    [Inductive] one as follows: *)


Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

(** Again, for readability, we can also display this definition using
    inference-rule notation.  At the same time, let's introduce a more
    readable infix notation. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

Lemma quiz: forall T(s:list T), ~(s=~EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings
    [[1]] and [[2]] directly.  Since the goal mentions [[1; 2]]
    instead of [[1] ++ [2]], Coq wouldn't be able to figure out how to
    split the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** **** Exercise: 3 stars, standard (exp_match_ex1)**)
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H as [H1 | H2].
  -apply (MUnionL s re1 re2). apply H1.
  -apply (MUnionR re1 s re2). apply H2.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss.
  -unfold fold. apply MStar0.
  -simpl. apply MStarApp.
   + apply H. simpl. left. reflexivity.
   + apply IHss. simpl in H. intros. apply H. right. apply H0.
Qed.

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec)**)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2.
  split.
  -generalize dependent s1.
    induction s2.
    +Abort.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl. simpl in Hin. apply Hin.
  - apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - destruct Hin.
  - simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)  **)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool:=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => (re_not_empty re1)&&(re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1)||(re_not_empty re2)
  | Star re => true
  end.
Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  -intros H. induction re.
   +destruct H as [s H1]. inversion H1.
   +simpl. reflexivity.
   +reflexivity.
   +simpl. apply andb_true_iff. split.
    * apply IHre1. destruct H as [s H1]. exists s. Abort. 
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re'], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)
(**Que1**)
Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re.
  intros H.
  remember (Star re) as re'.
  revert re Heqre'. 
  induction H; intros.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split.
    +reflexivity.
    +intros. inversion H.
  - apply IHexp_match2 in Heqre'. destruct Heqre' as [ss [H1 H2]].
    exists (s1::ss).
    Abort.
(** [] *)

(** **** Exercise: 5 stars, advanced (pumping)  

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

(**(Que2')**)
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.
Lemma napp_star: forall T (m:nat)(s1 s2 : list T) (re : @reg_exp T),
  s1=~re->
  s2=~Star re ->
  napp m s1++s2=~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  -simpl. apply Hs2.
  -simpl. rewrite <- app_assoc.
    apply MStarApp.
    +apply Hs1.
    +apply IHm.
Qed.

Import Coq.omega.Omega.
Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  - simpl. omega.
  - simpl. intros. rewrite app_length in H.
    apply Nat.add_le_cases in H.
    destruct H as [H1 | H2].
    +apply IH1 in H1. destruct H1 as [ s3[s4 [s5  H1']]].
     destruct H1' as [H3 [H4 H5]].
     exists s3,s4,(s5++s2). split.
      * rewrite H3. rewrite app_assoc. rewrite app_assoc. rewrite app_assoc. reflexivity.
      *split.
       {apply H4. }
       {intros m. rewrite app_assoc. rewrite app_assoc.
        apply MApp.
         {rewrite<-app_assoc. apply H5. }
         {apply Hmatch2. }
       }
    +apply IH2 in H2. destruct H2 as [ s3[s4 [s5  H2']]].
     destruct H2' as [H3 [H4 H5]].
     exists (s1++s3),s4,s5. split.
      * rewrite H3. rewrite app_assoc. reflexivity.
      *split.
       {apply H4. }
       {intros m. rewrite<-app_assoc.
        apply MApp.
         {apply Hmatch1. } 
         {apply H5. }
       }
   -simpl. assert(H: pumping_constant re1 <= pumping_constant re1 +pumping_constant re2).
    {apply le_plus_l. }
    intros.
    assert(H':pumping_constant re1 <= length s1).
    {apply (le_trans (pumping_constant re1) (pumping_constant re1 +pumping_constant re2) (length s1)).
     -apply H.
     -apply H0. }
    apply IH in H'. destruct H' as [s2 [s3 [s4 [H1 [H2 H2']]]]].
    exists s2, s3, s4. split.
    +apply H1.
    +split.
     *apply H2.
     *intros m. apply MUnionL. apply H2'.
   -simpl. assert(H: pumping_constant re2 <= pumping_constant re1 +pumping_constant re2).
    {rewrite plus_comm. apply le_plus_l. }
    intros.
    assert(H':pumping_constant re2 <= length s2).
    {apply (le_trans (pumping_constant re2) (pumping_constant re1 +pumping_constant re2) (length s2)).
     -apply H.
     -apply H0. }
    apply IH in H'. destruct H' as [s1 [s3 [s4 [H1 [H2 H2']]]]].
    exists s1, s3, s4. split.
    +apply H1.
    +split.
     *apply H2.
     *intros m. apply MUnionR. apply H2'.
  -simpl. intros contra. inversion contra.
  -simpl. intros. rewrite app_length in H. simpl in IH2.
   destruct s1.
   +simpl in H. apply IH2 in H. simpl. destruct H as [s1 [s3 [s4 [H1 [H2 H2']]]]].
    exists s1, s3, s4. split.
    *apply H1.
    *split.
     {apply H2. }
     {apply H2'. }
   + exists [],(x::s1),s2. split.
    *simpl. reflexivity.
    *split.
      {unfold not. intros H1. inversion H1. }
      {intros m. simpl. apply star_app.
        -induction m.
         +simpl. apply MStar0.
         +remember (x::s1) as s1'.
          simpl. apply star_app.
            *apply MStar1. apply Hmatch1.
            *apply IHm.
        -apply Hmatch2.
      }
Qed.
End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (n =? m) eqn:H.
    + intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.


(** **** Exercise: 2 stars, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  -induction H.
   +intros. reflexivity.
   +intros. apply H in H0. inversion H0.
  -induction H.
   +intros. apply H.
   +intros H1. discriminate H1.
Qed.
(** [] *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, recommended (eqbP_practice) **)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Lemma zero_plus_zero: forall n m,
  n+m=0 -> m=0.
Proof.
  intros.
  rewrite plus_comm in H.
  destruct m.
  -reflexivity.
  -simpl in H. discriminate H.
Qed.
Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l H.
  induction l.
  -unfold not. intros. inversion H0.
  -simpl. destruct (eqbP x n) as [H1 | H1].
   +rewrite H1 in H. simpl in H. 
    assert(H2:(n=?n)=true). {apply eqb_eq. reflexivity. }
    rewrite H2 in H.  inversion H.
   +unfold not. intros. destruct H0 as [H2 | H3].
    *unfold not in H1. apply H1 in H2. apply  H2.
    *simpl in H.  apply zero_plus_zero in H. apply IHl in H.
     unfold not in H. apply H in H3. apply H3.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, recommended (nostutter_defn) **)

Definition chk_head {X:Type} (l:list X) (x: X):Prop :=
  match l with
  |[] => True
  |h::t => h<>x
end.
Inductive nostutter {X:Type} : list X -> Prop :=
  |no_empty: nostutter []
  |no_n_m m l(H1: nostutter l)(H2:chk_head l m): nostutter (m::l).
Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply eqb_false; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. 
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) **)
(**Que2**)
Inductive in_order_merge {X:Type}:list X -> list X -> list X -> Prop :=
  |emp_emp_emp: in_order_merge [] [] []
  |MergeL l1 l2 l x(H: in_order_merge l1 l2 l): in_order_merge (x::l1) l2 (x::l)
  |MergeR l1 l2 l x(H: in_order_merge l1 l2 l): in_order_merge l1 (x::l2) (x::l).
Theorem filter_test_eq_l1: forall X (l1 l2 l:list X) (test:X->bool),
  in_order_merge l1 l2 l ->
  (forall x, In x l1 ->test x =true)->
  (forall x, In x l2 ->test x =false)->
  filter test l=l1.
Proof.
  intros.
  induction H.
  -reflexivity.
  -simpl. rewrite H0.
   2:{ simpl. left. reflexivity. }
   assert (H1': forall x :X, In x l1 -> test x=true). { intros. apply H0. simpl. right. apply H2. }
   pose proof IHin_order_merge H1' H1.
   rewrite H2.
   reflexivity.
  -simpl. rewrite H1.
   2:{ simpl. left. reflexivity. }
   assert (H1': forall x: X, In x l2 -> test x=false). {intros. apply H1. simpl. right. apply H2. }
   pose proof IHin_order_merge H0 H1'.
   apply H2.
Qed.
(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* FILL IN HERE 

    [] *)

Theorem filter_behavior: forall X (l sl:list X)(test:X -> bool),
  subseq sl l ->
  forallb test sl= true ->
  length sl<=length (filter test l).
Proof.
  intros.
  induction H.
  -simpl. apply O_le_n.
  -simpl. destruct (test x).
   +simpl. apply (le_trans (length l1) (length (filter test l2)) (S(length (filter test l2)))).
    *apply IHsubseq in H0. apply H0.
    *apply le_S. apply le_n.
   +apply IHsubseq in H0. apply H0.
  -simpl. simpl in H0. apply andb_true_iff in H0. destruct H0 as [H1 H2].
   apply IHsubseq in H2. 
   rewrite H1. simpl.
   apply n_le_m__Sn_le_Sm.
   apply H2.
Qed.

(** **** Exercise: 4 stars, standard, optional (palindromes) **)
Inductive pal {X:Type}: list X->Prop :=
  |pal_emp: pal []
  |pal_one m: pal [m]
  |pal_add l m(H:pal l): pal ((m::l)++[m]).
Theorem pal_app_rev: forall X (l:list X),
   pal (l++rev l).
Proof.
  intros X l.
  induction l.
  -simpl. apply pal_emp.
  -simpl. rewrite app_assoc. apply (pal_add (l++rev l) x). apply IHl.
Qed.
Theorem pal_rev: forall X (l:list X),
  pal l ->
  l=rev l.
Proof.
  intros.
  induction H.
  -reflexivity.
  -reflexivity.
  -simpl. rewrite rev_app_distr. simpl. rewrite<-IHpal.
   reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)  
     forall l, l = rev l -> pal l.
*)

Theorem rev_pal :forall X (l:list X),
  l= rev l ->
  pal l.
Proof.
  intros.
  Abort.
(** **** Exercise: 4 stars, advanced, optional (NoDup) **)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)  **)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl in H. destruct H as [H1 | H2].
   +rewrite H1. exists [], l. simpl. reflexivity.
   +apply IHl in H2. destruct H2 as [l1 [l2 H3]].
    exists (x0::l1),l2.
    rewrite H3.
    reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  |repeats_start n l(H1: In n l) : repeats (n::l)
  |repeats_add n l (H2: repeats l) : repeats (n::l).

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   -intros. simpl in H1. inversion H1.
   -intros.
    assert(H2: (In x l1')\/ ~(In x l1')). { apply H. }
    destruct H2 as [Hl1 | Hl2].
    +Abort.
(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

Require Export Coq.Strings.Ascii.

Definition string := list ascii.

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)**)

Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
   intros.
   split.
   -intros. inversion H.
    destruct s1.
    +left. split.
      *apply H3.
      *apply H4.
    +right. exists s1,s2. split.
      *simpl in H1. inversion H1. reflexivity.
      *split.
       {inversion H1. rewrite H6 in H3. apply H3. }
       {apply H4. }
  -intros [H1 | H2].
   +destruct H1 as [H3 H4].
    *assert(H: []++(a::s)=a::s). {simpl. reflexivity. }
     rewrite<- H. apply MApp.
     apply H3. apply H4.
   +destruct H2 as [s0[s1 [H3 [H4 H5]]]].
    rewrite H3. 
     assert(H: (a::s0)++s1=a::s0++s1). {simpl. reflexivity. }
     rewrite<- H. apply MApp.
     apply H4. apply H5.
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)  **)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros. split.
  -intros. 
    remember (Star re) as re'.
    induction H.
    + discriminate Heqre'.
    + discriminate Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'. Abort.
  
(** [] *)

Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)  

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)  *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive) *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr) **)
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)  

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl) **)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Wed Jan 9 12:02:45 EST 2019 *)

(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.
Check 3 = 3.
(* ===> Prop *)
Check forall n m : nat, n + m = m + n.
(* ===> Prop *)
Check 2 = 2.
(* ===> Prop *)
Check forall n : nat, n = 2.
(* ===> Prop *)
Check 3 = 4.
(* ===> Prop *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(* ################################################################# *)
(** * Logical Connectives *)

(** ** Conjunction *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split;reflexivity.
Qed.
Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.
Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro;reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  split.
  -destruct n.
    +reflexivity.
    +discriminate H.
  -destruct m.
    +reflexivity.
    +destruct n.
      *simpl in H. discriminate H.
      *discriminate H.
Qed.
(** [] *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** Exercise: 1 star, standard, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q.
  intros [HP HQ].
  apply HQ.
Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP.  Qed.

(** **** Exercise: 2 stars, standard (and_assoc) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  -split.
    +apply HP.
    +apply HQ.
  -apply HR.
Qed.
(** [] *)
Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** Disjunction *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: 1 star, standard (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  destruct n.
  -left. reflexivity.
  - destruct m.
    +right. reflexivity.
    +intros H. simpl in H. discriminate H.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  -right. apply HP.
  -left. apply HQ.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation **)

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, standard, optional (not_implies_our_not)  

    Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H Q.
  unfold not in H.
  intros H1.
  apply H in H1.
  destruct H1.
Qed.
(** [] *)

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf)  

    Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_inf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H.
  unfold not.
  intros H1 H2.
  apply H in H2. apply H1 in H2.
  apply H2.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [HP nHP].
  apply nHP in HP.
  apply HP.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP)  

    Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.
(** [] *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)  

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P. split.
  -intros H. apply H.
  -intros H. apply H.
Qed.
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros [HP HQ1].
  intros [HQ2 HR].
  split.
  -intros H. apply HP in H. apply HQ2 in H. apply H.
  -intros H. apply HR in H. apply HQ1 in H. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  -intros [HP | [HQ HR]].
   +split.
     *left. apply HP.
     *left. apply HP.
   +split.
     *right. apply HQ.
     *right. apply HR.
  -intros [[HP1 | HQ] [HP2 | HR]].
   +left. apply HP1.
   +left. apply HP1.
   +left. apply HP2.
   +right. split.
    *apply HQ.
    *apply HR.
Qed.
(** [] *)

From Coq Require Import Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star, standard, recommended (dist_not_exists)  

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x H0].
  apply H0.
  apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (dist_exists_or)  

    Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  -intros H. destruct H as [x [HP | HQ]].
   +left. exists x. apply HP.
   +right. exists x. apply HQ.
  -intros H. destruct H as [HP | HQ].
   +destruct HP as [x PX].
    exists x. left. apply PX.
   +destruct HQ as [x QX].
    exists x. right. apply QX.
Qed.
(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].

    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars, standard (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  -induction l.
   +simpl. intros contra. destruct contra.
   +simpl. intros [H1 | H2].
    * exists x. split.
     {apply H1. }
     {left. reflexivity. }
    * apply IHl in H2. destruct H2 as [z [H3 H4]].
      exists z. split.
      {apply H3. }
      {right. apply H4. }
  -intros [x [H1 H2]].
   rewrite <- H1. apply In_map. apply H2.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (In_app_iff)  *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  -intros H. induction l.
    +simpl. simpl in H. right. apply H.
    +simpl. simpl in H. destruct H as [H1 | H2].
     *left. unfold In. left. apply H1.
     *apply IHl in H2. destruct H2 as [H3 | H4].
      {left. right. apply H3. }
      {right. apply H4. }
  -intros H. induction l.
    + simpl in H. destruct H.
      *destruct H.
      *simpl. apply H.
    + simpl in H. apply or_assoc in H. simpl. destruct H as [H1 | H2].
      *left. apply H1.
      *apply IHl in H2. right. apply H2.
Qed.
    
(** [] *)

(** **** Exercise: 3 stars, standard, recommended (All)  *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  |[] => True
  |h::t => (P h)/\(All P t)
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l .
  split.
  -intros H.
    induction l.
    +simpl. reflexivity.
    +simpl. simpl in H. split.
      *apply H. left. reflexivity.
      *apply IHl. intros y. intros H1. apply H. right. apply H1.
  -intros H.
    induction l.
     +intros y. intros H1. simpl in H1. destruct H1.
     +simpl. intros x0 H'.
      destruct H'.
      *simpl in H. destruct H as [H1 H2]. rewrite <- H0. apply H1.
      *simpl in H. destruct H as [H1 H2]. apply IHl. apply H2. apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (combine_odd_even) *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop:=
  fun (n:nat) => if oddb n then Podd n else Peven n.  

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n.
  destruct (oddb n) eqn:H0.
  -unfold combine_odd_even. rewrite H0. intros H1 H2.
   apply H1. reflexivity.
  -unfold combine_odd_even. rewrite H0. intros H1 H2.
   apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.
Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.


Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ################################################################# *)
(** * Coq vs. Set Theory *)
(* ================================================================= *)
(** ** Functional Extensionality *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 4 stars, standard (tr_rev_correct) *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_lemma : forall X  (l1 l2 : list X), 
  rev_append l1 l2 = (rev l1)++l2.
Proof.
  intros X l1.
  induction l1.
  -intros l2. simpl. reflexivity.
  -intros l2. simpl. rewrite <- app_assoc. simpl. apply IHl1.
Qed.
Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  unfold tr_rev.
  intros x.
  rewrite tr_rev_lemma.
  apply app_nil_r.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Propositions and Booleans *)

(** ... that [evenb n] evaluates to [true]... *)
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars, standard (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n.
  induction n.
  - simpl. exists 0. reflexivity.
  - destruct (evenb n) eqn: H.
    + rewrite evenb_S. rewrite H. simpl. destruct IHn as [k E]. exists k. rewrite E.
      reflexivity.
    + rewrite evenb_S. rewrite H. simpl. destruct IHn as [k E]. exists (S k). rewrite E.
      reflexivity.
Qed.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.
  
Example even_1000 : exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

(** In contrast, propositional negation may be more difficult
    to grasp. *)

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  -intros H. unfold andb in H. split.
    +destruct b1.
      *reflexivity.
      *destruct H. reflexivity.
    +destruct b2.
      *reflexivity.
      *destruct H. destruct b1.
        {reflexivity. }
        {reflexivity. }
  -intros [HA HB].
    unfold andb. rewrite HA.
    rewrite HB. reflexivity.
Qed.
Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  -intros H. destruct b1.
   + left. reflexivity.
   + simpl in H. right. apply H.
  -intros [HA | HB].
    +rewrite HA. reflexivity.
    +rewrite HB. destruct b1.
      *reflexivity.
      *reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq) *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H. unfold not. destruct (x=?y) eqn: H1.
    + discriminate H.
    + intros H2. rewrite H2 in H1. rewrite<- eqb_refl in H1. discriminate H1.
  - intros H. unfold not in H. destruct (x=?y) eqn: H1.
    +apply eqb_eq in H1. apply H in H1. destruct H1.
    +reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list) *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with 
  |[],[] =>true
  |[], h::t => false
  |h::t, [] => false
  |h1::t1, h2::t2 => match (eqb h1 h2) with
        |true => eqb_list eqb t1 t2
        |false => false
  end
end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb.
  intros H.
  split.
  -revert l2. induction l1.
    +intros l2. destruct l2 eqn: H1. 
      *reflexivity.
      *intros H2. discriminate H2.
    +simpl. intros l2. destruct l2 eqn: H3.
      *intros H4. discriminate H4.
      *destruct (eqb x x0) eqn:H6.
       {intros H5. apply H in H6. apply IHl1 in H5. rewrite H6. rewrite H5. reflexivity. } 
       {intros H5. discriminate H5. }
  Abort.

(** [] *)

(** **** Exercise: 2 stars, standard, recommended (All_forallb)  

    Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  -intros H. induction l.
    + reflexivity.
    + simpl. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHl in H2. 
      split.
      *apply H1.
      *apply H2.
  -intros H. induction l.
    + reflexivity.
    + simpl. simpl in H. destruct H as [H1 H2]. apply IHl in H2.
      apply andb_true_iff.
      split.
      *apply H1.
      *apply H2.
Qed.

(** Are there any important properties of the function [forallb] which
    are not captured by this specification? *)

(* FILL IN HERE 

    [] *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)
Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable) *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not.
  intros H1. apply H1.
  right. intros H2. apply H1. left. apply H2.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)*)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros e_m X P H x.
  unfold not in H.
  assert(H1: P x\/~P x). {apply e_m. }
  destruct H1 as [H3 | H4].
  - apply H3.
  - unfold not in H4. apply ex_falso_quodlibet. apply H.
    exists x. apply H4.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms) *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).


Lemma em_pe: excluded_middle->peirce.
Proof.
  intros em P Q.
  assert(H1: P\/~P). {apply em. }
  assert(H2: Q\/~Q). {apply em. }
  destruct H1 as [HP | nHP].
  -intros H'. apply HP.
  -intros. unfold not in nHP. destruct H2 as [HQ | nHQ].
    +assert(H': P->Q). {intros. apply HQ. }
    apply H in H'. apply H'.
    +assert(H': P->Q). {intros. apply nHP in H0. inversion H0. }
    apply H in H'. apply H'.
Qed.
   
Lemma pe_dne: peirce -> double_negation_elimination.
Proof.
  intros pe P nP.
  unfold not in nP.
  assert(H:((P->False)->P)->P). {apply pe. }
  apply H.
  intros H1.
  apply nP in H1.
  destruct H1.
Qed.
Lemma dne_dmnan: double_negation_elimination->de_morgan_not_and_not.
Proof. 
  intros dne P Q H.
  assert(H1:~~(P\/Q) ->(P\/Q)). {apply dne. }
  apply H1.
  unfold not. 
  unfold not in H.
  intros. apply H.
  split.
  -intros. assert(H': P\/Q). { left. apply H2. }
   apply H0 in H'. apply H'.
  -intros. assert(H': P\/Q). { right. apply H2. }
   apply H0 in H'. apply H'.
Qed.
Lemma dmnan_ito : de_morgan_not_and_not->implies_to_or.
Proof.
  intros dmnan P Q H.
  unfold not.
  assert(H1:~(~(P->False) /\ ~Q) ->(P->False)\/Q). {apply dmnan. }
  apply H1.
  unfold not.
  intros.
  destruct H0 as [H2 H3].
  apply H2. intros.
  apply H in H0.
  apply H3 in H0.
  apply H0.
Qed.
Lemma ito_em: implies_to_or ->excluded_middle.
Proof.
  intros ito. 
  unfold excluded_middle.
  intros P.
  assert(H:(P->P)-> (~P\/P)). {apply ito. }
  assert(H':P->P). {intro. apply H0. }
  apply H in H'.
  destruct H' as [H1 | H2].
  -right. apply H1.
  -left. apply H2.
Qed.
  
(* Wed Jan 9 12:02:45 EST 2019 *)

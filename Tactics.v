Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.

(* ################################################################# *)
(** * The [apply] Tactic *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.  Qed.


Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, standard, optional (silly_ex)  

    Complete the following proof without using [simpl]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
      evenb 4 = true ->
      oddb 3 = true.
Proof.
  intros eq1 eq2.
  apply eq1. apply eq2.
Qed.
(** [] *)


Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. 
  apply H.  Qed.

(** **** Exercise: 3 stars, standard (apply_exercise1)  

    (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H1.
  rewrite ->H1.
  symmetry.
  apply rev_involutive.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (apply_rewrite)  

    Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied? *)
(*
rewrite 是重写，而apply是应用定理
*)
(* ################################################################# *)

(** * The [apply with] Tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

(** **** Exercise: 3 stars, standard, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  -apply eq2.
  -apply eq1.
Qed.
  
(** [] *)

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

(** Here's a more interesting example that shows how [injection] can
    derive multiple equations at once. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. Qed.

(** **** Exercise: 1 star, standard (injection_ex3)  *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H2 as H3 H4.
  symmetry.
  apply H3.
Qed.
(** [] *)

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(** **** Exercise: 1 star, standard (discriminate_ex3)  *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H1.
  discriminate H1.
Qed.
(** [] *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.
      discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. injection eq as goal. apply goal. Qed.
      
(** **** Exercise: 2 stars, standard (eqb_true)  *)
Lemma injective_S : forall n m,
  n=m -> S n = S m.
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n as [|n' ].
  -simpl. intros m eq. destruct m.
    + reflexivity.
    + discriminate eq.
  -simpl. intros m eq. destruct m.
    + discriminate eq.
    + apply injective_S. apply IHn'. apply eq.
Qed.
(** [] *)

Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** **** Exercise: 3 stars, standard, recommended (plus_n_n_injective)  

    Practice using "in" variants in this proof.  (Hint: use
    [plus_n_Sm].) *)
  
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  -simpl. intros m eq. destruct m.
    + reflexivity.
    + discriminate eq.
  -simpl. intros m eq. destruct m.
    + discriminate eq.
    + apply f_equal. apply IHn'. simpl in eq. apply S_injective' in eq. 
      rewrite <- plus_n_Sm in eq.
      rewrite <- plus_n_Sm in eq.
      apply S_injective' in eq.
      apply eq.
Qed.
(** [] *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, recommended (gen_dep_practice)  

    Prove this by induction on [l]. *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  -simpl. intros n eq. destruct n.
    +reflexivity.
    +discriminate eq.
  -simpl. intros n eq. destruct n.
    +discriminate eq.
    +apply IHl. apply S_injective' in eq. rewrite -> eq. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Unfolding Definitions *)

Definition square n := n * n.

(** ... and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.

(** **** Exercise: 3 stars, standard, optional (combine_split)  

    Here is an implementation of the [split] function mentioned in
    chapter [Poly]: *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(** Prove that [split] and [combine] are inverses in the following
    sense: *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as[|x l].
  -intros l1 l2 H.
    simpl in H. injection H as H1 H2. rewrite <-H1. rewrite <- H2. reflexivity.
  -intros l1 l2 H.
    destruct x as [a b].
    simpl in H. 
    destruct (split l) as [lx ly].
    inversion H.
    simpl.
    assert(H': combine lx ly=l). { apply (IHl lx ly). reflexivity. }
    rewrite H'.
    reflexivity.
Qed.
  
(** [] *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        [eqn:] again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.  Qed.

(** **** Exercise: 2 stars, standard (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn:Bool.
  -destruct b eqn:Bool1.
    +rewrite -> Bool. rewrite -> Bool. reflexivity.
    + destruct (f true) eqn:Bool2.
      {rewrite-> Bool2. reflexivity. }
      {rewrite->Bool. reflexivity. }
  -destruct b eqn:flag.
    + destruct (f false) eqn:flag1.
      {rewrite ->Bool. reflexivity. }
      {rewrite ->flag1. reflexivity. }
    +rewrite -> Bool. rewrite -> Bool. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (eqb_sym)  *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (n=?m) eqn:flag.
  -apply eqb_true in flag. rewrite -> flag. rewrite <- eqb_refl. reflexivity. 
  -destruct (m=?n) eqn:flag1.
    + apply eqb_true in flag1. rewrite ->flag1 in flag. rewrite <- eqb_refl in flag. discriminate flag.
    +reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (eqb_sym_informal)  

    Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [(n =? m) = (m =? n)].

   Proof: *)
   (* FILL IN HERE 

    [] *)

(** **** Exercise: 3 stars, standard, optional (eqb_trans)  *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros  n m p H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  rewrite -> H2 in H1.
  rewrite -> H1.
  rewrite <- eqb_refl.
  reflexivity.
Qed.
 
(** [] *)

(** **** Exercise: 3 stars, advanced (split_combine)  *)

Definition split_combine_statement : Prop :=
  (* ("[: Prop]" means that we are giving a name to a
     logical proposition here.) *)
  forall( X Y:Type) (l1 :list X) (l2 :list Y),length l1 = length l2 -> split (combine l1 l2)=(l1,l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1.
  -intros l2.
    intros H.  destruct l2 eqn: H1.
    +reflexivity.
    +discriminate H.
  -intros l2.
    intros H. destruct l2 eqn: H1.
    +discriminate H.
    +simpl in H. apply S_injective in H. simpl. rewrite -> IHl1. reflexivity. apply H.
Qed.
(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise)  

    This one is a bit challenging.  Pay attention to the form of your
    induction hypothesis. *)

Lemma eq_len: forall (X:Type) (l1 l2: list X),
  l1=l2 -> length l1 =length l2.
Proof.
  intros X l1 l2.
  intros H.
  rewrite ->H.
  reflexivity.
Qed.
Lemma eq_empty: forall (X:Type) (test : X-> bool) (l :list X),
  length l=0 -> filter test l=[].
Proof.
  intros X test l.
  induction l.
  - reflexivity.
  - intros H. discriminate H.
Qed.
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf H.
  induction l as [|y l].
  -simpl in H.
   discriminate H.
  -simpl in H.
   destruct (test y) eqn:H1.
   +injection H as H2.
    rewrite -> H2 in H1.
    apply H1.
   +apply IHl.
    apply H.
Qed.
    
(** [] *)

(** **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge)  *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool:=
  match l with
  |nil =>true
  |h::l => match (test h) with
      |false =>false
      |true => forallb test l
  end
end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X-> bool) (l : list X) :bool:=
  match l with
  |nil => false
  |h::l => match (test h) with
      |true => true
      |false => existsb test l
  end
end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool:=
  negb( forallb (fun x:X =>negb(test x) ) l).

Lemma forall_existsb':forall (X :Type) (test : X -> bool)(x :X) (l :list X),
  test x =false ->
  existsb' test (x::l) = existsb' test l.
Proof.
  intros X test x l H.
  unfold existsb'.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [|y l].
  -reflexivity.
  -simpl. destruct (test y) eqn:H1.
    +unfold existsb'. simpl. rewrite H1.
    reflexivity.
    +symmetry. rewrite forall_existsb' with (X:=X) (test:=test) (x:=y) (l:=l).
      *symmetry;apply IHl.
      *apply H1.
Qed.
(** [] *)

(* Wed Jan 9 12:02:44 EST 2019 *)

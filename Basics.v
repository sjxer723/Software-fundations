Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.


Proof. simpl. reflexivity.  Qed.

Inductive bool : Type :=
  | true
  | false.


Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Notation] command defines a new
    symbolic notation for an existing definition. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.


(** **** Exercise: 1 star, standard (nandb)   *)
Definition ref (b1:bool): bool:=
  match b1 with
  |true => false
  |false => true
  end.
Definition nandb (b1:bool) (b2:bool):bool:=
   match b2 with
   |true =>ref b1
   |false =>true
   end.
Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (andb3)   *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool:=
    match b1 with
    |false =>false
    |true =>(andb b2 b3)
    end.
Example test_andb31: (andb3 true true true) = true.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
Example test_andb32:(andb3 false true true) = false.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
Example test_andb33:(andb3 true false true) = false.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
Example test_andb34:(andb3 true true false) = false.
(* FILL IN HERE *)Proof. simpl. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Types *)


Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)


Check negb.
(* ===> negb : bool -> bool *)

(* ================================================================= *)
(** ** New Types from Old *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.


Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.


(* ================================================================= *)
(** ** Tuples *)


Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).
(* ==> bits B1 B0 B1 B0 : nybble *)


Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

(* ================================================================= *)
(** ** Modules *)


Module NatPlayground.

(* ================================================================= *)
(** ** Numbers *)

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary decimal numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in decimal form by default: *)

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
  (* ===> 2 : nat *)

(** The constructor [S] has the type [nat -> nat], just like
    [pred] and functions like [minustwo]: *)

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).
Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(** (You will notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [reflexivity].  We'll see more about why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Adding three to two now gives us five, as we'd expect. *)

Compute (plus 3 2).

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** Exercise: 1 star, standard (factorial)  

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat:=
  match n with
    |O => S O
    |S n' =>mult n (factorial n')
  end.
Example test_factorial1:          (factorial 3) = 6.
   Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
   Proof. simpl. reflexivity. Qed.  
(** [] *)

(** Again, we can make numerical expressions easier to read and write
    by introducing notations for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

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

(** Similarly, the [leb] function tests whether its first argument is
    less than or equal to its second argument, yielding a boolean. *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** Since we'll be using these (especially [eqb]) a lot, let's give
    them infix notations. *)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3':             (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 1 star, standard (ltb)  

    The [ltb] function tests natural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined
    function.  (It can be done with just one previously defined
    function, but you can use two if you need to.) *)

Definition ltb (n m : nat) : bool:=(n<=?m)&&ref(n=?m).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
  Proof. simpl. reflexivity. Qed.
Example test_ltb2:             (ltb 2 4) = true.
  Proof. simpl. reflexivity. Qed.
Example test_ltb3:             (ltb 4 2) = false.
  Proof. simpl. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal. *)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** This theorem is a bit more interesting than the others we've
    seen: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.


(** **** Exercise: 1 star, standard (plus_id_exercise)  

    Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.
(** [] *)


Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 2 stars, standard (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H1.
  rewrite -> plus_1_l.
  rewrite <- H1.
  reflexivity. Qed.

  (* (N.b. This proof can actually be completed with tactics other than
     [rewrite], but please do use [rewrite] for the sake of the exercise.) 

    [] *)

(* ################################################################# *)
(** * Proof by Case Analysis *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.  
  - reflexivity.
  - reflexivity.  Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** If there are no arguments to name, we can just write [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (andb_true_elim2)  

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
   intros b c.
   intros H1.
Abort.  
(** [] *)

(** **** Exercise: 1 star, standard (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n. destruct n as [|n'] eqn:E.
  -reflexivity.
Abort.
(** [] *)

(* ================================================================= *)
(** ** More on Notation (Optional) *)

(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(* ================================================================= *)
(** ** Fixpoints and Structural Recursion (Optional) *)

(** Here is a copy of the definition of addition: *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.


(* ################################################################# *)
(** * More Exercises *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.  
  intros b. destruct b eqn: Eb.
  -rewrite -> H. rewrite ->H. reflexivity.
  -rewrite -> H. rewrite ->H. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (negation_fn_applied_twice)  

    Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x]. *)

Theorem negation_fn_applied_twice :
  forall (f :bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b :bool), f(f b)=b.
  
Proof.
  intros f.
  intros H.
  intros b. destruct b eqn: Eb.
  -rewrite -> H. simpl. rewrite ->H. reflexivity.
  -rewrite -> H. simpl. rewrite ->H. reflexivity.
Qed.
From Coq Require Export String.

(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (andb_eq_orb)   *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  -simpl. intros H. rewrite -> H. reflexivity.
  -simpl. intros H. rewrite -> H. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (binary) *)

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  |Z => B Z
  |A n => B n
  |B n => A (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  |Z => 0
  |A m' => 2*( bin_to_nat m')
  |B m' => 1+ 2* (bin_to_nat m')
  end.
Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. reflexivity. Qed.
Definition manual_grade_for_binary : option (nat*string) := None.
(** [] *)

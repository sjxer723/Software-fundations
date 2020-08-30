Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From LF Require Import Maps.

(* ################################################################# *)
(* ================================================================= *)
(** ** Syntax *)

Module AExp.
(*算术和布尔表达式*)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Evaluation *)
(** _Evaluating_ an arithmetic expression produces a number. *)

(*求值*)
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)
(*将0+e化简为e*)
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Coq Automation *)

(* ================================================================= *)
(** ** Tacticals *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Just [reflexivity] would have failed. *)
  apply HP. 
Qed.

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (Simple Form) *)

(** For example, consider the following trivial lemma: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (*除ANum和APlus两种情况以外*)
  - reflexivity.
  - destruct a1 eqn:Ea1;
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    +(*但ANum情况下，上述操作什么也没有进行,于是解构n*)
      destruct n eqn:En; simpl; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (General Form) *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** **** Exercise: 3 stars, standard (optimize_0plus_b_sound)  *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b' => b
  | BAnd b1 b2=> b
end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b.
  induction b; simpl;
  try (rewrite optimize_0plus_sound);
  try (rewrite optimize_0plus_sound);
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (optimize)  

    _Design exercise_  *)
Fixpoint optimize_0plus_mult (a:aexp) : aexp :=
  match a with
  |ANum n => ANum n
  |APlus (ANum 0) e2 => optimize_0plus_mult e2
  |APlus e1 e2 => APlus (optimize_0plus_mult e1) (optimize_0plus_mult e2)
  |AMinus e1 e2 => AMinus (optimize_0plus_mult e1) (optimize_0plus_mult e2)
  |AMult (ANum 0) e2 => ANum 0
  |AMult e1 e2 => AMult (optimize_0plus_mult e1) (optimize_0plus_mult e2)
end.

Theorem optimize_0plus_mult_sound: forall a,
  aeval (optimize_0plus_mult a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1 eqn:Ea1.
    + destruct n eqn:En.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - destruct a1 eqn:Ea2.
    + destruct n eqn:En.
      * simpl. reflexivity.
      * simpl. rewrite IHa2. reflexivity.
    +simpl. simpl in IHa1. rewrite IHa1.
     rewrite IHa2. reflexivity.
    +simpl. simpl in IHa1. rewrite IHa1.
     rewrite IHa2. reflexivity.
    +simpl. simpl in IHa1. rewrite IHa1.
     rewrite IHa2. reflexivity.
Qed.

(* ================================================================= *)
(** ** Defining New Tactic Notations *)
(*将多个策略封住成单条指令*)
(*接受策略c作为参数，等价于simpl;try c.*)
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(* ================================================================= *)
(** ** The [omega] Tactic *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(* ================================================================= *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: For a variable [x], find an assumption [x = e] or
       [e = x] in the context, replace [x] with [e] throughout the
       context and current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x] (where [x] is a variable).

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave like [apply
       H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c]. *)

(* ################################################################# *)
(** * Evaluation as a Relation *)


Module aevalR_first_try.

(*建立表达式与值之间的关系*)
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.

(* A small notational aside. We would previously have written the
   definition of [aevalR] like this, with explicit names for the
   hypotheses in each case: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

(** Instead, we've chosen to leave the hypotheses anonymous, just
    giving their types.  This style gives us less control over the
    names that Coq chooses during proofs involving [aevalR], but it
    makes the definition itself quite a bit lighter. *)

End TooHardToRead.

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(*可在aevalR自身内使用此记法,但在给出定义的同时声明它的意义*)
Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Inference Rule Notation *)

(** **** Exercise: 1 star, standard, optional (beval_rules)  

    Here, again, is the Coq definition of the [beval] function:

  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => (aeval a1) =? (aeval a2)
    | BLe a1 a2   => (aeval a1) <=? (aeval a2)
    | BNot b1     => negb (beval b1)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.
*)
(* Do not modify the following line: *)
Definition manual_grade_for_beval_rules : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Equivalence of the Definitions *)
Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H; induction H; subst; reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (bevalR)  

    Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval]. *)

Reserved Notation "e '\\\' n" (at level 90, left associativity).
Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : BTrue\\\true
  | E_BFalse : BFalse \\\ false
  | E_BEq (e1 e2: aexp) (n1 n2:nat):
      (e1\\ n1)-> (e2\\ n2)->(BEq e1 e2)\\\(n1=?n2)
  | E_BLe (e1 e2: aexp) (n1 n2:nat):
      (e1\\n1)->(e2\\n2)->(BLe e1 e2)\\\(n1<=?n2)
  | E_BNot (b1:bexp) (b2:bool):
      (b1\\\b2)-> (BNot b1)\\\(negb b2)
   |E_BAnd (b1 b2:bexp) (b3 b4:bool):
      (b1\\\b3)->
      (b2\\\b4)->
      (BAnd b1 b2)\\\(b3&&b4)
  where "e '\\\' b" := (bevalR e b) : type_scope.
Lemma aevalR_itself : forall a,
  a\\ aeval a.
Proof.
  intros.
  apply aeval_iff_aevalR';reflexivity.
Qed.
Lemma bevalR_itself : forall b,
  b\\\ beval b.
Proof.
  intros.
  induction b;simpl;
  try apply E_BTrue; try apply E_BFalse; 
  try apply E_BEq;try apply E_BLe; try apply E_BNot; try apply E_BAnd;
  try apply IHb; try apply IHb1; try apply IHb2;
  try apply aevalR_itself.
Qed.
Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros H; induction H;simpl;(try reflexivity);
    try apply aeval_iff_aevalR' in H;
    try apply aeval_iff_aevalR' in H0;
    subst; reflexivity.
  - intros H; simpl; induction H;try apply bevalR_itself.
Qed.
(** [] *)

End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

Module aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).   (* <--- NEW *)

Reserved Notation "e '\\' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).


Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny \\ n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) \\ n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.
(*函数定义和关系式定义各自的优点：
  关系式定义：1.更加优雅，容易理解
   2. Coq可以根据Inductive定义自动生成不错的反演函数和归纳法则
  函数定义：1.函数定义是确定性的，在所有参数上定义
  2.有了函数定义，我们可以利用Coq的计算机制在证明过程中简化表达式*)

(* ################################################################# *)
(** * Expressions With Variables *)

(* ================================================================= *)
(** ** States *)
(*状态表示程序执行中某一时刻所有变量的值*)
Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Declare Scope imp_scope.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.

Set Printing Coercions.

Print example_bexp.

Unset Printing Coercions.

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x        (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X <= 4))%imp
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)


(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c ::= SKIP | x ::= a | c ;; c | TEST b THEN c ELSE c FI
         | WHILE b DO c END

    (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's notation
    mechanism.  In particular, we use [TEST] to avoid conflicting with
    the [if] and [IF] notations from the standard library.) 
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE ~(Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END 
*)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

(**阶乘函数的形式化定义*)

Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

(* ================================================================= *)
(** ** Desugaring notations *)

Unset Printing Notations.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   CSeq (CAss Z X)
        (CSeq (CAss Y (S O))
              (CWhile (BNot (BEq Z O))
                      (CSeq (CAss Y (AMult Y Z))
                            (CAss Z (AMinus Z (S O))))))
        : com *)
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
(* ===>
   fact_in_coq =
   (Z ::= AId X;;
   Y ::= ANum 1;;
   WHILE ~ (AId Z = ANum 0) DO
     Y ::= AId Y * AId Z;;
     Z ::= AId Z - ANum 1
   END)%imp
       : com *)
Unset Printing Coercions.

(* ================================================================= *)
(** ** The [Locate] command *)

(* ----------------------------------------------------------------- *)
(** *** Finding notations *)

(** When faced with unknown notation, use [Locate] with a _string_
    containing one of its symbols to see its possible
    interpretations. *)
Locate "&&".
Locate ";;".
Locate "WHILE".

(* ----------------------------------------------------------------- *)
(** *** Finding identifiers *)
Locate aexp.
(* ===>
   Inductive Top.aexp
   Inductive Top.AExp.aexp
     (shorter name to refer to it in current context is AExp.aexp)
   Inductive Top.aevalR_division.aexp
     (shorter name to refer to it in current context is aevalR_division.aexp)
   Inductive Top.aevalR_extended.aexp
     (shorter name to refer to it in current context is aevalR_extended.aexp)
*)

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END)%imp.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

(* ################################################################# *)
(** * Evaluating Commands *)
(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.
Close Scope imp_scope.

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ SKIP ]=> st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   st =[ x := a1 ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                            (E_Seq)
                         st =[ c1;;c2 ]=> st''

                          beval st b1 = true
                           st =[ c1 ]=> st'
                ---------------------------------------                (E_IfTrue)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b1 = false
                           st =[ c2 ]=> st'
                ---------------------------------------               (E_IfFalse)
                st =[ TEST b1 THEN c1 ELSE c2 FI ]=> st'

                         beval st b = false
                    -----------------------------                  (E_WhileFalse)
                    st =[ WHILE b DO c END ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ WHILE b DO c END ]=> st''
                  --------------------------------                  (E_WhileTrue)
                  st  =[ WHILE b DO c END ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').


Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (ceval_example2)  *)
Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X!->0).
  -apply E_Ass. reflexivity.
  -apply E_Seq with (Y!->1; X!->0).
   +apply E_Ass. reflexivity.
   +apply E_Ass. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (pup_to_n)  *)

Definition pup_to_n : com:=
   (SKIP;;
  Y ::= 0;;
  WHILE ~(X = 0) DO
    Y ::= Y + X;;
    X ::= X - 1
  END)%imp.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n.
  apply E_Seq with (X!->2).
  - apply E_Skip.
  - apply E_Seq with (Y!->0;X!->2).
   +apply E_Ass. reflexivity.
   +apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
    *reflexivity.
    *apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2).
      {apply E_Ass. reflexivity. }
      {apply E_Ass. reflexivity. }
    *apply E_WhileTrue with (X !-> 0 ; Y !-> 3 ;X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
      {reflexivity. }
      {apply E_Seq with (Y !-> 3 ;X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
        {apply E_Ass. reflexivity. }
        {apply E_Ass. reflexivity. }
      }
      {apply E_WhileFalse.
        simpl. reflexivity. }
Qed.


(* ================================================================= *)
(** ** Determinism of Evaluation *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. discriminate H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. discriminate H4.
  - (* E_WhileTrue, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 3 stars, standard, recommended (XtimesYinZ_spec)  

    State and prove a specification of [XtimesYinZ]. *)
Theorem XtimesYinZ_spec : forall st st' n1 n2,
  st X =n1 ->
  st Y =n2 ->
  st =[XtimesYinZ]=>st' ->
  st' Z =n1*n2.
Proof.
  intros.
  inversion H1.
  subst. clear H1. simpl.
  apply t_update_eq.
Qed.
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef
           eqn:Heqloopdef.
Abort.
(** [] *)

(** **** Exercise: 3 stars, standard (no_whiles_eqv)  

    Consider the following function: *)

Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.
Close Scope imp_scope.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
  | N_Skip: no_whilesR SKIP
  | N_Ass(x: string) (a: aexp): no_whilesR (x::=a)
  | N_Seq (c1 c2:com)
    (H1: no_whilesR c1) (H2: no_whilesR c2):no_whilesR (c1;; c2)
  | N_If (b:bexp) (c1 c2:com) 
    (H1: no_whilesR c1) (H2: no_whilesR c2):
    no_whilesR (TEST b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros.
  split.
  -intros. induction c.
   +apply N_Skip.
   +apply N_Ass.
   +apply N_Seq. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
    *apply IHc1 in H1. apply H1. 
    *simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHc2 in H2. apply H2.
   +apply N_If. simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
    *apply IHc1 in H1. apply H1.
    *simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHc2 in H2. apply H2.
   +simpl in H. inversion H.
  -intros. induction H.
   +reflexivity.
   +reflexivity.
   +simpl. apply andb_true_iff. split.
    *apply IHno_whilesR1.
    *apply IHno_whilesR2.
   +simpl. apply andb_true_iff. split.
    *apply IHno_whilesR1.
    *apply IHno_whilesR2.
Qed.
(**  [] *)

(** **** Exercise: 4 stars, standard (no_whiles_terminating)  . *)


Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (stack_compiler)**)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  |[] => stack
  |h::t => match h with
    |SPush n => s_execute st (n::stack) t
    |SLoad x => s_execute st ((aeval st x)::stack) t
    |SPlus => match stack with 
      |h1::h2::t1 => s_execute st ((h1+h2)::t1) t
      |_ => stack
      end
    |SMinus => match stack with
      |h1::h2::t1 => s_execute st ((h2-h1)::t1) t
      |_ => stack
      end
    |SMult => match stack with
      |h1::h2::t1 => s_execute st ((h1*h2)::t1) t
      |_ => stack
      end
  end
end.
Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. simpl. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. simpl. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr:=
   match e with
    |ANum n => [SPush n]
    |AId x => [SLoad x]               
    |APlus a1 a2 => (s_compile a1)++(s_compile a2)++[SPlus]
    |AMinus a1 a2 => (s_compile a1)++(s_compile a2)++[SMinus]
    |AMult a1 a2 =>(s_compile a1)++(s_compile a2)++[SMult]
end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
  s_compile (X - (2 * Y))%imp
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. simpl. reflexivity. Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (stack_compiler_correct) *)
Lemma s_compile_app: forall st stack prog1 prog2,
  s_execute st stack (prog1++prog2)= s_execute st (s_execute st stack prog1) prog2.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  induction prog1.
  -simpl. reflexivity.
  -Admitted.
Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  induction e.
  -reflexivity.
  -reflexivity.
  -simpl. rewrite s_compile_app. rewrite IHe1. 
  rewrite s_compile_app. Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (short_circuit)  *)
Fixpoint beval' (st: state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  =>
      match (beval st b1) with
      |true => (beval st b2)
      |false => false
  end
end.

Module BreakImp.
(** **** Exercise: 4 stars, advanced (break_imp) *)
Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, st' at next level).

(** Based on the above description, complete the definition of the
    [ceval] relation. *)
Reserved Notation "st '=[' c ']=>' st' '/'s"
  (at level 40, st' at next level).
Inductive ceval : com -> state -> result ->state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st / SContinue
  | E_Break :forall st,
      st =[ BREAK]=> st/ SBreak
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[x ::= a1]=> (x !-> n ; st) /SContinue
  | E_Seq1 : forall c1 c2 st st' ,
      st  =[c1]=> st'/SBreak ->
      st  =[c1 ;; c2]=> st'/SBreak
  | E_Seq2 : forall c1 c2 st st' st'' (res:result),
      st=[c1]=> st'/SContinue ->
      st'=[c2]=> st''/res ->
      st=[c1;;c2]=> st''/res
  | E_IfTrue : forall st st' b c1 c2 res,
      beval st b = true ->
      st =[ c1 ]=> st'/res ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'/res
  | E_IfFalse : forall st st' b c1 c2 res,
      beval st b = false ->
      st =[ c2 ]=> st'/res ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'/res
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st/SContinue
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st'/SContinue ->
      st' =[ WHILE b DO c END ]=> st''/SContinue ->
      st  =[ WHILE b DO c END ]=> st''/SContinue
  | E_WhileBreak : forall st st' b c,
      beval st b =true ->
      st =[c]=> st'/SBreak ->
      st =[WHILE b DO c END ]=> st'/SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     st =[ BREAK;; c ]=> st' / s ->
     st = st'.
Proof.
  intros.
  inversion H.
  -subst. inversion H5. reflexivity.
  -subst. inversion H2.
Qed.

Theorem while_continue : forall b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s ->
  s = SContinue.
Proof.
  intros.
  inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
  intros.
  apply E_WhileBreak;try apply H;try apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  st =[ WHILE b DO c END ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
  remember (WHILE b DO c END) as loop.
  induction H;try inversion Heqloop;subst.
  -rewrite H in H0. inversion H0.
  -apply IHceval2;try reflexivity;try apply H0.
  -exists st. apply H1.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros.
  generalize dependent st2.
  generalize dependent s2.
  induction H;subst.
   -intros. split;inversion H0;reflexivity.
   -intros; split; inversion H0;subst;reflexivity.
   -intros; split; inversion H0;subst;reflexivity.
   -intros. inversion H0;subst.
    +apply IHceval with (s2:=SBreak). inversion H0.
     {apply H4. }
     {apply H6. }
    +assert(H': st'=st'0/\SBreak=SContinue). {apply IHceval with (s2:=SContinue).
     apply H3.
     }
     destruct H' as [H1 H2].
     inversion H2.
   -intros. inversion H1;subst.
    +assert(H': st'=st2/\SContinue=SBreak). { apply IHceval1 with (s2:=SBreak).
    apply H7. }
    destruct H' as [H1' H2].
    inversion H2.
    +apply IHceval2. 
     assert(H': st'=st'0/\SContinue=SContinue). {apply IHceval1 with (s2:=SContinue).
    apply H4. }
    destruct H' as [H1' H2].
    subst. apply H8.
   -intros. inversion H1;subst.
    +apply IHceval with (s2:=s2) (st2:=st2). apply H9.
    +rewrite H in H8. inversion H8.
   -intros. inversion H1;subst.
    +rewrite H in H8. inversion H8.
    +apply IHceval with (s2:=s2) (st2:=st2). apply H9.
   -intros. inversion H0.
    +split;reflexivity.
    +rewrite H in H3; inversion H3.
    +rewrite H in H3; inversion H3.
   -intros. inversion H2;subst.
     +rewrite H in H8. inversion H8.
     +apply IHceval2.
      assert(H':st'=st'0/\SContinue=SContinue). { apply IHceval1 with (st2:= st'0).
      apply H6. }
      destruct H' as [H1' H2'];subst.
      apply H10.
     +apply IHceval2.
      assert(H':st'=st2/\SContinue=SBreak). { apply IHceval1 with (s2:=SBreak).
      apply H9. }
      destruct H' as [H1' H2'].
      inversion H2'.
    -intros. inversion H1;subst.
      +rewrite H in H7. inversion H7.
      +assert(H': st'=st'0/\SBreak=SContinue). { apply IHceval with (s2:=SContinue) (st2:=st'0).
        apply H5. }
        destruct H' as [H1' H2'].
        inversion H2'.
      +assert(H': st'=st2/\SBreak=SBreak). { apply IHceval with (s2:=SBreak). apply H8. }
       destruct H' as [H1' H2'].
       split;try apply H1';try reflexivity.
Qed.
(** [] *)
End BreakImp.

(** **** Exercise: 4 stars, standard, optional (add_for_loop) **)
Module forloop.
Inductive com : Type :=
  | C_Skip        
  | C_Ass (x : string) (a : aexp)
  | C_Seq (c1 c2 : com)
  | C_If (b : bexp) (c1 c2 : com)
  | C_While (b : bexp) (c : com)
  | C_For (c1 c2 c3:com) (b:bexp).


Notation "'SKIP'" :=
   C_Skip.
Notation "x '::=' a" :=
  (C_Ass x a) (at level 60).
Notation "c1 ;; c2" :=
  (C_Seq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (C_While b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (C_If c1 c2 c3) (at level 80, right associativity).
Notation "'FOR' '(' c1 ';' b ';' c2 ')' 'DO' c3 'END'" :=
  (C_For c1 c2 c3 b)(at level 80, right associativity).

Reserved Notation "st '=[' c ']=>' st' '/'s"
  (at level 40, st' at next level).
Inductive cval: state -> com -> state -> Prop :=
  | F_Skip: forall st, 
     st =[ SKIP ]=> st
  | F_Ass: forall x a st, 
     st =[ x::= a ]=> (x !-> (aeval st a); st)
  | F_Seq: forall c1 c2 st st' st'', 
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st''->
      st =[ c1;; c2 ]=> st''
  | F_IfTrue: forall b c1 c2 st st', 
       beval st b = true ->
       st =[ c1 ]=> st' ->
       st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | F_IfFalse: forall b c1 c2 st st',
       beval st b = false -> 
       st =[ c2 ]=> st' -> 
       st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | F_WhileFalse: forall b c st, 
       beval st b = false ->
       st =[ WHILE b DO c END ]=> st
  | F_WhileTrue: forall b c st st' st'',
       beval st b = true -> 
       st =[ c ]=> st' ->
       st' =[ WHILE b DO c END ]=> st'' -> st =[ WHILE b DO c END ]=> st''
  | F_For: forall b c1 c2 c3 st st' st'', 
       st =[ c1]=> st' ->
       st'=[ WHILE b DO c3 ;; c2 END ]=> st'' ->
       st =[ FOR ( c1; b; c2 ) DO c3 END ]=> st' 
where "st '=[' c ']=>' st'" := (cval st c st').
End forloop.
(* Wed Jan 9 12:02:46 EST 2019 *)

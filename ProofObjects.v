(** * ProofObjects: The Curry-Howard Correspondence *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Print even.
(* ==>
  Inductive even : nat -> Prop :=
    | ev_0 : even 0
    | ev_SS : forall n, even n -> even (S (S n)).
*)
(*柯里-霍华德同构：既在类型层面表达具有什么类型，又在命题层面上表示式什么的证明*)

Check ev_SS.
(* ===> ev_SS : forall n,
                  even n ->
                  even (S (S n)) *)
(*ev_SS构造子表示接受两个参数-数字n以及命题ev n的证明，产生ev(S (S n))的证明*)

Theorem ev_4 : even 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4.

(** Indeed, we can also write down this proof object _directly_,
    without the need for a separate proof script: *)

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(* ################################################################# *)
(** * Proof Scripts *)

Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(*策略证明并不是必要的，可手动构造想要的证据，通过Definition直接给证据一个全局名称*)
Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(**构造方式虽然不同，但是存储在全局环境中的证明是一致的*)

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : even 4 *)

(** **** Exercise: 2 stars, standard (eight_is_even)  

    Give a tactic proof and a proof object showing that [even 8]. *)

Theorem ev_8 : even 8.
Proof.
  apply (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).
Qed.

Definition ev_8' : even 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).
(** [] *)

(* ################################################################# *)
Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, even n -> even (4 + n) :=
  fun (n : nat) => fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.
(* ===>
     : forall n : nat, even n -> even (4 + n) *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : even n), even (n + 2).
(*该例子中，forall时并没有依赖，可以简写成->，我们没有必要给箭头左边的类型一个名字*)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : even n), even (n + 2).

(** Or, equivalently, we can write it in more familiar notation: *)

Definition ev_plus2'' : Prop :=
  forall n, even n -> even (n + 2).

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ################################################################# *)
(** * Programming with Tactics *)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.
(*使用Defined而不是Qed来终止证明，它可以在计算中就像正常定义的函数一样被使用,而通过Qed定义的对象
在计算中是不透明的*)

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.
(*split策略能用于所有只有一个构造子*)

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** **** Exercise: 2 stars, standard, optional (conj_fact) *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun( P Q R:Prop) => fun(H1 : P/\Q) => fun(H2 :Q/\R) =>
  match H1,H2 with
  |conj p q,conj q' r => conj p r
  end.
(** [] *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

End Or.

(** **** Exercise: 2 stars, standard, optional (or_commut'') *)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun(P Q:Prop) => fun(H: P\/Q) =>
  match H with
  |or_introl P=> or_intror P
  |or_intror Q=> or_introl Q
end.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => even n).
(* ===> exists n : nat, even n
        : Prop *)

Definition some_nat_is_even : exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** Exercise: 2 stars, standard, optional (ex_ev_Sn) *)

Definition ex_ev_Sn : ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (ev_SS 0 (ev_0)).
(** [] *)

Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .

End Props.

(* ################################################################# *)
(** * Equality *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

(** **** Exercise: 2 stars, standard (equality__leibniz_equality) *)
(*相等的归纳定义蕴含了Leibniez相等关系*)
Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
  intros.
  inversion H.
  rewrite H2 in H0.
  apply H0.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (leibniz_equality__equality)  *)
Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
  intros.
  assert(H1: x=x -> x=y). {apply H. }
  assert(H2: x=x). {reflexivity. }
  assert(H3: x=y). {apply H1 in H2. apply H2. }
  subst.
  apply eq_refl.
Qed.
(** [] *)

End MyEquality.

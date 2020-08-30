From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
From LF Require Import Imp Maps.

(** Here was our first try at an evaluation function for commands,
    omitting [WHILE]. *)

Open Scope imp_scope.
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        (l !-> aeval st a1 ; st)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st  (* bogus *)
  end.
Close Scope imp_scope.
(*然而这样的定义不会被Coq接受，因为任何有可能不会停机的函数都会被Coq拒绝*)
(*一个改进技巧是将一个附加参数传入求值函数中来告诉它要运行多久*)
Open Scope imp_scope.
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.
Close Scope imp_scope.

(*为了区分正常停机和异常停机,将返回参数由state替换为option state*)
Open Scope imp_scope.
Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.
Close Scope imp_scope.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Compute
     (test_ceval empty_st
         (X ::= 2;;
          TEST (X <= 1)
            THEN Y ::= 3
            ELSE Z ::= 4
          FI)).
(*   ====>
      Some (2, 0, 4)   *)

(** **** Exercise: 2 stars, standard, recommended (pup_to_n)  

    Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)

Definition pup_to_n : com :=
   (X ::= X;;
    WHILE ~(X = 0)
    DO Y ::=Y+X;;
       X ::= X-1
    END).
    
Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.


(** **** Exercise: 2 stars, standard, optional (peven)  *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.
Definition evenb_or_not : com :=
   (X ::= X;;
   WHILE ~(X <= 2)
    DO X ::= X-2
    END;;
    TEST (X=0)
        THEN Z ::= 0
        ELSE Z ::= 1
    FI).

Example pup_to_n_2 :
  test_ceval (X !-> 5) evenb_or_not
  = Some (1, 0, 1).
Proof. reflexivity. Qed.


(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.

      + (* ;; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.

      + (* TEST *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1. intros H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_ceval_step__ceval_inf : option (nat*string) := None.
(** [] *)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        discriminate Hceval.

    + (* TEST *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. discriminate Hceval.  Qed.

(** **** Exercise: 3 stars, standard, recommended (ceval__ceval_step) *)

Lemma i1_leq_i1i2 :forall i1 i2,
  i1<=i1+i2.
Proof.
  induction i2.
  -rewrite<-plus_n_O. reflexivity.
  -rewrite plus_comm. simpl. apply le_S. rewrite plus_comm. apply IHi2.
Qed.
Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  -exists 1. reflexivity.
  -exists 1. simpl;rewrite H; reflexivity.
  -destruct IHHce1 as [i1 H1]. destruct IHHce2 as [i2 H2].
   exists (1+i1+i2). simpl.  
   destruct (ceval_step st c1 (i1 + i2)) eqn: Heqst1.
   +assert (H1': ceval_step st c1 (i1+i2) =Some st'). {
    apply ceval_step_more with (i1:=i1) (i2:= i1+i2).
    *apply i1_leq_i1i2.
    *apply H1. }
    assert (H': s=st'). { rewrite Heqst1 in H1'. 
     inversion H1'. reflexivity. }
     subst.
    apply(ceval_step_more i2 (i1+i2)).
     *rewrite plus_comm. apply i1_leq_i1i2.
     *apply H2.
   +assert (H1': ceval_step st c1 (i1+i2) =Some st'). {
    apply ceval_step_more with (i1:=i1) (i2:= i1+i2).
    *apply i1_leq_i1i2.
    *apply H1. }
    rewrite H1' in Heqst1. inversion Heqst1.
  -destruct IHHce as [i H1]. exists (1+i). simpl.
   rewrite H. apply H1.
  -destruct IHHce as [i H1]. exists (1+i). simpl.
   rewrite H. apply H1.
  -exists 1. simpl. rewrite H. reflexivity.
  -destruct IHHce1 as [i1 H1]. destruct IHHce2 as [i2 H2].
   exists (1+i1+i2). simpl.
   rewrite H.
   assert (H1': ceval_step st c (i1+i2) =Some st'). {
    apply ceval_step_more with (i1:=i1) (i2:= i1+i2).
    *apply i1_leq_i1i2.
    *apply H1. }
   rewrite H1'.
   rewrite plus_comm.
   apply (ceval_step_more i2 (i2+i1)) . 
    *apply i1_leq_i1i2.
    *apply H2.
Qed. 
Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ################################################################# *)
(** * Determinism of Evaluation Again *)

Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.  Qed.

(* Wed Jan 9 12:02:46 EST 2019 *)

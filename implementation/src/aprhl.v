

From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Snapv
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis ErrorBounds
     IntervalArithQ  TypeValidator.

From Snapv
     Require Import Command CommandSemantics.

From Snapv 
    Require Import Hoare Imp Maps.
From Snapv.aprhl Require Import Extra Prob.

(* ################################################################# *)
(** * Definitions *)
Definition Assertion := state -> Prop.

Inductive hoare_rule : Assertion -> command -> R -> command -> Assertion -> Prop :=
  | H_Skip  P:
      hoare_proof P (SKIP) 0 (SKIP) P
  | H_Asgn Q x1 a1 x2 a2 :,
      hoare_proof (assn_sub x1 x2 a1 a2 Q) (ASGN (Var R x1) a1) 0 (ASGN (Var R x12) a2) Q
  | H_Seq  P c1 c2 Q d1 d2 R r1 r2:
      hoare_proof P c1 r1 d1 Q -> hoare_proof Q c2 r2 d2 R 
    -> hoare_proof P (SEQ c1 c2) (r1 + r2) (SEQ d1 d2) R
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q
  | H_UnifP x1 x2 eps:
hoare_proof True (UNIF1 (Var R x1)) eps (UNIF1 (Var R x2))
 (forall l r, l < x1 < r -> eps * l < x2 < eps * r)
  | H_UnifN x1 x2 eps:
hoare_proof True (UNIF1 (Var R x1)) eps (UNIF1 (Var R x2))
 (forall l r, l < x1 < r -> (-eps * l) < x2 < (-eps * r))
  | H_Null  x1 x2 eps:
hoare_proof True (UNIF2 (Var R x1)) 0 (UNIF2 (Var R x2))
 ( x1 =  x2 )
    .



Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X.  apply H.  intros. apply H0. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.
Proof.
  intros. eapply H_Consequence.
    apply X. intros. apply H0.  apply H. Qed.



Example sample_proof :
  hoare_proof
    ((fun st:state => st X = 3) [X |-> X + 2] [X |-> X + 1])
    (X ::= X + 1;; X ::= X + 2)
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq; apply H_Asgn.
Qed.



Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *)
intros.
induction X; subst.
- apply hoare_skip.
- apply hoare_asgn.
- apply hoare_seq with Q; try assumption.
- apply hoare_if; try assumption.
- apply hoare_while; try assumption.
- apply hoare_consequence with P' Q'; try assumption.
Qed.


Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  induction c; intro P.
  - (* SKIP *)
    eapply H_Consequence.
    apply H_Skip.
    intros. apply H.
    (* Proof of True *)
    intros. apply I.
  - (* ::= *)
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  - (* ;; *)
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ => True)).
    apply IHc2.
    intros. apply I.
  - (* IFB *)
    apply H_Consequence_pre with (fun _ => True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  - (* WHILE *)
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

(** Similarly, we can show that [{{False}} c {{Q}}] is provable for
    any [c] and [Q]. *)

Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  intros P Q [CONTRA HP].
  inversion CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  induction c; intro Q.
  - (* SKIP *) pre_false_helper H_Skip.
  - (* ::= *) pre_false_helper H_Asgn.
  - (* ;; *) pre_false_helper H_Seq. apply IHc1. apply IHc2.
  - (* IFB *)
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  - (* WHILE *)
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.


Definition wp (c:com) (Q:Assertion) : Assertion :=
  fun s => forall s', c / s \\ s' -> Q s'.

(** **** Exercise: 1 star (wp_is_precondition)  *)

Lemma wp_is_precondition: forall c Q,
  {{wp c Q}} c {{Q}}.
(* FILL IN HERE *) 
Proof.
intros. unfold wp.
induction c; subst; try assumption.
- eapply hoare_consequence.
+ apply hoare_skip.
+ intros H S. apply S. apply E_Skip.
+ intros H S. apply S.
- eapply hoare_consequence_pre.
+ apply hoare_asgn.
+ intros H S. apply S. apply E_Ass. reflexivity.
- eapply hoare_consequence_pre; try assumption.
 { eapply hoare_seq. apply IHc2. unfold hoare_triple; intros. apply IHc1 in H.
 apply H in H0. apply IHc2 in H1. apply H1. Admitted.

(** [] *)

(** **** Exercise: 1 star (wp_is_weakest)  *)

Lemma wp_is_weakest: forall c Q P',
   {{P'}} c {{Q}} -> forall st, P' st -> wp c Q st.
(* FILL IN HERE *)
Proof.
intros. Admitted.

(** The following utility lemma will also be useful. *)

Lemma bassn_eval_false : forall b st, ~ bassn b st -> beval st b = false.
Proof.
  intros b st H. unfold bassn in H. destruct (beval st b).
    exfalso. apply H. reflexivity.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars (hoare_proof_complete)  *)
(** Complete the proof of the theorem. *)

Theorem hoare_proof_complete: forall P c Q,
  {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q HT.
  - (* SKIP *)
    eapply H_Consequence.
     eapply H_Skip.
      intros.  eassumption.
      intro st. apply HT.  apply E_Skip.
  - (* ::= *)
    eapply H_Consequence.
      eapply H_Asgn.
      intro st. apply HT. econstructor. reflexivity.
      intros; assumption.
  - (* ;; *)
    apply H_Seq with (wp c2 Q).
     eapply IHc1.
       intros st st' E1 H. unfold wp. intros st'' E2.
         eapply HT. econstructor; eassumption. assumption.
     eapply IHc2. intros st st' E1 H. apply H; assumption.
  (* FILL IN HERE *) Admitted.
(** [] *)

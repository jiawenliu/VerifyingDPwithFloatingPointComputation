(**
Environment library.
Defines the environment type for the Flover framework and a simulation relation
between environments.
 **)
From Coq
     Require Import Reals.Reals micromega.Psatz QArith.Qreals.

From Snapv
     Require Import Infra.ExpressionAbbrevs Infra.RationalSimps.

(**
Define an approximation relation between two environments.
We use this relation for the soundness proofs.
It is necessary to have this relation, since two evaluations of the very same
exprression may yield different values for different machine epsilons
(or environments that already only approximate each other)
 **)
Inductive approxEnv : env -> (expr R -> option mType) -> analysisResult -> NatSet.t
                      -> NatSet.t -> env -> Prop :=
|approxRefl Gamma A:
   approxEnv emptyEnv Gamma A NatSet.empty NatSet.empty emptyEnv
|approxUpdFree E1 E2 Gamma A v1 v2 x fVars dVars m:
   approxEnv E1 Gamma A fVars dVars E2 ->
   Gamma (Var R x) = Some m ->
   (Rabs (v1 - v2) <= computeErrorR v1 m)%R ->
   NatSet.mem x (NatSet.union fVars dVars) = false ->
   approxEnv (updEnv x v1 E1)
             Gamma A (NatSet.add x fVars) dVars
             (updEnv x v2 E2)
|approxUpdBound E1 E2 Gamma A v1 v2 x fVars dVars m iv err:
   approxEnv E1 Gamma A fVars dVars E2 ->
   Gamma (Var R x) = Some m ->
   SnapvMap.find (Var Q x) A = Some (iv, err) ->
   (Rabs (v1 - v2) <= Q2R err)%R ->
   NatSet.mem x (NatSet.union fVars dVars) = false ->
   approxEnv (updEnv x v1 E1)
             Gamma A fVars (NatSet.add x dVars)
             (updEnv x v2 E2).

Section RelationProperties.

  Variable (x:nat) (v:R) (E1 E2:env) (Gamma:expr R -> option mType)
           (A:analysisResult) (fVars dVars: NatSet.t).

  Hypothesis approxEnvs: approxEnv E1 Gamma A fVars dVars E2.

  Lemma approxEnv_gives_value:
    E1 x = Some v ->
    NatSet.In x (NatSet.union fVars  dVars) ->
    exists v',
      E2 x = Some v'.
  Proof.
    induction approxEnvs;
      intros E1_def x_valid.
    - unfold emptyEnv in E1_def; simpl in E1_def. congruence.
    - unfold updEnv in *.
      case_eq (x =? x0); intros eq_case; rewrite eq_case in *.
      + eexists; eauto.
      + eapply IHa; eauto.
        set_tac.
        destruct x_valid; set_tac.
        destruct H2 as [? | [? ?]]; subst; try auto.
        rewrite Nat.eqb_refl in eq_case; congruence.
    - unfold updEnv in *.
      case_eq (x =? x0); intros eq_case; rewrite eq_case in *.
      + eexists; eauto.
      + eapply IHa; auto.
        set_tac.
        destruct x_valid; set_tac.
        destruct H3 as [? | [ ? ?]]; subst; try auto.
        rewrite Nat.eqb_refl in eq_case; congruence.
  Qed.

  Arguments mTypeToQ _ : simpl nomatch.

  Lemma approxEnv_fVar_bounded v2 m:
    E1 x = Some v ->
    E2 x = Some v2 ->
    NatSet.In x fVars ->
    Gamma (Var R x) = Some m ->
    (Rabs (v - v2) <= computeErrorR v m)%R.
  Proof.
    induction approxEnvs;
      intros E1_def E2_def x_free x_typed.
    - unfold emptyEnv in *; simpl in *; congruence.
    - set_tac.
      destruct x_free as [x_x0 | [x_neq x_free]]; subst.
      + unfold updEnv in *;
          rewrite Nat.eqb_refl in *; simpl in *.
        congruence.
      + unfold updEnv in *; simpl in *.
        rewrite <- Nat.eqb_neq in x_neq.
        rewrite x_neq in *; simpl in *.
        unfold updDefVars in x_typed.
        cbn in x_typed.
        apply Nat.eqb_neq in x_neq.
        destruct (x ?= x0)%nat eqn:?.
        * apply Nat.compare_eq in Heqc; subst; congruence.
        * apply IHa; auto.
        * apply IHa; auto.
    - assert (x =? x0 = false) as x_x0_neq.
      { rewrite Nat.eqb_neq; hnf; intros; subst.
        set_tac.
        apply H2.
        set_tac. }
      unfold updEnv in *; rewrite x_x0_neq in *.
      cbn in x_typed.
      apply Nat.eqb_neq in x_x0_neq.
      destruct (x ?= x0)%nat eqn:?.
      * apply Nat.compare_eq in Heqc; subst; congruence.
      * apply IHa; auto.
      * apply IHa; auto.
  Qed.

  Lemma approxEnv_dVar_bounded v2 m iv e:
    E1 x = Some v ->
    E2 x = Some v2 ->
    NatSet.In x dVars ->
    Gamma (Var R x) = Some m ->
    SnapvMap.find (Var Q x) A = Some (iv, e) ->
    (Rabs (v - v2) <= Q2R e)%R.
  Proof.
    induction approxEnvs;
      intros E1_def E2_def x_def x_typed A_e; subst.
    - unfold emptyEnv in *; simpl in *; congruence.
    - assert (x =? x0 = false) as x_x0_neq.
      { rewrite Nat.eqb_neq; hnf; intros; subst.
        set_tac.
        apply H1; set_tac.
      }
      unfold updEnv in *; rewrite x_x0_neq in *.
      unfold updDefVars in x_typed; cbn in x_typed.
      apply Nat.eqb_neq in x_x0_neq.
      destruct (x ?= x0)%nat eqn:?.
      * apply Nat.compare_eq in Heqc; subst; congruence.
      * apply IHa; auto.
      * apply IHa; auto.
    - set_tac.
      destruct x_def as [x_x0 | [x_neq x_def]]; subst.
      + unfold updEnv in *;
          rewrite Nat.eqb_refl in *; simpl in *.
        inversion E1_def; inversion E2_def; subst.
        rewrite A_e in *; inversion H0; auto.
      + unfold updEnv in *; simpl in *.
        rewrite <- Nat.eqb_neq in x_neq.
        rewrite x_neq in *; simpl in *.
        unfold updDefVars in x_typed; cbn in x_typed.
        apply Nat.eqb_neq in x_neq.
        destruct (x ?= x0)%nat eqn:?.
        * apply Nat.compare_eq in Heqc; subst; congruence.
        * apply IHa; auto.
        * apply IHa; auto.
  Qed.

End RelationProperties.

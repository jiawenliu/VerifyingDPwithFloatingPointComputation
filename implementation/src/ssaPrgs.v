(**
  We define a pseudo SSA predicate.
  The formalization is similar to the renamedApart property in the LVC framework by Schneider, Smolka and Hack
  http://dblp.org/rec/conf/itp/SchneiderSH15
  Our predicate is not as fully fledged as theirs, but we especially borrow the idea of annotating
  the program with the predicate with the set of free and defined variables
**)
Require Import Coq.QArith.QArith Coq.QArith.Qreals Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Snapv.Infra.RealRationalProps Snapv.Infra.Ltacs.
Require Export Snapv.ExpressionSemantics.

Lemma validVars_add V (e:expr V) Vs n:
  NatSet.Subset (freeVars e) Vs ->
  NatSet.Subset (freeVars e) (NatSet.add n Vs).
Proof.
  set_tac.
Qed.

(*
Lemma validVars_non_stuck (e:expr Q) inVars E:
 NatSet.Subset (usedVars e) inVars ->
  (forall v, NatSet.In v (usedVars e) ->
        exists r, (toREvalEnv E) v = Some (r, REAL))%R ->
  exists vR, eval_expr (toREvalEnv E) (toREval (toRExp e)) vR REAL.
Proof.
    revert inVars E; induction e;
    intros inVars E vars_valid fVars_live.
  - simpl in *.
    assert (NatSet.In n (NatSet.singleton n)) as in_n by (rewrite NatSet.singleton_spec; auto).
    specialize (fVars_live n in_n).
    destruct fVars_live as [vR E_def].
    exists vR; econstructor; eauto.
  - exists (perturb (Q2R v) 0); constructor.
    simpl (meps REAL); rewrite Rabs_R0; rewrite Q2R0_is_0; lra.
  - assert (exists vR, eval_expr (toREvalEnv E) (toREval (toRExp e)) vR REAL)
      as eval_e_def by (eapply IHe; eauto).
    destruct eval_e_def as [ve eval_e_def].
    case_eq u; intros; subst.
    + exists (evalUnop Neg ve); constructor; auto.
    + exists (perturb (evalUnop Inv ve) 0); constructor; auto.
      simpl (meps REAL); rewrite Q2R0_is_0; rewrite Rabs_R0; lra.
  - repeat rewrite NatSet.subset_spec in *; simpl in *.
    assert (exists vR1, eval_expr (toREvalEnv E) (toREval (toRExp e1)) vR1 REAL) as eval_e1_def.
    + eapply IHe1; eauto.
      * hnf; intros.
        apply vars_valid.
        rewrite NatSet.union_spec; auto.
      * intros.
        destruct (fVars_live v) as [vR E_def]; try eauto.
        apply NatSet.union_spec; auto.
    + assert (exists vR2, eval_expr (toREvalEnv E) (toREval (toRExp e2)) vR2 REAL) as eval_e2_def.
      * eapply IHe2; eauto.
        { hnf; intros.
        apply vars_valid.
        rewrite NatSet.union_spec; auto. }
        { intros.
          destruct (fVars_live v) as [vR E_def]; try eauto.
          apply NatSet.union_spec; auto. }
      * destruct eval_e1_def as [vR1 eval_e1_def];
          destruct eval_e2_def as [vR2 eval_e2_def].
        exists (perturb (evalBinop b vR1 vR2) 0).
        replace REAL with (computeJoin REAL REAL) by auto.
        constructor; auto.
        simpl meps; rewrite Q2R0_is_0. rewrite Rabs_R0; lra.
  - assert (exists vR, eval_expr (toREvalEnv E) (toREval (toRExp e))  vR REAL) as eval_r_def by (eapply IHe; eauto).
    destruct eval_r_def as [vr eval_r_def].
    exists vr.
    simpl toREval.
    auto.
Qed. *)

Inductive ssa (V:Type): (expr V) -> NatSet.t -> NatSet.t -> Prop :=
| ssaVar x inVars outVars:
    (x ∈ inVars) ->
    (NatSet.Subset inVars outVars) ->
    ssa (Var _ x) inVars outVars
| ssaConst m v inVars outVars:
    (NatSet.Subset inVars outVars) ->
    ssa (Const m v) inVars outVars
| ssaUnop u e inVars outVars:
    ssa e inVars outVars ->
    ssa (Unop u e) inVars outVars
| ssaBinop b e1 e2 inVars outVars1 outVars2 outVars3:
    ssa e1 inVars outVars1 ->
    ssa e2 inVars outVars2 ->
    NatSet.Subset (NatSet.union outVars1 outVars2) outVars3 ->
    ssa (Binop b e1 e2) inVars outVars3
(*| ssaFma e1 e2 e3 inVars outVars1 outVars2 outVars3 outVars4:
    ssa e1 inVars outVars1 ->
    ssa e2 inVars outVars2 ->
    ssa e3 inVars outVars3 ->
    NatSet.Subset (NatSet.union outVars1 (NatSet.union outVars2 outVars3))
                  outVars4 ->
    ssa (Fma e1 e2 e3) inVars outVars4
*)
(*  | ssaDowncast m e inVars outVars:
    ssa e inVars outVars ->
    ssa (Downcast m e) inVars outVars
*)
  (*| ssaLet m x e s inVars outVars1 outVars2 outVars3:
    NatSet.mem x inVars = false ->
    ssa e inVars outVars1 ->
    ssa s (NatSet.add x inVars) outVars2 ->
    NatSet.Subset (NatSet.union outVars1 outVars2) outVars3 ->
    ssa (Let m x e s) inVars outVars3*)
        (*
| ssaCond e1 e2 e3 inVars outVars:
    ssa e1 inVars outVars ->
    ssa e2 inVars outVars ->
    ssa e3 inVars outVars ->
    ssa (Cond e1 e2 e3) inVars outVars
         *)
.

Lemma ssa_subset_freeVars V (f: expr V) inVars outVars:
  ssa f inVars outVars ->
  NatSet.Subset (freeVars f) inVars.
Proof.
  intros ssa_f; induction ssa_f; cbn; try now set_tac.
  - intros n ?. set_tac. now subst.
  - intros n. set_tac. intros [?|?]; auto.
(*  - intros n. set_tac. intros [?|[?|?]]; auto.
  - intros n. set_tac. intros [?|[? ?]]; auto.
    eapply NatSetProps.Dec.F.add_3; eauto.
*)  
  (* - intros n. set_tac. intros [?|[?|?]]; auto. *)
Qed.

Lemma ssa_equal_set V (f:expr V) inVars inVars' outVars:
  NatSet.Equal inVars' inVars ->
  ssa f inVars outVars ->
  ssa f inVars' outVars.
Proof.
  intros set_eq ssa_f.
  revert set_eq; revert inVars'.
  induction ssa_f; try constructor; auto.
  - intros. hnf in H0. hnf in set_eq. rewrite set_eq; auto.
  - hnf in *; intros.
    apply H0. rewrite <- set_eq; auto.
  - hnf in *. intros.
    apply H. rewrite <- set_eq; auto.
  - hnf in *. intros.
    econstructor; eauto.
(*  - hnf in *; intros. econstructor; eauto.
  - hnf in *; intros. econstructor; eauto.
    + apply NatSetProps.Dec.F.not_mem_iff. intros ?. set_tac. now apply H, set_eq.
    + apply IHssa_f2.
      split; set_tac; intros[?|Ha]; auto; apply set_eq in Ha; auto.
*)
Qed.

Lemma ssa_subset_ext V (f:expr V):
  forall inVars1 inVars2 outVars,
    NatSet.Subset inVars1 inVars2 ->
    NatSet.Subset (freeVars f) inVars1 ->
    ssa f inVars2 outVars ->
    ssa f inVars1 outVars.
Proof.
  induction f; intros * invars_sub fVars_sub ssa_invars;
    inversion ssa_invars; subst; simpl in *.
  - constructor. set_tac.
    hnf; intros; apply H1. now apply invars_sub.
  - constructor.
    hnf; intros; apply H3. now apply invars_sub.
  - specialize (IHf _ _ _ invars_sub fVars_sub H3).
    constructor; auto.
  - assert (NatSet.Subset (freeVars f1) inVars1 /\
            NatSet.Subset (freeVars f2) inVars1)
      as (f1_subset & f2_subset)
        by (split; set_tac).
    eapply ssaBinop;
      [ eapply IHf1; eauto | eapply IHf2; eauto | auto ].
(*  - assert (NatSet.Subset (freeVars f1) inVars1 /\
            NatSet.Subset (freeVars f2) inVars1 /\
            NatSet.Subset (freeVars f3) inVars1)
      as (f1_subset & f2_subset & f3_subset)
        by (repeat split; set_tac).
    eapply ssaFma;
      [ eapply IHf1; eauto | eapply IHf2; eauto | eapply IHf3; eauto | auto ].
  - specialize (IHf _ _ _ invars_sub fVars_sub H3).
    constructor; auto.
  - eapply ssaLet.
    + destruct ((n) mem (inVars1)) eqn:in_case; try auto.
      set_tac.
      exfalso; apply H3.
      apply invars_sub; auto.
    + eapply IHf1; eauto.
      set_tac.
    + eapply IHf2; try eauto.
      * set_tac; intuition.
      * set_tac. destruct (a =? n) eqn:case_mem.
        { rewrite Nat.eqb_eq in case_mem; auto. }
        { rewrite Nat.eqb_neq in case_mem.
          right; apply fVars_sub.
          set_tac. }
    + auto.*)
Qed.

Corollary ssa_is_fVars V (f:expr V) inVars outVars:
  NatSet.Subset (freeVars f) inVars ->
  ssa f inVars outVars ->
  ssa f (freeVars f) outVars.
Proof.
  intros.
  eapply ssa_subset_ext; eauto.
  set_tac.
Qed.

Lemma ssa_outVars_extensible V (e:expr V):
  forall inVars outVars1 outVars2,
    ssa e inVars outVars1 ->
    NatSet.Subset outVars1 outVars2 ->
    ssa e inVars outVars2.
Proof.
  induction e; intros * ssa_e subset_vars;
    inversion ssa_e; subst; try constructor; try set_tac.
  - eapply IHe; eauto.
  - econstructor; try eauto. set_tac.
(*  - econstructor; try eauto. set_tac.
    destruct H; try auto. set_tac.
  - eapply IHe; eauto.
  - econstructor; try eauto.
    + rewrite <- NatSetProps.Dec.F.not_mem_iff; auto.
    + set_tac.*)
Qed.


Ltac extended_ssa :=
  eapply ssa_outVars_extensible; try eauto; set_tac.

Fixpoint validSSA (f:expr Q) (inVars:NatSet.t) :=
  match f with
  | Var _ x => NatSet.mem x inVars
  | Const _ _ => true
  | Unop _ e => validSSA e inVars
  | Binop _ e1 e2 => validSSA e1 inVars && validSSA e2 inVars
(*  | Fma e1 e2 e3 => validSSA e1 inVars && validSSA e2 inVars && validSSA e3 inVars
  | Downcast _ e => validSSA e inVars
  | Let m x e g =>
    (negb (NatSet.mem x inVars)) && validSSA e inVars && validSSA g (NatSet.add x inVars)
*)  
  (* | Cond e1 e2 e3 => validSSA e1 inVars && validSSA e2 inVars && validSSA e3 inVars *)
  end.

Lemma validSSA_sound f inVars:
  validSSA f inVars = true ->
  exists outVars, ssa f inVars outVars.
Proof.
  induction f in inVars |- *; cbn; intros H.
  - exists inVars. constructor; [ set_tac | auto using NatSetProps.subset_refl].
  - exists inVars. constructor; auto using NatSetProps.subset_refl.
  - destruct (IHf _ H) as [O ?]. exists O.
    now constructor.
  - andb_to_prop H.
    edestruct IHf1 as [O1 ?]; eauto.
    edestruct IHf2 as [O2 ?]; eauto.
    exists (O1 ∪ O2).
    econstructor; try eauto. set_tac.
(*  - andb_to_prop H.
    edestruct IHf1 as [O1 ?]; eauto.
    edestruct IHf2 as [O2 ?]; eauto.
    edestruct IHf3 as [O3 ?]; eauto.
    exists (O1 ∪ O2 ∪ O3).
    econstructor; try eauto. set_tac.
    destruct H2; try auto. set_tac.
  - destruct (IHf _ H) as [O ?]. exists O.
    now constructor.
  - andb_to_prop H.
    apply negb_true_iff in L0.
    edestruct IHf1 as [O1 ?]; eauto.
    edestruct IHf2 as [O2 ?]; eauto.
    exists (O1 ∪ O2).
    econstructor; try eauto. set_tac.
*)    (*
  - andb_to_prop H.
    edestruct IHf1 as [O1 ?]; eauto.
    edestruct IHf2 as [O2 ?]; eauto.
    edestruct IHf3 as [O3 ?]; eauto.
    exists (O1 ∪ O2 ∪ O3).
    constructor; eauto using ssa_open_out.
*)
Qed.

Lemma validSSA_checks_freeVars f S :
  validSSA f S = true ->
  NatSet.Subset (freeVars f) S.
Proof.
  induction f in S |- *; intros * validSSA_true; cbn in *; set_tac.
  - now subst.
  - apply IHf; auto.
  - andb_to_prop validSSA_true.
    destruct H; [apply IHf1 | apply IHf2]; auto.
(*  - andb_to_prop validSSA_true.
    destruct H; set_tac; [apply IHf1 | destruct H; [apply IHf2 | apply IHf3]]; auto.
  - apply IHf; auto.
  - andb_to_prop validSSA_true.
    destruct H; [apply IHf1; auto |].
    pose proof (IHf2 _ R).
    revert H. set_tac.
    intros [? ?].
    pose proof (H0 _ H).
    set_tac. firstorder.*)
    (*
  - andb_to_prop validSSA_true.
    destruct H; set_tac; [apply IHf1 | destruct H; [apply IHf2 | apply IHf3]]; auto.
*)
Qed.

Lemma validSSA_eq_set s s' f :
  NatSet.Equal s' s -> validSSA f s = true -> validSSA f s' = true.
Proof.
  induction f in s, s' |- *; cbn; intros sub ?; auto.
  - set_tac. now apply sub.
  - eapply IHf; eauto.
  - andb_to_prop H.
    erewrite IHf1, IHf2; eauto.
(*  - andb_to_prop H.
    erewrite IHf1, IHf2, IHf3; eauto.
  - eapply IHf; eauto.
  - andb_to_prop H.
    apply andb_true_iff; split.
    apply andb_true_iff; split.
    + apply negb_true_iff.
      apply negb_true_iff in L0.
      set_tac.
      apply NatSetProps.FM.not_mem_iff.
      intros ?. apply L0. now apply sub.
    + eapply IHf1; eauto.*)
      (*
    + apply NatSetProps.FM.subset_1.
      apply NatSetProps.FM.subset_2 in R0.
      apply NatSetProps.equal_sym in sub.
      apply NatSetProps.subset_equal in sub.
      set_tac.
       *)
(*    + eapply IHf2; eauto.
      assert (NatSet.Subset s' s) by now apply NatSetProps.subset_equal in sub.
      apply NatSetProps.equal_sym in sub.
      apply NatSetProps.subset_equal in sub.
      split; set_tac; intuition.*)
      (*
  - andb_to_prop H.
    erewrite IHf1, IHf2, IHf3; eauto.
*)
Qed.

Lemma validSSA_downward_closed S S' f :
  NatSet.Subset (freeVars f) S' ->
  NatSet.Subset S' S ->
  validSSA f S = true ->
  validSSA f S' = true.
Proof.
  induction f in S, S' |- *; cbn; set_tac.
  - eauto.
  - andb_to_prop H1.
    erewrite IHf1, IHf2; eauto; set_tac.
(*  - andb_to_prop H1.
    erewrite IHf1, IHf2, IHf3; eauto; set_tac.
  - eauto.*)
(*  - andb_to_prop H1.
    apply andb_true_intro; split.
    apply andb_true_intro; split.
    + apply negb_true_iff.
      apply negb_true_iff in L0.
      set_tac.
      apply NatSetProps.FM.not_mem_iff.
      intros ?. apply L0. now apply H0.
    + eapply IHf1; eauto. set_tac.*)
      (*
    + apply NatSetProps.FM.subset_1.
      apply NatSetProps.FM.subset_2 in R0.
      set_tac.
       *)
(*    + eapply IHf2; eauto.
      * set_tac.
        destruct (dec_eq_nat a n); [now left | right; set_tac].
      * set_tac. intuition.*)
        (*
  - andb_to_prop H1.
    erewrite IHf1, IHf2, IHf3; eauto; set_tac.
*)
Qed.

(*Lemma ssa_shadowing_free m x y v v' e f inVars outVars E Gamma DeltaMap:
  ssa (Let m x (toREval (toRExp e)) (toREval (toRExp f))) inVars outVars ->
  NatSet.In y inVars ->
  eval_expr E Gamma DeltaMap (toREval (toRExp e)) v REAL ->
  forall E n, updEnv x v (updEnv y v' E) n = updEnv y v' (updEnv x v E) n.
Proof.
  intros ssa_let y_free eval_e.
  inversion ssa_let; subst.
  intros E' n; unfold updEnv.
  case_eq (n =? x).
  - intros n_eq_x.
    rewrite Nat.eqb_eq in n_eq_x.
    case_eq (n =? y); try auto.
    intros n_eq_y.
    rewrite Nat.eqb_eq in n_eq_y.
    rewrite n_eq_x in n_eq_y.
    rewrite <- n_eq_y in y_free.
    rewrite <- NatSet.mem_spec in y_free.
    congruence.
  - intros n_neq_x.
    case_eq (n =? y); auto.
Qed.

Lemma ssa_inv_let V (e: expr V) m x g inVars outVars:
ssa (Let m x e g) inVars outVars ->
~ NatSet.In x inVars /\ ~ NatSet.In x (freeVars e).
Proof.
  intros ssa_let.
  inversion ssa_let; subst.
  set_tac.
  split; auto.
  intros x_free.
  eapply ssa_subset_freeVars in x_free; eauto.
Qed.
*)
  
Lemma eval_expr_ssa_extension (e: expr R) E Gamma DeltaMap
      vR vR' m__e n fVars:
  NatSet.Subset (freeVars e) fVars ->
  ~ (n ∈ fVars) ->
  eval_expr E Gamma DeltaMap e vR m__e ->
  eval_expr (updEnv n vR' E) Gamma DeltaMap e vR m__e.
Proof.
  intros Hsub Hnotin Heval.
  eapply eval_expr_ignore_bind; [auto |].
  intros ?. apply Hnotin. set_tac.
Qed.

(*Lemma eval_expr_ssa_extension2 (e: expr R) (e' : expr Q) E Gamma DeltaMap
      v v' m__e m n c fVars dVars outVars:
  ssa (Let m__e n e' c) (fVars ∪ dVars) outVars ->
  NatSet.Subset (freeVars e) (fVars ∪ dVars) ->
  ~ (n ∈ fVars ∪ dVars) ->
  eval_expr (updEnv n v' E) Gamma DeltaMap e v m ->
  eval_expr E Gamma DeltaMap e v m.
Proof.
  intros Hssa Hsub Hnotin Heval.
  eapply eval_expr_det_ignore_bind2; [eauto |].
  edestruct ssa_inv_let; eauto.
Qed.*)

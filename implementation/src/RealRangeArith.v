From Coq
     Require Import QArith.QArith QArith.Qreals QArith.Qminmax micromega.Psatz Recdef.

From Flover
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.Ltacs Infra.RealSimps TypeValidator ssaPrgs IntervalArithQ
     IntervalArith.

Lemma eqb_var x e : FloverMapFacts.P.F.eqb (Var Q x) e = true -> e = Var Q x.
Proof.
  rewrite eqb_cmp_eq. destruct e; cbn; try discriminate.
  case_eq (x ?= n)%nat; intros H; try discriminate.
  apply Nat.compare_eq in H. now subst.
Qed.

Lemma find_in_precond P x (iv: intv) :
  FloverMap.find (Var Q x) P = Some iv -> List.In (Var Q x, iv) (FloverMap.elements P).
Proof.
  rewrite FloverMapFacts.P.F.elements_o.
  intros H. apply findA_find in H as [e [H _]].
  apply List.find_some in H as [Hin Heq].
  apply eqb_var in Heq. cbn in *. now subst.
Qed.

(*
Definition P_intv_sound E (P: precond) :=
  forall x iv, FloverMap.find (Var Q x) P = Some iv
             -> exists vR: R, E x = Some vR /\ Q2R (fst iv) <= vR <= Q2R (snd iv).
*)

Definition eval_preIntv E P :=
  forall x iv, List.In (Var Q x, iv) P ->
          exists vR: R, E x = Some vR /\ (Q2R (fst iv) <= vR <= Q2R (snd iv))%R.

Definition addVar2Set (elt: (expr Q * intv)) s :=
  match elt with
  | (Var _ x, _) => NatSet.add x s
  | _ => s
  end.

Definition preIntvVars P :=
  List.fold_right addVar2Set NatSet.empty P.

Lemma preIntvVars_sound P x iv :
  List.In (Var Q x, iv) P -> x ∈ (preIntvVars P).
Proof.
  unfold preIntvVars.
  induction P.
  - cbn. tauto.
  - cbn. intros [-> | ?]; cbn; set_tac.
    destruct a as [e ?]; destruct e; auto. cbn. set_tac.
Qed.

Definition dVars_range_valid (dVars:NatSet.t) (E:env) (A:analysisResult) :Prop :=
  forall v, NatSet.In v dVars ->
       exists vR iv err,
         E v =  Some vR /\
         FloverMap.find (Var Q v) A = Some (iv, err) /\
         (Q2R (fst iv) <= vR <= Q2R (snd iv))%R.

Ltac kill_trivial_exists :=
  match goal with
  | [ |- exists iv err v, Some (?i,?e) = Some (iv, err) /\ _ ] => exists i, e
  | [ |- exists iv err, Some (?i,?e) = Some (iv, err) /\ _ ] => exists i, e
  end.

Fixpoint validRanges e (A:analysisResult) E Gamma :Prop :=
  match e with
  | Var _ x => True
  | Const m v => True
  | Unop u e1 => validRanges e1 A E Gamma
  | Binop b e1 e2 =>
    (b = Div ->
     (forall iv2 err,
         FloverMap.find e2 A = Some (iv2, err) ->
         ((Qleb (ivhi iv2) 0) && (negb (Qeq_bool (ivhi iv2) 0))) ||
         ((Qleb 0 (ivlo iv2)) && (negb (Qeq_bool (ivlo iv2) 0))) = true)) /\
    validRanges e1 A E Gamma /\ validRanges e2 A E Gamma
  | Fma e1 e2 e3 =>
    validRanges e1 A E Gamma /\ validRanges e2 A E Gamma /\
    validRanges e3 A E Gamma
  | Downcast m e1 => validRanges e1 A E Gamma
  | Let _ x e1 e2 =>
    validRanges e1 A E Gamma /\
    (exists iv1 err1 iv_x err_x,
        FloverMap.find e1 A = Some (iv1, err1) /\
        FloverMap.find (Var Q x) A = Some (iv_x, err_x) /\
        Qeq_bool (ivlo iv1) (ivlo iv_x) && Qeq_bool (ivhi iv1) (ivhi iv_x) = true) /\
    (forall vR, eval_expr E Gamma DeltaMapR (toREval (toRExp e1)) vR REAL ->
           validRanges e2 A (updEnv x vR E) Gamma)
      (*
  | Cond e1 e2 e3 =>
    validRanges e1 A E Gamma /\ validRanges e2 A E Gamma /\
    validRanges e3 A E Gamma
*)
  end /\
  exists iv err vR,
    FloverMap.find e A = Some (iv, err) /\
    eval_expr E Gamma DeltaMapR (toREval (toRExp e)) vR REAL /\
    (Q2R (fst iv) <= vR <= Q2R (snd iv))%R.

Corollary validRanges_single e A E Gamma:
  validRanges e A E Gamma ->
  exists iv err vR,
    FloverMap.find e A = Some (iv, err) /\
    eval_expr E Gamma DeltaMapR (toREval (toRExp e)) vR REAL /\
    (Q2R (fst iv) <= vR <= Q2R (snd iv))%R.
Proof.
  destruct e; intros [_ valid_e]; simpl in *; try auto.
Qed.

Lemma validRanges_swap Gamma1 Gamma2:
  forall e A E,
    (forall n, Gamma1 n =  Gamma2 n) ->
    validRanges e A E Gamma1 ->
    validRanges e A E Gamma2.
Proof.
  induction e; intros * Gamma_swap valid1; simpl in *; try (split; auto);
    try (
        destruct valid1 as [_ [? [? [? [? [? ?]]]]]];
        repeat eexists; eauto;
        [eapply swap_Gamma_eval_expr with (Gamma1 := Gamma1); eauto |
         lra |
         lra]).
  - destruct valid1; auto.
  - destruct valid1 as [[? [? ?]] ?]; auto.
  - destruct valid1 as [[? [? ?]] ?]; auto.
  - destruct valid1; auto.
  - destruct valid1 as [[H1 [H2 H3]] _]; auto.
    repeat split; try auto.
    intros. eauto using swap_Gamma_eval_expr.
  (* - destruct valid1 as [[? [? ?]] ?]; auto. *)
Qed.

(*
Fixpoint validRangesCmd (f:cmd Q) A E Gamma {struct f} : Prop :=
  match f with
  | Let m x e g =>
    validRanges e A E Gamma /\
    (forall vR, eval_expr E Gamma DeltaMapR (toREval (toRExp e)) vR REAL ->
             validRangesCmd g A (updEnv x vR E) Gamma)
  | Ret e => validRanges e A E Gamma
  end /\
  exists iv_e err_e vR,
    FloverMap.find (getRetExp f) A = Some (iv_e, err_e) /\
    bstep (toREvalCmd (toRCmd f)) E Gamma DeltaMapR vR REAL /\
    (Q2R (fst iv_e) <=  vR <= Q2R (snd iv_e))%R.

Corollary validRangesCmd_single f A E Gamma:
  validRangesCmd f A E Gamma ->
  exists iv_e err_e vR,
    FloverMap.find (getRetExp f) A = Some (iv_e, err_e) /\
    bstep (toREvalCmd (toRCmd f)) E Gamma DeltaMapR vR REAL /\
    (Q2R (fst iv_e) <=  vR <= Q2R (snd iv_e))%R.
Proof.
  destruct f; simpl in *; intros [ _ valid_f]; auto.
Qed.

Lemma validRangesCmd_swap:
  forall f A E Gamma1 Gamma2,
    (forall n, Gamma1 n =  Gamma2 n) ->
    validRangesCmd f A E Gamma1 ->
    validRangesCmd f A E Gamma2.
Proof.
  induction f; intros * Gamma_swap valid1; simpl in *; try (split; auto);
    try (
        destruct valid1 as [_ [? [? [? [? [? ?]]]]]];
        repeat eexists; eauto;
        [eapply swap_Gamma_bstep with (Gamma1 := Gamma1); eauto |
         lra |
         lra]).
  - destruct valid1 as [[? valid_all_exec] ?]; split.
    + eapply validRanges_swap; eauto.
    + intros. eapply IHf; [ auto | eapply valid_all_exec].
      eapply swap_Gamma_eval_expr with (Gamma1 := Gamma2); eauto.
  - destruct valid1.
    eapply validRanges_swap; eauto.
Qed.
*)

Lemma validRanges_eq_compat (e1: expr Q) e2 A E Gamma:
  Q_orderedExps.eq e1 e2 ->
  validRanges e1 A E Gamma ->
  validRanges e2 A E Gamma.
Proof.
  intros Heq.
  unfold Q_orderedExps.eq in Heq.
  revert E.
  functional induction (Q_orderedExps.exprCompare e1 e2); intros E; try congruence.
  - simpl.
    intros [_ validr1].
    repeat split; auto.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    apply Nat.compare_eq in Heq.
    rewrite <- Heq.
    intuition.
  - intros [_ validr1].
    repeat split; auto.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      unfold Q_orderedExps.exprCompare.
      rewrite e3; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite e3; auto.
  - simpl in e3.
    rewrite andb_false_iff in e3.
    destruct e3.
    + apply Ndec.Pcompare_Peqb in e6.
      congruence.
    + apply N.compare_eq in Heq; subst.
      rewrite N.eqb_refl in H; congruence.
  - intros valid1; destruct valid1 as [validsub1 validr1].
    specialize (IHc Heq E validsub1).
    split; auto.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e5; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite e5; auto.
  - intros valid1; destruct valid1 as [[_ [validsub1 validsub1']] validr1].
    specialize (IHc e6 E validsub1).
    specialize (IHc0 Heq E validsub1').
    repeat split; auto; try congruence.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e6; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite Heq, e6; auto.
  - intros valid1; destruct valid1 as [[_ [validsub1 validsub1']] validr1].
    specialize (IHc e6 E validsub1).
    specialize (IHc0 Heq E validsub1').
    repeat split; auto; try congruence.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e6; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite Heq, e6; auto.
  - intros valid1; destruct valid1 as [[_ [validsub1 validsub1']] validr1].
    specialize (IHc e6 E validsub1).
    specialize (IHc0 Heq E validsub1').
    repeat split; auto; try congruence.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e6; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite Heq, e6; auto.
  - intros valid1; destruct valid1 as [[Hdiv [validsub1 validsub1']] validr1].
    specialize (IHc e6 E validsub1).
    specialize (IHc0 Heq E validsub1').
    repeat split; auto.
    {
      intros Hrefl; specialize (Hdiv Hrefl).
      intros iv2 err Hfind.
      erewrite FloverMapFacts.P.F.find_o with (y := e12) in Hfind.
      eapply Hdiv; eauto.
      now rewrite Q_orderedExps.exprCompare_eq_sym.
    }
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e6; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite Heq, e6; auto.
  - intros valid1; destruct valid1 as [[validsub1 [validsub1' validsub1'']] validr1].
    specialize (IHc e3 E validsub1).
    specialize (IHc0 e4 E validsub1').
    specialize (IHc1 Heq E validsub1'').
    repeat split; auto; try congruence.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e3, e4, Heq; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite Heq, e3, e4; auto.
  - intros valid1; destruct valid1 as [validsub1 validr1].
    specialize (IHc Heq E validsub1).
    split; auto.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e5; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite e5; auto.
  - simpl in e5.
    rewrite andb_false_iff in e5.
    destruct e5.
    + apply Ndec.Pcompare_Peqb in e8.
      congruence.
    + apply N.compare_eq in Heq; subst.
      rewrite N.eqb_refl in *; congruence.
  - intros valid1; destruct valid1
      as [[validsub1 [(? & ? & ? & ? & find_e1 & find_x & valid_equiv) validsub2]] validr1].
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    inversion Hee; subst.
    apply nat_compare_eq in e4; subst.
    repeat split; auto.
    + specialize (IHc e5 E validsub1).
      apply validRanges_single in IHc.
      destruct IHc as (iv_e1 & err_e1 & vR1 & find_e21 & eval_e21 & bounded_e21).
      erewrite FloverMapFacts.P.F.find_o with (y:= e21) in find_e1; eauto.
      rewrite find_e21 in find_e1; inversion find_e1; subst.
      repeat eexists; eauto.
    + intros v ?.
      eapply IHc0; eauto.
      apply validsub2.
      erewrite expr_compare_eq_eval_compat; eauto.
    + exists iv, err, vR.
      intuition.
      * rewrite <- Hfind.
        symmetry.
        apply FloverMapFacts.P.F.find_o.
        simpl.
        rewrite e3, e5.
        rewrite Nat.compare_refl; auto.
      * erewrite expr_compare_eq_eval_compat; eauto.
        rewrite Q_orderedExps.exprCompare_eq_sym.
        simpl.
        rewrite e3, e5.
        rewrite Nat.compare_refl; auto.
  - cbn in * |-.
    rewrite Pos.eqb_compare in e3.
    rewrite N.eqb_compare in e3.
    rewrite Heq, e7 in e3.
    discriminate.
    (*
  - intros valid1; destruct valid1 as [[validsub1 [validsub1' validsub1'']] validr1].
    specialize (IHc e3 E validsub1).
    specialize (IHc0 e4 E validsub1').
    specialize (IHc1 Heq E validsub1'').
    repeat split; auto; try congruence.
    destruct validr1 as [iv [err [vR [Hfind [Hee Hcont]]]]].
    exists iv, err, vR.
    intuition.
    + rewrite <- Hfind.
      symmetry.
      apply FloverMapFacts.P.F.find_o.
      simpl.
      rewrite e3, e4, Heq; auto.
    + erewrite expr_compare_eq_eval_compat; eauto.
      rewrite Q_orderedExps.exprCompare_eq_sym.
      simpl.
      rewrite Heq, e3, e4; auto.
*)
Qed.

(*
Lemma validRanges_ssa_extension (e: expr Q) A E Gamma
      vR' n fVars:
  NatSet.Subset (freeVars e) fVars ->
  ~ (n ∈ fVars) ->
  validRanges e A E Gamma ->
  validRanges e A (updEnv n vR' E) Gamma.
Proof.
  induction e in E, fVars |- *;
    intros Hsub Hnotin Hranges.
  - split; auto.
    destruct Hranges as [_ [iv [err [vR Hranges]]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eassumption.
    (*eapply swap_Gamma_eval_expr.
    + intros *. symmetry. eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
  - split; auto.
    destruct Hranges as [_ [iv [err [vR Hranges]]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eassumption.
    (* eapply swap_Gamma_eval_expr.
    eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
  - simpl in Hsub.
    destruct Hranges as [Hunopranges Hranges].
    specialize (IHe _ _ Hsub Hnotin Hunopranges).
    split; auto.
    destruct Hranges as [iv [err [vR Hranges]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eauto.
    (* eapply swap_Gamma_eval_expr.
    eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
    rewrite freeVars_toREval_toRExp_compat; auto.
  - simpl in Hsub.
    assert (NatSet.Subset (freeVars e1) fVars) as Hsub1 by set_tac.
    assert (NatSet.Subset (freeVars e2) fVars) as Hsub2 by (clear Hsub1; set_tac).
    destruct Hranges as [[Hdiv [Hranges1 Hranges2]] Hranges].
    specialize (IHe1 _ _ Hsub1 Hnotin Hranges1).
    specialize (IHe2 _ _ Hsub2 Hnotin Hranges2).
    simpl.
    repeat split; auto.
    destruct Hranges as [iv [err [vR Hranges]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eauto.
    (* eapply swap_Gamma_eval_expr.
    eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
    simpl.
    rewrite !freeVars_toREval_toRExp_compat; auto.
  - simpl in Hsub.
    assert (NatSet.Subset (freeVars e1) fVars) as Hsub1 by set_tac.
    assert (NatSet.Subset (freeVars e2) fVars) as Hsub2 by (clear Hsub1; set_tac).
    assert (NatSet.Subset (freeVars e3) fVars) as Hsub3 by (clear Hsub1 Hsub2; set_tac).
    destruct Hranges as [[Hranges1 [Hranges2 Hranges3]] Hranges].
    specialize (IHe1 _ _ Hsub1 Hnotin Hranges1).
    specialize (IHe2 _ _ Hsub2 Hnotin Hranges2).
    specialize (IHe3 _ _ Hsub3 Hnotin Hranges3).
    simpl.
    repeat split; auto.
    destruct Hranges as [iv [err [vR Hranges]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eauto.
    (* eapply swap_Gamma_eval_expr.
    eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
    simpl.
    rewrite !freeVars_toREval_toRExp_compat; auto.
  - simpl in Hsub.
    destruct Hranges as [Hranges' Hranges].
    specialize (IHe _ _ Hsub Hnotin Hranges').
    split; auto.
    destruct Hranges as [iv [err [vR Hranges]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eauto.
    (* eapply swap_Gamma_eval_expr.
    eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
    rewrite freeVars_toREval_toRExp_compat; auto.
  - rename n0 into x. simpl in Hsub.
    assert (NatSet.Subset (freeVars e1) fVars) as Hsub1 by set_tac.
    destruct Hranges as [[Hranges1 Hranges2] Hranges].
    specialize (IHe1  _ _ Hsub1 Hnotin Hranges1).
    destruct Hranges as (iv & err & vR & find_e & eval_real & bounded_e).
    inversion eval_real; subst.
    specialize (Hranges2 v1 H7).
    specialize (IHe2 (updEnv x v1 E) fVars).
    repeat split; auto.
    + intros.
      destruct (n =? n0)%nat eqn:Heqn.
      * rewrite Nat.eqb_eq in Heqn; subst.
      * admit.
    + exists iv, err, vR; intuition.
      eapply eval_expr_ssa_extension; eauto.
      cbn.
    rewrite !freeVars_toREval_toRExp_compat; auto.
    (*
  - simpl in Hsub.
    assert (NatSet.Subset (freeVars e1) fVars) as Hsub1 by set_tac.
    assert (NatSet.Subset (freeVars e2) fVars) as Hsub2 by (clear Hsub1; set_tac).
    assert (NatSet.Subset (freeVars e3) fVars) as Hsub3 by (clear Hsub1 Hsub2; set_tac).
    destruct Hranges as [[Hranges1 [Hranges2 Hranges3]] Hranges].
    specialize (IHe1 _ _ Hsub1 Hnotin Hranges1).
    specialize (IHe2 _ _ Hsub2 Hnotin Hranges2).
    specialize (IHe3 _ _ Hsub3 Hnotin Hranges3).
    simpl.
    repeat split; auto.
    destruct Hranges as [iv [err [vR Hranges]]].
    exists iv, err, vR; intuition.
    eapply eval_expr_ssa_extension; eauto.
    (* eapply swap_Gamma_eval_expr.
    eapply Rmap_updVars_comm.
    eapply eval_expr_ssa_extension; try eassumption. *)
    simpl.
    rewrite !freeVars_toREval_toRExp_compat; auto.
*)
Abort.
*)
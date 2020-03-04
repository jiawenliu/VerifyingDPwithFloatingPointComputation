From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Flover
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis ErrorBounds
     IntervalValidation RealRangeValidator TypeValidator ErrorValidation ErrorValidationLemmas.

Arguments mTypeToQ _ :simpl nomatch.
(**
   Soundness theorem for the error bound validator.
   Proof is by induction on the expression e.
   Each case requires the application of one of the soundness lemmata proven before
 **)
Theorem validErrorbound_sound (e:expr Q):
  forall E1 E2 fVars dVars outVars A Gamma,
    validTypes e Gamma ->
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    ssa e (NatSet.union fVars dVars) outVars ->
    NatSet.Subset (NatSet.diff (freeVars e) dVars) fVars ->
    validErrorbound e Gamma A dVars = true ->
    validRanges e A E1 (toRTMap (toRExpMap Gamma)) ->
    validErrorBounds e E1 E2 A Gamma.
Proof.
  revert e; induction e;
    intros * typing_ok approxCEnv ssa_f fVars_subset valid_error valid_intv DeltaMap deltas_matched.
  - split; auto.
    intros nR (elo, ehi) err eval_real A_eq.
    split.
    + eapply validErrorboundCorrectVariable_eval; eauto.
    + intros * eval_float. eapply validErrorboundCorrectVariable; eauto.
  - unfold validErrorBounds. split; auto.
    intros nR (elo, ehi) err eval_real A_eq.
    pose proof (validRanges_single _ _ _ _ valid_intv) as valid_const.
    destruct valid_const as [? [ ? [? [? [? ?]]]]].
    unfold error in H.
    rewrite H in A_eq; inversion A_eq; subst.
    rewrite (meps_0_deterministic _ eval_real H0) in *; auto.
    split.
    + eapply validErrorboundCorrectConstant_eval; eauto.
    + intros * eval_float.
      eapply validErrorboundCorrectConstant with (E2 := E2) (DeltaMap := DeltaMap); eauto.
      inversion eval_float; subst; auto.
  - rename IHe into IHe'.
    inversion ssa_f; subst.
    assert (validErrorBounds e E1 E2 A Gamma) as IHe.
    {
      eapply IHe'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct u; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    clear IHe'.
    split.
    { destruct u; cbn in *; Flover_compute; try congruence. auto. }
    auto.
    intros nR (elo, ehi) err eval_real A_eq.
    simpl in *.
    unfold error in *.
    rewrite A_eq in valid_error.
    cbn in *; Flover_compute; try congruence; type_conv; subst;
    destruct u; Flover_compute; try congruence.
    destruct typing_ok as [mU [? [[? ?] ?]]]; auto.
    inversion eval_real; subst.
    destruct valid_intv as [valid_rec [iv [err_e [vR [? [? ?]]]]]].
    inversion eval_real; subst.
    assert (m0 = REAL) by (eapply toRTMap_eval_REAL; eauto); subst.
    specialize (IHe DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v1) (iv := i) (err := q) in IHe; eauto.
    specialize IHe as [[nF [mF eval_float]] valid_bounds_e].
    split.
    * inversion H; subst.
      exists (evalUnop Neg nF); exists mU.
      eapply Unop_neg'; eauto.
      { eapply toRExpMap_some; eauto. simpl; auto. }
      { destruct H1 as [? [? ?]].
        apply validTypes_single in H0.
        destruct H0 as [? [? ?]].
        assert (x0 = x) by congruence; subst.
        assert (mF = x).
        { eapply H15; eauto. }
        subst; auto. }
    * intros * eval_float_op.
      inversion eval_float_op; subst; simpl.
      apply bound_flip_sub.
      canonize_hyps.
      rewrite R0; eapply valid_bounds_e; eauto.
  - rename IHe1 into IHe1'; rename IHe2 into IHe2'.
    inversion ssa_f; subst.
    assert (validErrorBounds e1 E1 E2 A Gamma) as IHe1.
    {
      eapply IHe1'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - set_tac. split; set_tac.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct b; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    clear IHe1'.
    assert (validErrorBounds e2 E1 E2 A Gamma) as IHe2.
    {
      eapply IHe2'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - set_tac. split; set_tac.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct b; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    clear IHe2'.
    split.
    { repeat split; [ | auto | auto ].
      intros; subst.
      Opaque mTypeToQ mTypeToR.
      cbn in *; Flover_compute; try congruence.
      Transparent mTypeToQ mTypeToR.
      unfold error in *.
      rewrite Heqo2 in H0. inversion H0; subst; auto. }
    intros nR (elo, ehi) err eval_real A_eq.
    simpl in valid_intv.
    destruct valid_intv
        as [[nodiv_zero [valid_e1 valid_e2]] valid_bin].
    unfold error in *.
    cbn in valid_error. Flover_compute; try congruence.
    destruct typing_ok as [? [? [[? [? ?]] ?]]]; auto.
    inversion eval_real; subst.
    assert (m1 = REAL /\ m2 = REAL) as [? ?] by (split; eapply toRTMap_eval_REAL; eauto); subst.
    specialize (IHe1 DeltaMap deltas_matched).
    apply validRanges_single in valid_e1;
      apply validRanges_single in valid_e2.
    destruct valid_e1 as [iv1 [ err1 [v1' [map_e1 [eval_real_e1 bounds_e1]]]]].
    destruct valid_e2 as [iv2 [ err2 [v2' [map_e2 [eval_real_e2 bounds_e2]]]]].
    pose proof (meps_0_deterministic _ eval_real_e1 H14); subst.
    pose proof (meps_0_deterministic _ eval_real_e2 H17); subst.
    rewrite map_e1, map_e2 in *.
    inversion Heqo1; inversion Heqo2; subst.
    rename e0 into err1; rename i0 into iv1.
    rename e3 into err2; rename i1 into iv2.
    apply validErrorBoundsRec_single with (v__R := v1) (iv := iv1) (err := err1) in IHe1; eauto.
    specialize IHe1 as [[nF1 [mF1 eval_float1]] valid_bounds_e1].
    specialize (IHe2 DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v2) (iv := iv2) (err := err2) in IHe2; eauto.
    specialize IHe2 as [[nF2 [mF2 eval_float2]] valid_bounds_e2].
    assert (contained nF1 (widenInterval (Q2R (fst iv1), Q2R (snd iv1)) (Q2R err1)))
      as bounds_float_e1.
    { eapply distance_gives_iv; simpl;
        try eauto. }
    assert (contained nF2 (widenInterval (Q2R (fst iv2), Q2R (snd iv2)) (Q2R err2)))
      as bounds_float_e2.
    { eapply distance_gives_iv; simpl;
        try eauto. }
    assert (b = Div -> ~ (nF2 = 0)%R) as no_div_zero.
    { intros; subst; simpl in *.
      andb_to_prop R0.
      apply le_neq_bool_to_lt_prop in L0.
      simpl in *. canonize_hyps.
      intro; subst.
      rewrite <- Q2R0_is_0 in bounds_float_e2.
      destruct L0 as [nodivzero | nodivzero];
        apply Qlt_Rlt in nodivzero;
        try rewrite Q2R_plus in *; try rewrite Q2R_minus in *; lra. }
    destruct H3 as [m1 [m2 [? [? valid_join]]]].
    assert (m1 = mF1) by (eapply validTypes_exec in H0; eauto);
      assert (m2 = mF2) by (eapply validTypes_exec in H1; eauto);
      subst.
    split.
    + specialize (deltas_matched (evalBinop b nF1 nF2) x)
        as (delta' & delta_matched' & delta_bound').
      exists (perturb (evalBinop b nF1 nF2) x delta'), x.
      eapply Binop_dist' with (delta:= delta'); eauto.
      eapply toRExpMap_some; eauto. simpl; auto.
    + intros * eval_float.
      clear eval_float1 eval_float2.
      inversion eval_float; subst.
      eapply (binary_unfolding H26 H21 H19 H22 H25) in eval_float; try auto.
      destruct b.
      * eapply (validErrorboundCorrectAddition (e1:=e1) A); eauto.
        { cbn. instantiate (1:=dVars); Flover_compute.
          rewrite L, L1, R; simpl; auto. }
        { destruct iv1; auto. }
        { destruct iv2; auto. }
        { eapply toRExpMap_find_map; eauto. }
      * eapply (validErrorboundCorrectSubtraction (e1:=e1) A); eauto.
        { cbn; instantiate (1:=dVars); Flover_compute.
          rewrite L, L1, R; simpl; auto. }
        { destruct iv1; auto. }
        { destruct iv2; auto. }
        { eapply toRExpMap_find_map; eauto. }
      *  eapply (validErrorboundCorrectMult (e1 := e1) A); eauto.
        { cbn; instantiate (1:=dVars); Flover_compute.
          rewrite L, L1, R; simpl; auto. }
        { destruct iv1; auto. }
        { destruct iv2; auto. }
        { eapply toRExpMap_find_map; eauto. }
      * eapply (validErrorboundCorrectDiv (e1 := e1) A); eauto.
        { cbn; instantiate (1:=dVars); Flover_compute.
          rewrite L, L1, L0, R; simpl; auto. }
        { destruct iv1; auto. }
        { destruct iv2; auto. }
        { eapply toRExpMap_find_map; eauto. }
  - rename IHe1 into IHe1'; rename IHe2 into IHe2'; rename IHe3 into IHe3'.
    inversion ssa_f; subst.
    assert (validErrorBounds e1 E1 E2 A Gamma) as IHe1.
    {
      eapply IHe1'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - set_tac. split; set_tac.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct b; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    assert (validErrorBounds e2 E1 E2 A Gamma) as IHe2.
    {
      eapply IHe2'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - set_tac. split; set_tac.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct b; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    assert (validErrorBounds e3 E1 E2 A Gamma) as IHe3.
    {
      eapply IHe3'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - set_tac. split; set_tac.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct b; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    clear IHe1' IHe2' IHe3'.
    split; auto.
    intros nR (elo, ehi) err eval_real A_eq.
    simpl in valid_intv.
    destruct valid_intv
        as [[valid_e1 [valid_e2 valid_e3]] valid_bin].
    cbn in valid_error. Flover_compute; try congruence.
    destruct typing_ok
      as [mG [find_mG [
                  [valid_t1 [valid_t2 [valid_t3
                                         [m1 [m2 [m3 [find_m1 [find_m2 [find_m3 valid_join]
                                         ]]]]]]]] valid_exec]]].
    inversion eval_real; subst.
    assert (m0 = REAL /\ m4 = REAL /\ m5 = REAL) as [? [? ?]]
        by (repeat split; eapply toRTMap_eval_REAL; eauto); subst.
    apply validRanges_single in valid_e1;
      apply validRanges_single in valid_e2;
      apply validRanges_single in valid_e3.
    destruct valid_e1 as [iv1 [ err1 [v1' [map_e1 [eval_real_e1 bounds_e1]]]]].
    destruct valid_e2 as [iv2 [ err2 [v2' [map_e2 [eval_real_e2 bounds_e2]]]]].
    destruct valid_e3 as [iv3 [ err3 [v3' [map_e3 [eval_real_e3 bounds_e3]]]]].
    pose proof (meps_0_deterministic _ eval_real_e1 H10); subst.
    pose proof (meps_0_deterministic _ eval_real_e2 H13); subst.
    pose proof (meps_0_deterministic _ eval_real_e3 H14); subst.
    rewrite map_e1, map_e2, map_e3 in *.
    symmetry in Heqo1, Heqo2, Heqo3.
    inversion Heqo1; inversion Heqo2; inversion Heqo3; subst.
    specialize (IHe1 DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v1) (iv := iv1) (err := err1) in IHe1; eauto.
    specialize IHe1 as [[nF1 [mF1 eval_float1]] valid_bounds_e1].
    specialize (IHe2 DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v2) (iv := iv2) (err := err2) in IHe2; eauto.
    specialize IHe2 as [[nF2 [mF2 eval_float2]] valid_bounds_e2].
    specialize (IHe3 DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v3) (iv := iv3) (err := err3) in IHe3; eauto.
    specialize IHe3 as [[nF3 [mF3 eval_float3]] valid_bounds_e3].
    assert (m1 = mF1) by (eapply validTypes_exec in find_m1; eauto).
    assert (m2 = mF2) by (eapply validTypes_exec in find_m2; eauto).
    assert (m3 = mF3) by (eapply validTypes_exec in find_m3; eauto); subst.
    assert (contained nF1 (widenInterval (Q2R (fst iv1), Q2R (snd iv1)) (Q2R err1)))
      as bounds_float_e1.
    { eapply distance_gives_iv; simpl;
        try eauto. }
    assert (contained nF2 (widenInterval (Q2R (fst iv2), Q2R (snd iv2)) (Q2R err2)))
      as bounds_float_e2.
    { eapply distance_gives_iv; simpl;
        try eauto. }
    assert (contained nF3 (widenInterval (Q2R (fst iv3), Q2R (snd iv3)) (Q2R err3)))
      as bounds_float_e3.
    { eapply distance_gives_iv; simpl;
        try eauto. }
    split.
    + specialize (deltas_matched (evalFma nF1 nF2 nF3) mG) as (delta' & delta_some' & delta_bound').
      eexists; exists mG; econstructor; eauto.
      eapply toRExpMap_some; eauto. simpl; auto.
    + intros * eval_float.
      clear eval_float1 eval_float2 eval_float3.
      inversion eval_float; subst.
      eapply (fma_unfolding H16 H12 H17 H20 H21) in eval_float; try auto.
      eapply (validErrorboundCorrectFma (e1:=e1) (e2:=e2) (e3:=e3) A); eauto.
      { simpl. unfold error in *.
        rewrite A_eq.
        rewrite Heqo0.
        rewrite Heqo in A_eq; inversion A_eq; subst.
        rewrite R, L0, L, R1; simpl.
        rewrite map_e1, map_e2, map_e3.
        inversion Heqo0; subst.
        auto. }
      { destruct iv1; auto. }
      { destruct iv2; auto. }
      { destruct iv3; auto. }
      { eapply toRExpMap_find_map; eauto. }
  - rename IHe into IHe'.
    inversion ssa_f; subst.
    assert (validErrorBounds e E1 E2 A Gamma) as IHe.
    {
      eapply IHe'; eauto.
      - specialize typing_ok as (? & ?).
        intuition.
      - cbn in *; Flover_compute; try congruence; type_conv; subst;
          destruct u; Flover_compute; try congruence.
      - cbn in valid_intv.
        intuition.
    }
    clear IHe'.
    split; auto.
    intros nR (elo, ehi) err eval_real A_eq.
    unfold error in *.
    cbn in *; Flover_compute; try congruence; type_conv; subst.
    inversion eval_real; subst.
    apply REAL_least_precision in H4; subst.
    destruct i as [ivlo_e ivhi_e]; rename e0 into err_e.
    destruct valid_intv as [valid_e1 valid_intv].
    destruct typing_ok as [mG [find_m [[valid_e [? [m1 [find_e1 morePrecise_m1]]]] valid_exec]]].
    specialize (IHe DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v1) (iv := i0) (err := e1) in IHe;
      eauto.
    specialize IHe as [[vF [mF eval_float_e]] bounded_e].
    assert (mF = m1) by (eapply validTypes_exec in find_e1; eauto); subst.
    apply validRanges_single in valid_e1.
    destruct valid_e1 as [iv1' [err1' [v1' [map_e [eval_real_e bounds_e]]]]].
    unfold error in *.
    rewrite map_e in Heqo1; inversion Heqo1; subst.
    pose proof (meps_0_deterministic _ eval_real_e H7); subst. clear H7.
    split.
    + specialize (deltas_matched (vF) mG)
        as (delta' & delta_some' & delta_bound').
      eexists; eexists.
      eapply Downcast_dist'; eauto.
      eapply toRExpMap_some with (e:= Downcast mG e); eauto. congruence.
    + intros * eval_float.
      inversion eval_float; subst.
      eapply validErrorboundCorrectRounding; eauto.
      * simpl. eapply Downcast_dist'; eauto.
        { constructor; cbn; auto. }
        { destruct Req_dec_sum as [Heq|Hneq]; auto; congruence. }
        { unfold updDefVars; cbn. rewrite mTypeEq_refl. auto. }
      * cbn; instantiate (1:=dVars).
        unfold error in *; Flover_compute.
        rewrite Heqo in A_eq. inversion A_eq; subst.
        rewrite L, L0; auto.
      * destruct i0; auto.
      * eapply toRExpMap_find_map; eauto.
  - inversion ssa_f; subst.
    assert (NatSet.Subset (freeVars e1 -- dVars) fVars) as valid_varset.
    { set_tac.
      split; try auto.
      set_tac. }
    pose proof typing_ok as valid_types'.
      (* pose proof valid_intv as valid_intv'. *)
    cbn in *. Flover_compute; try congruence.
    destruct typing_ok
      as [me [find_me [[validt_e [validt_f [? [find_e [find_x [find_f ?]]]]]] validt_exec]]].
    destruct valid_intv as [[validRange_e1 [validBound_x validRange_e2]] eval_real]; auto.
    destruct eval_real as [iv_1 [err_1 [vR1 [? [eval_real1 range_valid]]]]].
    assert (validErrorBounds e1 E1 E2 A Gamma) as Hsound
        by (eapply IHe1; eauto).
    split.
    {
      split; [ | split ].
      - eapply IHe1; eauto.
      - intros * find_e1 find_x2.
        unfold error in *.
        repeat (match goal with
                | H1: FloverMap.find ?e1 ?A = Some (?iv1, ?err1),
                      H2: FloverMap.find ?e1 ?A = Some (?iv2, ?err2) |- _ =>
                  rewrite H1 in H2; inversion H2; subst; clear H2;
                  let v := fresh "find" in
                  revert H1; intros v
                end).
        destruct validBound_x as (? & ? & ? & ? & ? & ? & ?).
        repeat (match goal with
                | H: Some ?a = Some ?b |- _ => inversion H; subst; clear H end).
        andb_to_prop H2; canonize_hyps. intuition.
      - intros vR vF eval_real eval_float.
        eapply validErrorBoundsRec_single in Hsound; eauto.
        destruct Hsound as [[vFe [mFe eval_float_e]] bounded_e].
        canonize_hyps.
        rename R into valid_rec.
        (* eapply validTypes_exec in find_me; eauto; subst. *)
        assert (m0 = me) by congruence; subst.
        (* type_conv; subst. *)
        eapply IHe2 with (fVars := fVars) (outVars := outVars); eauto.
        + eapply approxUpdBound; try eauto; simpl in *.
          * eapply (toRExpMap_some _ (Var Q n)); eauto.
          * apply Rle_trans with (r2:= Q2R e0); try lra.
            eapply bounded_e; eauto.
        + eapply ssa_outVars_extensible with (outVars1 := outVars2); try eauto;
            [ | set_tac].
          eapply ssa_equal_set; eauto.
          hnf. intros a; split; intros in_set.
          * rewrite NatSet.add_spec, NatSet.union_spec;
              rewrite NatSet.union_spec, NatSet.add_spec in in_set.
            destruct in_set as [P1 | [ P2 | P3]]; auto.
          * rewrite NatSet.add_spec, NatSet.union_spec in in_set;
              rewrite NatSet.union_spec, NatSet.add_spec.
            destruct in_set as [P1 | [ P2 | P3]]; auto.
        + hnf. intros a in_diff.
          rewrite NatSet.diff_spec, NatSet.add_spec in in_diff.
          destruct in_diff as [ in_freeVars no_dVar].
          apply fVars_subset.
          set_tac.
          repeat split; tauto.
    }
    intros vR (elo, ehi) err eval_real A_res.
    assert (vR = vR1)
      by (eapply (meps_0_deterministic (Let REAL n (toRExp e1) (toRExp e2))); eauto); subst.
    inversion eval_real; subst.
    specialize (Hsound DeltaMap deltas_matched).
    apply validErrorBoundsRec_single with (v__R := v1) (iv:= i0) (err:= e0) in Hsound; auto.
    destruct Hsound as [[ve1 [me1 evalExists]] evalHasError].
    assert (validErrorBounds e2 (updEnv n v1 E1) (updEnv n ve1 E2) A Gamma)
      as Hsound2.
    { eapply IHe2; eauto.
      + apply RMicromega.Qeq_true in L0.
        eapply approxUpdBound; try eauto; simpl in *.
        1: eapply (toRExpMap_some _ (Var Q n)); now eauto.
        rewrite <- L0; auto.
        eapply evalHasError; eauto.
      + instantiate (1:= outVars2).
        eapply ssa_outVars_extensible with (outVars1 := outVars2); try eauto;
            [ | set_tac].
        eapply ssa_equal_set; eauto.
        hnf. intros a; split; intros in_set.
        * rewrite NatSet.add_spec, NatSet.union_spec;
            rewrite NatSet.union_spec, NatSet.add_spec in in_set.
          destruct in_set as [P1 | [ P2 | P3]]; auto.
        * rewrite NatSet.add_spec, NatSet.union_spec in in_set;
            rewrite NatSet.union_spec, NatSet.add_spec.
          destruct in_set as [P1 | [ P2 | P3]]; auto.
      + hnf. intros a in_diff.
        rewrite NatSet.diff_spec, NatSet.add_spec in in_diff.
        destruct in_diff as [ in_freeVars no_dVar].
        apply fVars_subset.
        set_tac.
        split; tauto.
    }
    eapply validErrorBoundsRec_single in Hsound2; eauto.
    destruct Hsound2 as [[v2 [m2 eval_fixed]] ?].
    split.
    assert (m = me1) by (eapply validTypes_exec; try exact evalExists; eauto).
    injection find_me; intros Heq. subst.
    + exists v2, me.
      eapply Let_dist with (E:=E2); try eassumption.
      eapply toRExpMap_some with (e2:=toRExp (Let me1 n e1 e2)); eauto.
      destruct valid_types' as (? & ? & ?).
      inversion H1; subst.
      destruct H2 as [(? & ? & ? & ? & ? & ? & ?) ?].
      eapply validTypes_single in H4.
      destruct H4 as (? & ? & ?).
      rewrite H13 in *. inversion H4; subst.
      assert (m2 = x1).
      { eapply H16; eauto. }
      subst. auto.
    + intros * eval_float.
      (* clear eval_fixed. *)
      inversion eval_float; subst.
      (* assert (m = me1) by (eapply validTypes_exec; try exact evalExists; eauto).
      subst. *)
      assert (Herr: Q2R err = Q2R e4).
      { apply RMicromega.Qeq_true in R1.
        rewrite R1. unfold error in *; congruence. }
      rewrite Herr.
      assert (validErrorBounds e2 (updEnv n v1 E1) (updEnv n v0 E2) A Gamma).
      { eapply IHe2; eauto.
        - eapply approxUpdBound; eauto.
          + eapply (toRExpMap_some _ (Var Q n)); eauto.
          + apply RMicromega.Qeq_true in L0. rewrite <- L0. eapply evalHasError; eauto.
        - eapply ssa_equal_set; eauto.
          split; set_tac; tauto.
        - intros a ?. apply fVars_subset. set_tac.
          split; [right| intros ?; apply H2; set_tac].
          split; auto.
          intros ?; subst. apply H2. set_tac. }
      eapply validErrorBoundsRec_single in H1; eauto.
      destruct H1. eapply H2; eauto.
  (* - cbn in *. Flover_compute; congruence. *)
Qed.
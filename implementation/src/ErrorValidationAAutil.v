From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Recdef Reals.Reals.

From Flover
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis
     ExpressionSemantics IntervalValidation TypeValidator RealRangeValidator ErrorBounds
     ErrorValidation AffineForm AffineArithQ AffineArith AffineValidation.

Definition mkErrorPolyQ (err: Q) noise :=
  if Qeq_bool err 0 then
    Const 0
  else
    Noise noise err (Const 0).

Definition mkErrorPolyR (err: R) noise :=
  if Req_dec_sum err 0%R then
    Const 0%R
  else
    Noise noise err (Const 0%R).

Lemma mem_false_find_none V e (expr_map: FloverMap.t (affine_form V)):
  FloverMap.mem e expr_map = false <-> FloverMap.find e expr_map = None.
Proof.
  split; intros Hmem.
  - rewrite FloverMapFacts.P.F.mem_find_b in Hmem.
    destruct FloverMap.find; congruence.
  - rewrite FloverMapFacts.P.F.mem_find_b.
    destruct FloverMap.find; congruence.
Qed.

Lemma afQ2R_mkErrorPolyQ e n:
  afQ2R (mkErrorPolyQ e n) = mkErrorPolyR (Q2R e) n.
Proof.
  cbn.
  unfold mkErrorPolyR, mkErrorPolyQ.
  destruct Req_dec_sum.
  - destruct Qeq_bool eqn: Heq.
    + cbn.
      f_equal; lra.
    + apply Qeq_bool_neq in Heq.
      replace 0%R with (Q2R 0) in e0 by lra.
      apply eqR_Qeq in e0; lra.
  - destruct Qeq_bool eqn: Heq.
    + apply Qeq_bool_iff in Heq.
      apply Qeq_eqR in Heq; lra.
    + cbn; f_equal; f_equal.
      lra.
Qed.

Lemma mkErrorPolyR_fresh_compat e n1 n2:
  (n1 < n2)%nat -> fresh n2 (mkErrorPolyR e n1).
Proof.
  intros Hle.
  unfold fresh, mkErrorPolyR.
  destruct Req_dec_sum; cbn; lia.
Qed.

Lemma toInterval_mkErrorPolyR e n:
  (0 <= e)%R ->
  toInterval (mkErrorPolyR e n) = (-e, e)%R.
Proof.
  intros.
  unfold toInterval, mkErrorPolyR; destruct Req_dec_sum; cbn.
  - subst.
    f_equal; lra.
  - rewrite Rabs_pos_eq; auto.
    f_equal; lra.
Qed.

Lemma get_const_mkErrorPolyR e n:
  get_const (mkErrorPolyR e n) = 0%R.
Proof.
  unfold mkErrorPolyR; destruct Req_dec_sum; now cbn.
Qed.

Lemma toInterval_negate_aff a:
  toInterval (negate_aff a) = (-(snd (toInterval a)), -(fst (toInterval a)))%R.
Proof.
  unfold negate_aff, mult_aff_const, mult_aff.
  remember (a, (Const (-1)%R)) as a12.
  assert (fst a12 = a /\ snd a12 = (Const (-1)%R)) as Havals by now rewrite Heqa12.
  destruct Havals as [Heqa1 Heqa2].
  rewrite <- Heqa1 in *.
  clear Heqa1 Heqa12 a.
  functional induction (mult_aff_aux a12); cbn in *; try congruence.
  - destruct Req_dec_sum; [|lra].
    unfold toInterval.
    cbn.
    repeat rewrite Rminus_0_r.
    repeat rewrite Rplus_0_r.
    inversion Heqa2; subst; clear Heqa2.
    f_equal; lra.
  - specialize (IHa Heqa2).
    destruct (Req_dec_sum (radius a1' * 0) 0); [|lra].
    destruct Req_dec_sum; [|lra].
    unfold toInterval in *.
    cbn in *.
    inversion Heqa2; subst; clear Heqa2.
    inversion IHa; clear IHa.
    field_rewrite ((- (get_const a1' + (Rabs v1 + radius a1'))) = (- (get_const a1' + radius a1')) - Rabs v1)%R.
    field_rewrite ((- (get_const a1' - (Rabs v1 + radius a1'))) = (- (get_const a1' - radius a1')) + Rabs v1)%R.
    rewrite <- H0.
    rewrite <- H1.
    field_rewrite (v1 * -1 = -v1)%R.
    rewrite Rabs_Ropp.
    f_equal; lra.
Qed.

Lemma from_intv_from_interval (l h: Q) n:
  afQ2R (fromIntv (l, h) n) = fromInterval (Q2R l, Q2R h) n.
Proof.
  unfold fromInterval, fromIntv.
  cbn.
  assert (Const (Q2R (h / (2 # 1) + l / (2 # 1))) = Const (Q2R h / 2 + Q2R l / 2)%R) as H'.
  {
    rewrite Q2R_plus; rewrite Q2R_div; try lra.
    rewrite Q2R_div; try lra.
    now field_rewrite (Q2R (2 # 1) = 2)%R.
  }
  destruct (Qeq_bool l h) eqn: Hc.
  - apply Qeq_bool_iff in Hc.
    apply Qeq_eqR in Hc.
    rewrite Hc.
    cbn.
    destruct (Req_dec_sum (Q2R h) (Q2R h)); try contradiction.
    now setoid_rewrite <- Hc at 2.
  - apply Qeq_bool_neq in Hc.
    destruct (Req_dec_sum (Q2R l) (Q2R h)) as [Hc__R|]; try (apply eqR_Qeq in Hc__R; contradiction).
    cbn.
    f_equal; [|assumption].
    rewrite <- Q2R_max.
    repeat rewrite Q2R_minus.
    repeat rewrite Q2R_plus.
    repeat rewrite Q2R_div; try lra.
    now field_rewrite (Q2R (2 # 1) = 2)%R.
Qed.

Lemma computeErrorR_pos x m:
  (0 <= computeErrorR x m)%R.
Proof.
  unfold computeErrorR.
  destruct m; try lra; try (apply Rmult_le_pos; [apply Rabs_pos|apply mTypeToR_pos_R]).
  apply mTypeToR_pos_R.
Qed.

Lemma RmaxAbsFun_symmetric_pos_arg x:
  (0 <= x)%R -> RmaxAbsFun (-x, x)%R = x.
Proof.
  intros Hposx.
  unfold RmaxAbsFun.
  cbn.
  rewrite Rmax_right; [apply Rabs_right|rewrite Rabs_Ropp]; lra.
Qed.

Lemma Rle_Ropp_pos x:
  (0 <= x)%R -> (-x <= x)%R.
Proof.
  intros; lra.
Qed.

Lemma RmaxAbsFun_iv iv x:
  iv = (-x, x)%R -> (0 <= x)%R -> (- RmaxAbsFun iv, RmaxAbsFun iv)%R = iv.
Proof.
  intros Hivsym Hxpos.
  rewrite Hivsym.
  unfold RmaxAbsFun.
  cbn.
  rewrite Rabs_Ropp.
  rewrite Rmax_right; [|apply Rle_refl].
  rewrite Rabs_pos_eq; auto.
Qed.

Lemma const_0_sym a:
  get_const a = 0%R <-> toInterval a = (-(AffineArith.radius a), AffineArith.radius a)%R.
Proof.
  split.
  - intros Hc.
    unfold toInterval.
    rewrite Hc.
    cbn.
    f_equal; lra.
  - intros Hiv.
    unfold toInterval in Hiv.
    cbn in Hiv.
    inversion Hiv; subst; clear Hiv.
    lra.
Qed.

Lemma const_0_plus a1 a2:
  get_const a1 = 0%R ->
  get_const a2 = 0%R ->
  get_const (plus_aff a1 a2) = 0%R.
Proof.
  intros Hc1 Hc2.
  unfold plus_aff.
  remember (a1, a2) as a12.
  assert (fst a12 = a1 /\ snd a12 = a2) as Havals by now rewrite Heqa12.
  destruct Havals as [Heqa1 Heqa2].
  rewrite <- Heqa1 in Hc1.
  rewrite <- Heqa2 in Hc2.
  clear Heqa1 Heqa2 Heqa12 a1 a2.
  functional induction (plus_aff_tuple a12); cbn in *; try lra; now apply IHa.
Qed.

Lemma plus_aff_to_interval_sym_compat af1 af2 v1 v2:
  toInterval af1 = (-v1, v1)%R ->
  toInterval af2 = (-v2, v2)%R ->
  toInterval (plus_aff af1 af2) = (- (radius (plus_aff af1 af2)), (radius (plus_aff af1 af2)))%R.
Proof.
  intros Hiv1 Hiv2.
  unfold toInterval in Hiv1, Hiv2.
  cbn in Hiv1, Hiv2.
  inversion Hiv1; subst; clear Hiv1.
  assert (get_const af1 = 0%R) as Hc1 by lra.
  inversion Hiv2; subst; clear Hiv2.
  assert (get_const af2 = 0%R) as Hc2 by lra.
  pose proof (const_0_plus _ _ Hc1 Hc2) as Hc__p.
  unfold toInterval.
  cbn.
  rewrite Hc__p.
  f_equal; lra.
Qed.

Lemma const_0_mult a1 a2 n:
  get_const a1 = 0%R ->
  get_const a2 = 0%R ->
  get_const (mult_aff a1 a2 n) = 0%R.
Proof.
  intros Hc1 Hc2.
  unfold mult_aff.
  destruct Req_dec_sum as [Heq|Heq].
  Set Default Goal Selector "all".
  remember (a1, a2) as a12.
  assert (fst a12 = a1 /\ snd a12 = a2) as Havals by now rewrite Heqa12.
  destruct Havals as [Heqa1 Heqa2].
  rewrite <- Heqa1 in Hc1.
  rewrite <- Heqa2 in Hc2.
  cbn.
  clear Heqa1 Heqa2 Heqa12 Heq a1 a2.
  functional induction (mult_aff_aux a12); cbn in *; try lra; subst; lra.
  Set Default Goal Selector "1".
Qed.

Lemma const_0_mult_l a1 a2 n:
  get_const a1 = 0%R ->
  get_const (mult_aff a1 a2 n) = 0%R.
Proof.
  intros Hc1.
  unfold mult_aff.
  destruct Req_dec_sum as [Heq|Heq].
  Set Default Goal Selector "all".
  remember (a1, a2) as a12.
  assert (fst a12 = a1 /\ snd a12 = a2) as Havals by now rewrite Heqa12.
  destruct Havals as [Heqa1 Heqa2].
  rewrite <- Heqa1 in Hc1.
  cbn.
  clear Heqa1 Heqa2 Heqa12 Heq a1 a2.
  functional induction (mult_aff_aux a12); cbn in *; try lra; subst; lra.
  Set Default Goal Selector "1".
Qed.

Lemma const_0_mult_r a1 a2 n:
  get_const a2 = 0%R ->
  get_const (mult_aff a1 a2 n) = 0%R.
Proof.
  intros Hc2.
  unfold mult_aff.
  destruct Req_dec_sum as [Heq|Heq].
  Set Default Goal Selector "all".
  remember (a1, a2) as a12.
  assert (fst a12 = a1 /\ snd a12 = a2) as Havals by now rewrite Heqa12.
  destruct Havals as [Heqa1 Heqa2].
  rewrite <- Heqa2 in Hc2.
  cbn.
  clear Heqa1 Heqa2 Heqa12 Heq a1 a2.
  functional induction (mult_aff_aux a12); cbn in *; try lra; subst; lra.
  Set Default Goal Selector "1".
Qed.

Lemma mult_aff_to_interval_sym_compat af1 af2 v1 v2 n:
  toInterval af1 = (-v1, v1)%R ->
  toInterval af2 = (-v2, v2)%R ->
  toInterval (mult_aff af1 af2 n) =
  (- (radius (mult_aff af1 af2 n)), (radius (mult_aff af1 af2 n)))%R.
Proof.
  intros Hiv1 Hiv2.
  unfold toInterval in Hiv1, Hiv2.
  cbn in Hiv1, Hiv2.
  inversion Hiv1; subst; clear Hiv1.
  assert (get_const af1 = 0%R) as Hc1 by lra.
  inversion Hiv2; subst; clear Hiv2.
  assert (get_const af2 = 0%R) as Hc2 by lra.
  pose proof (const_0_mult _ _ n Hc1 Hc2) as Hc__p.
  unfold toInterval.
  cbn.
  rewrite Hc__p.
  f_equal; lra.
Qed.

Lemma mult_aff_to_interval_sym_compat_l af1 af2 v1 n:
  toInterval af1 = (-v1, v1)%R ->
  toInterval (mult_aff af1 af2 n) =
  (- (radius (mult_aff af1 af2 n)), (radius (mult_aff af1 af2 n)))%R.
Proof.
  intros Hiv1.
  unfold toInterval in Hiv1.
  cbn in Hiv1.
  inversion Hiv1; subst; clear Hiv1.
  assert (get_const af1 = 0%R) as Hc1 by lra.
  pose proof (const_0_mult_l _ af2 n Hc1) as Hc__p.
  unfold toInterval.
  cbn.
  rewrite Hc__p.
  f_equal; lra.
Qed.

Lemma mult_aff_to_interval_sym_compat_r af1 af2 v2 n:
  toInterval af2 = (-v2, v2)%R ->
  toInterval (mult_aff af1 af2 n) =
  (- (radius (mult_aff af1 af2 n)), (radius (mult_aff af1 af2 n)))%R.
Proof.
  intros Hiv2.
  unfold toInterval in Hiv2.
  cbn in Hiv2.
  inversion Hiv2; subst; clear Hiv2.
  assert (get_const af2 = 0%R) as Hc2 by lra.
  pose proof (const_0_mult_r af1 _ n Hc2) as Hc__p.
  unfold toInterval.
  cbn.
  rewrite Hc__p.
  f_equal; lra.
Qed.

Lemma negate_aff_to_interval_sym_compat a v:
  toInterval a = (-v, v)%R ->
  toInterval (negate_aff a) = toInterval a.
Proof.
  intros Hiv.
  rewrite toInterval_negate_aff.
  rewrite Hiv.
  cbn; f_equal; lra.
Qed.

Lemma subtract_aff_to_interval_sym_compat af1 af2 v1 v2:
  toInterval af1 = (-v1, v1)%R ->
  toInterval af2 = (-v2, v2)%R ->
  toInterval (subtract_aff af1 af2) =
  (- (radius (subtract_aff af1 af2)), (radius (subtract_aff af1 af2)))%R.
Proof.
  intros Hiv1 Hiv2.
  unfold subtract_aff.
  eapply plus_aff_to_interval_sym_compat with (v1 := v1); eauto.
  rewrite <- Hiv2.
  erewrite negate_aff_to_interval_sym_compat; eauto.
Qed.

Lemma plus_aff_0_r a:
  plus_aff a (Const 0%R) = a.
Proof.
  unfold plus_aff.
  remember (a, (Const 0%R)) as a12.
  assert (fst a12 = a /\ snd a12 = (Const 0%R)) as Havals by now rewrite Heqa12.
  destruct Havals as [Heqa1 Heqa2].
  rewrite <- Heqa1.
  clear Heqa1 Heqa12 a.
  functional induction (plus_aff_tuple a12); cbn in *; try congruence.
  - f_equal.
    inversion Heqa2; lra.
  - inversion Heqa2; subst; clear Heqa2.
    specialize (IHa ltac:(reflexivity)).
    now rewrite IHa.
Qed.

Lemma radius_plus_from_interval a x n:
  fresh n a ->
  (0 <= x)%R ->
  radius (plus_aff a (fromInterval (-x, x) n))%R = ((radius a) + x)%R.
Proof.
  intros Hfresh Hxpos.
  induction a.
  - unfold fromInterval; cbn.
    destruct Req_dec_sum; cbn.
    + lra.
    + field_rewrite (x / 2 + - x / 2 = 0)%R.
      rewrite Rmax_right; try lra.
      rewrite Rabs_pos_eq; lra.
  - assert (n0 < n)%nat as Hlt.
    {
      unfold fresh in Hfresh.
      cbn in Hfresh.
      eapply Nat.le_lt_trans; try exact Hfresh.
      apply get_mia_monotonic.
    }
    apply fresh_noise_compat in Hfresh.
    specialize (IHa Hfresh).
    unfold plus_aff.
    unfold fromInterval in *; cbn in *.
    destruct Req_dec_sum; field_rewrite (Rabs v + radius a + x = radius a + x + Rabs v)%R.
    + rewrite <- IHa.
      replace x with 0%R by lra.
      unfold plus_aff; rewrite plus_aff_tuple_equation; cbn.
      lra.
    + field_rewrite (x / 2 + - x / 2 = 0)%R.
      rewrite Rmax_right; try lra.
      unfold plus_aff.
      rewrite plus_aff_tuple_equation.
      assert (n0 <> n) as Hneq by lia.
      rewrite <- Nat.eqb_neq in Hneq.
      rewrite Hneq.
      rewrite <- Nat.ltb_lt in Hlt.
      rewrite Hlt.
      cbn.
      rewrite plus_aff_tuple_equation.
      cbn.
      rewrite Rabs_pos_eq; try lra.
      rewrite Rminus_0_r.
      field_rewrite (x + (Rabs v + radius (plus_aff_tuple (a, Const 0))) =
                     x + radius (plus_aff_tuple (a, Const 0)) + Rabs v)%R.
      f_equal.
      replace (plus_aff_tuple (a, Const 0%R)) with (plus_aff a (Const 0%R)) by trivial.
      rewrite plus_aff_0_r.
      lra.
Qed.

Lemma af_evals_from_interval_updMap iv noise map vR:
  ((fst iv) <= vR <= (snd iv))%R ->
  exists q : noise_type,
    af_evals (fromInterval iv noise) vR (updMap map noise q).
Proof.
  intros interval_containment.
  destruct (Req_dec (IVlo iv) (IVhi iv)) as [Heq|Heq].
  {
    exists noise_zero.
    unfold af_evals, fromInterval.
    rewrite Heq.
    cbn.
    destruct Req_dec_sum; [|lra].
    cbn in Heq |-*.
    lra.
  }
  unfold af_evals, fromInterval.
  destruct Req_dec_sum; [lra|].
  cbn in Heq |-*.
  setoid_rewrite upd_sound.
  simpl.
  apply Rmax_case_strong.
  - intros Hmax.
    pose (l := fst iv).
    pose (h := snd iv).
    fold l h in Hmax, interval_containment, Heq |-*.
    pose (noise_expression := ((vR - h / 2 - l / 2) / (h / 2 + l / 2 - l))%R).
    assert (-(1) <= noise_expression <= 1)%R as Hnoise.
    {
      unfold noise_expression.
      apply Rabs_Rle_condition.
      destruct (Rle_lt_dec (h / 2 + l / 2 - l) 0)%R as [Hle0 | Hle0].
      - apply Rle_lt_or_eq_dec in Hle0; destruct Hle0 as [Hlt | Hlt];
          try (field_simplify in Hlt; assert (h = l) as Hz by lra; lra).
      - rewrite Rdiv_abs_le_bounds; try lra.
        assert (0 < h - l)%R as H1 by lra.
        field_rewrite (vR - h / 2 - l /2 = vR - (h + l) / 2)%R.
        field_rewrite (1 * (h / 2 + l / 2 - l) = (h - l) / 2)%R.
        apply Rabs_Rle_condition; lra.
    }
    rename noise into inoise.
    pose (noise := exist (fun x => -(1) <= x <= 1)%R noise_expression Hnoise).
    exists noise.
    unfold noise, noise_expression.
    simpl.
    field.
    intros Hnotz.
    field_simplify in Hnotz.
    assert (h = l) as Hz by lra.
    lra.
  - intros Hmax.
    pose (l := fst iv).
    pose (h := snd iv).
    fold l h in Hmax, interval_containment, Heq |-*.
    pose (noise_expression := ((vR - h / 2 - l / 2) / (h / 2 + l / 2 - l))%R).
    assert (-(1) <= noise_expression <= 1)%R as Hnoise.
    {
      unfold noise_expression.
      apply Rabs_Rle_condition.
      destruct (Rle_lt_dec (h / 2 + l / 2 - l) 0)%R as [Hle0 | Hle0].
      - apply Rle_lt_or_eq_dec in Hle0; destruct Hle0 as [Hlt | Hlt];
          try (field_simplify in Hlt; assert (h = l) as Hz by lra; lra).
      - rewrite Rdiv_abs_le_bounds; try lra.
        assert (0 < h - l)%R as H1 by lra.
        field_rewrite (vR - h / 2 - l /2 = vR - (h + l) / 2)%R.
        field_rewrite (1 * (h / 2 + l / 2 - l) = (h - l) / 2)%R.
        apply Rabs_Rle_condition; lra.
    }
    rename noise into inoise.
    pose (noise := exist (fun x => -(1) <= x <= 1)%R noise_expression Hnoise).
    exists noise.
    unfold noise, noise_expression.
    simpl.
    field.
    intros Hnotz.
    field_simplify in Hnotz.
    assert (h = l) as Hz by lra.
    lra.
Qed.

Lemma af_evals_mkErrorPolyR_updMap e noise map vR:
  (0 <= e)%R ->
  (Rabs vR <= e)%R ->
  exists q : noise_type,
    af_evals (mkErrorPolyR e noise) vR (updMap map noise q).
Proof.
  intros Hepos Hbounds.
  replace (mkErrorPolyR e noise) with (fromInterval (-e, e)%R noise).
  - apply af_evals_from_interval_updMap; cbn; now rewrite <- Rabs_Rle_condition.
  - unfold mkErrorPolyR, fromInterval; cbn.
    destruct Req_dec_sum.
    + destruct Req_dec_sum; f_equal; lra.
    + destruct Req_dec_sum; try lra.
      f_equal; f_equal; try lra.
      rewrite Rmax_right; lra.
Qed.

Lemma af_evals_updMap_compat a map n q v:
  fresh n a ->
  af_evals a v map <-> af_evals a v (updMap map n q).
Proof.
  intros Hfresh.
  unfold af_evals.
  erewrite eval_updMap_compat with (n := n) (q := q); eauto.
  reflexivity.
Qed.

Lemma RmaxAbsFun_pos iv:
  (0 <= RmaxAbsFun iv)%R.
Proof.
  unfold RmaxAbsFun.
  apply Rmax_case_strong; intros; apply Rabs_pos.
Qed.

Lemma Q2R_Q2RP_fst iv:
  Q2R (fst iv) = fst (Q2RP iv).
Proof.
  now destruct iv.
Qed.

Lemma Q2R_Q2RP_snd iv:
  Q2R (snd iv) = snd (Q2RP iv).
Proof.
  now destruct iv.
Qed.

Lemma Q2RP_addIntv iv1 iv2:
  Q2RP (addIntv iv1 iv2) = addInterval (Q2RP iv1) (Q2RP iv2).
Proof.
  cbn; unfold addInterval, absIntvUpd.
  rewrite Q2R_min4, Q2R_max4.
  repeat rewrite Q2R_plus.
  now destruct iv1, iv2; cbn.
Qed.

Lemma Q2RP_subtractIntv iv1 iv2:
  Q2RP (subtractIntv iv1 iv2) = subtractInterval (Q2RP iv1) (Q2RP iv2).
Proof.
  cbn; unfold subtractInterval, absIntvUpd.
  rewrite Q2R_min4, Q2R_max4.
  repeat rewrite Q2R_plus.
  repeat rewrite Q2R_opp.
  now destruct iv1, iv2; cbn.
Qed.

Lemma Q2RP_multIntv iv1 iv2:
  Q2RP (multIntv iv1 iv2) = multInterval (Q2RP iv1) (Q2RP iv2).
Proof.
  cbn; unfold multInterval, absIntvUpd.
  rewrite Q2R_min4, Q2R_max4.
  repeat rewrite Q2R_mult.
  now destruct iv1, iv2; cbn.
Qed.

Lemma Q2RP_invertIntv iv:
  ~ fst iv == 0 ->
  ~ snd iv == 0 ->
  Q2RP (invertIntv iv) = invertInterval (Q2RP iv).
Proof.
  intros.
  cbn; unfold invertInterval, mkInterval.
  repeat rewrite Q2R_inv; auto.
  now destruct iv; cbn.
Qed.

Lemma Q2RP_divideIntv iv1 iv2:
  ~ fst iv2 == 0 ->
  ~ snd iv2 == 0 ->
  Q2RP (divideIntv iv1 iv2) = divideInterval (Q2RP iv1) (Q2RP iv2).
Proof.
  intros.
  cbn; unfold divideInterval, absIntvUpd.
  rewrite Q2R_min4, Q2R_max4.
  repeat rewrite Q2R_mult.
  repeat rewrite Q2R_inv; auto.
  now destruct iv1, iv2; cbn.
Qed.

Lemma Q2RP_widenIntv iv v:
  Q2RP (widenIntv iv v) = widenInterval (Q2RP iv) (Q2R v).
Proof.
  unfold widenInterval, mkInterval.
  destruct iv; cbn.
  repeat rewrite Q2R_minus.
  now repeat rewrite Q2R_plus.
Qed.

Lemma perturb_destr: forall P v m d,
    P (perturb v m d) <->
    (m = REAL /\ (P v)) \/
    (exists w f, m = F w f /\ P (v + d))%R \/
    (m <> REAL /\ (forall w f, m <> F w f) /\ P (v * (1 + d)))%R.
Proof.
  intros.
  split; intros; destruct m; cbn in *; try congruence.
  1-6:firstorder.
  2-6: (intuition; try congruence;
    destruct H as (? & ? &? & ?); congruence).
  right; left; repeat eexists; eauto.
Qed.

Lemma perturb_csplit: forall (P: R -> Prop) v m d,
    (m = REAL -> P v) ->
    (forall w f, m = F w f -> P (v + d)%R) ->
    ((forall w f, m <> F w f) -> m <> REAL -> P (v * (1 + d))%R) ->
    P (perturb v m d).
Proof.
  intros. rewrite perturb_destr.
  destruct m.
  2-4: right; right; intuition; try congruence;
    apply H1; congruence.
  - intuition.
  - right; left; repeat eexists; eauto.
Qed.

Lemma computeErrorR_csplit: forall (P: R -> Prop) v m,
    (m = REAL -> P 0%R) ->
    (forall w f, m = F w f -> P (mTypeToR m)%R) ->
    ((forall w f, m <> F w f) -> m <> REAL -> P (Rabs v * mTypeToR m)%R) ->
    P (computeErrorR v m).
Proof.
  intros.
  destruct m; auto.
  1-3: apply H1; congruence.
  eapply H0; eauto.
Qed.

Lemma contained' a v1 v2 e e' l h map:
  (l <= v1 <= h)%R ->
  af_evals a (v1 - v2)%R map ->
  toInterval a = ((- e)%R, e) ->
  (e <= e')%R ->
  (l - e' <= v2 <= h + e')%R.
Proof.
  intros ? H1 H2 ?.
  apply to_interval_containment in H1.
  rewrite H2 in H1.
  cbn in H1.
  lra.
Qed.

Lemma one_half_pow_N_pos f:
  (0 <= 1 / 2 ^ N.to_nat f)%R.
Proof.
  replace (1 / 2 ^ N.to_nat f)%R with ((1 / 2) ^ N.to_nat f)%R.
  + apply pow_le; lra.
  + unfold Rdiv.
    rewrite Rinv_pow; try lra.
    rewrite Rpow_mult_distr.
    f_equal.
    apply pow1.
Qed.

Lemma plus_error_aff_af_evals
      af v1 v2 iv m delta noise1 noise_map1 noise_map' noise':
  af_evals af (v1 - v2) noise_map' ->
  fresh noise' af ->
  (noise1 <= noise')%nat ->
  (forall n' : nat, (noise' <= n')%nat -> noise_map' n' = None) ->
  contained_map noise_map1 noise_map' ->
  (Rabs delta <= mTypeToR m)%R ->
  contained v2 (Q2RP iv) ->
  exists noise_map2,
    contained_map noise_map1 noise_map2 /\
    (forall n, noise' + 1 <= n -> noise_map2 n = None)%nat /\
    fresh (noise' + 1) (plus_aff af (mkErrorPolyR (computeErrorR (Q2R (maxAbs iv)) m) noise')) /\
    af_evals
      (plus_aff af (mkErrorPolyR (computeErrorR (Q2R (maxAbs iv)) m) noise'))
      (v1 - perturb v2 m delta) noise_map2.
Proof.
  intros.
  apply perturb_csplit; intros; subst.
  - exists (updMap noise_map' noise' noise_zero).
    repeat split; auto.
    + eapply contained_map_trans; eauto.
      apply contained_map_extension; auto.
    + intros; unfold updMap.
      destruct (n =? noise') eqn: Heq.
      * apply beq_nat_true in Heq.
        lia.
      * apply H2; lia.
    + apply plus_aff_fresh_compat.
      * apply fresh_monotonic with (n := noise'); auto; lia.
      * apply mkErrorPolyR_fresh_compat; lia.
    + field_rewrite (v1 - v2 = (v1 - v2) + 0)%R.
      apply plus_aff_sound.
      * apply af_evals_updMap_compat; eauto using fresh_monotonic, af_evals_map_extension.
      * unfold mkErrorPolyR.
        cbn; destruct Req_dec_sum; cbn; lra.
  - field_rewrite (v1 - (v2 + delta) = (v1 - v2) - delta)%R.
    pose proof (@af_evals_mkErrorPolyR_updMap (computeErrorR (Q2R (maxAbs iv)) (F w f)) noise' noise_map' (- delta)%R) as Hevalsiv.
    cbn in Hevalsiv.
    destruct Hevalsiv as (q & Hevalsiv); try rewrite Rabs_Ropp;
      auto using computeErrorR_pos, one_half_pow_N_pos.
    exists (updMap noise_map' noise' q); cbn.
    repeat split; auto.
    + eapply contained_map_trans; eauto.
      apply contained_map_extension; auto.
    + intros; unfold updMap.
      destruct (n =? noise') eqn: Heq.
      * apply beq_nat_true in Heq.
        lia.
      * apply H2; lia.
    + apply plus_aff_fresh_compat.
      * apply fresh_monotonic with (n := noise'); auto; lia.
      * apply mkErrorPolyR_fresh_compat; lia.
    + apply plus_aff_sound; auto.
      apply af_evals_updMap_compat; eauto using fresh_monotonic, af_evals_map_extension.
  - field_rewrite (v1 - v2 * (1 + delta) = (v1 - v2) - v2 * delta)%R.
    apply computeErrorR_csplit; try congruence; intros _ _.
    pose proof (@af_evals_mkErrorPolyR_updMap (Rabs (Q2R (maxAbs iv)) * mTypeToR m)
                                              noise' noise_map' (- (v2 * delta))%R) as Hevalsiv.
    destruct Hevalsiv as (q & Hevalsiv);
      auto using computeErrorR_pos, Rmult_le_pos, Rabs_pos, mTypeToR_pos_R.
    {
      rewrite Ropp_mult_distr_l.
      rewrite Rabs_mult.
      rewrite Rabs_Ropp.
      apply Rmult_le_compat; auto using Rabs_pos.
      rewrite <- maxAbs_impl_RmaxAbs_iv.
      setoid_rewrite Rabs_right at 2; eauto using Rle_ge, RmaxAbsFun_pos.
      apply contained_leq_maxAbs;
        destruct iv; cbn in *;
          try rewrite Q2R_minus, Q2R_plus; eauto.
    }
    exists (updMap noise_map' noise' q).
    repeat split; auto.
    + eapply contained_map_trans; eauto.
      apply contained_map_extension; auto.
    + intros; unfold updMap.
      destruct (n =? noise') eqn: Heq.
      * apply beq_nat_true in Heq.
        lia.
      * apply H2; lia.
    + apply plus_aff_fresh_compat.
      * apply fresh_monotonic with (n := noise'); auto; lia.
      * apply mkErrorPolyR_fresh_compat; lia.
    + apply plus_aff_sound; auto.
      apply af_evals_updMap_compat; eauto using fresh_monotonic, af_evals_map_extension.
Qed.

Lemma addition_error_af_evals
      af1 af2 v__R1 v__R2 v__FP1 v__FP2 iv1 iv2 err1 err2 bound1 bound2 m delta noise noise_map:
  af_evals (afQ2R af1) (v__R1 - v__FP1) noise_map ->
  af_evals (afQ2R af2) (v__R2 - v__FP2) noise_map ->
  fresh noise (afQ2R af1) ->
  fresh noise (afQ2R af2) ->
  (forall n' : nat, (noise <= n')%nat -> noise_map n' = None) ->
  (Rabs delta <= mTypeToR m)%R ->
  (bound1 <= Q2R err1)%R ->
  toInterval (afQ2R af1) = ((- bound1)%R, bound1) ->
  (bound2 <= Q2R err2)%R ->
  toInterval (afQ2R af2) = ((- bound2)%R, bound2) ->
  (Q2R (fst iv1) <= v__R1 <= Q2R (snd iv1))%R ->
  (Q2R (fst iv2) <= v__R2 <= Q2R (snd iv2))%R ->
  exists noise_map',
    contained_map noise_map noise_map' /\
    (forall n, (noise + 1) <= n -> noise_map' n = None)%nat /\
    fresh (noise + 1) (plus_aff (plus_aff (afQ2R af1) (afQ2R af2))
                           (mkErrorPolyR (computeErrorR (Q2R (maxAbs (addIntv (widenIntv iv1 err1)
                                                                              (widenIntv iv2 err2))))
                                                        m) noise)) /\
    af_evals
      (plus_aff (plus_aff (afQ2R af1) (afQ2R af2))
                (mkErrorPolyR (computeErrorR (Q2R (maxAbs (addIntv (widenIntv iv1 err1)
                                                                   (widenIntv iv2 err2))))
                                             m) noise))
      (v__R1 + v__R2 - perturb (v__FP1 + v__FP2) m delta) noise_map'.
Proof.
  intros.
  eapply plus_error_aff_af_evals with (noise_map' := noise_map); eauto.
  - field_rewrite (v__R1 + v__R2 - (v__FP1 + v__FP2) = ((v__R1 - v__FP1) + (v__R2 - v__FP2)))%R.
    apply plus_aff_sound; auto.
  - apply plus_aff_fresh_compat; auto.
  - reflexivity.
  - rewrite Q2RP_addIntv.
    apply interval_addition_valid;
      destruct iv1, iv2; cbn in *;
        try rewrite Q2R_minus, Q2R_plus; eapply contained'; eauto.
Qed.

Lemma subtraction_error_af_evals
      af1 af2 v__R1 v__R2 v__FP1 v__FP2 iv1 iv2 err1 err2 bound1 bound2 m delta noise noise_map:
  af_evals (afQ2R af1) (v__R1 - v__FP1) noise_map ->
  af_evals (afQ2R af2) (v__R2 - v__FP2) noise_map ->
  fresh noise (afQ2R af1) ->
  fresh noise (afQ2R af2) ->
  (forall n' : nat, (noise <= n')%nat -> noise_map n' = None) ->
  (Rabs delta <= mTypeToR m)%R ->
  (bound1 <= Q2R err1)%R ->
  toInterval (afQ2R af1) = ((- bound1)%R, bound1) ->
  (bound2 <= Q2R err2)%R ->
  toInterval (afQ2R af2) = ((- bound2)%R, bound2) ->
  (Q2R (fst iv1) <= v__R1 <= Q2R (snd iv1))%R ->
  (Q2R (fst iv2) <= v__R2 <= Q2R (snd iv2))%R ->
  exists noise_map',
    contained_map noise_map noise_map' /\
    (forall n, (noise + 1) <= n -> noise_map' n = None)%nat /\
    fresh (noise + 1) (plus_aff (subtract_aff (afQ2R af1) (afQ2R af2))
                           (mkErrorPolyR (computeErrorR
                                            (Q2R (maxAbs (subtractIntv (widenIntv iv1 err1)
                                                                       (widenIntv iv2 err2))))
                                            m) noise)) /\
    af_evals
      (plus_aff (subtract_aff (afQ2R af1) (afQ2R af2))
                (mkErrorPolyR (computeErrorR (Q2R (maxAbs (subtractIntv (widenIntv iv1 err1)
                                                                        (widenIntv iv2 err2))))
                                             m) noise))
      (v__R1 - v__R2 - perturb (v__FP1 - v__FP2) m delta) noise_map'.
Proof.
  intros.
  eapply plus_error_aff_af_evals with (noise_map' := noise_map); eauto.
  - field_rewrite (v__R1 - v__R2 - (v__FP1 - v__FP2) = ((v__R1 - v__FP1) - (v__R2 - v__FP2)))%R.
    apply subtract_aff_sound; auto.
  - apply plus_aff_fresh_compat; auto; apply mult_aff_const_fresh_compat; auto.
  - reflexivity.
  - rewrite Q2RP_subtractIntv.
    apply interval_subtraction_valid;
      destruct iv1, iv2; cbn in *;
        try rewrite Q2R_minus, Q2R_plus; eapply contained'; eauto.
Qed.

Fixpoint updMap_n init map n noise :=
  match n with
  | O => map
  | S n' => updMap (updMap_n init map n' noise) (init + n)%nat noise
  end.

Lemma mult_aff_0_r a1 v a2 n map:
  af_evals a1 v map ->
  af_evals a2 0%R map ->
  fresh n a1 ->
  fresh n a2 ->
  exists q, af_evals (mult_aff a1 a2 n) 0%R (updMap map n q).
Proof.
  intros.
  field_rewrite (0 = v * 0)%R.
  eapply mult_aff_sound; eauto.
Qed.

Lemma mult_aff_0_l a1 v a2 n map:
  af_evals a1 0%R map ->
  af_evals a2 v map ->
  fresh n a1 ->
  fresh n a2 ->
  exists q, af_evals (mult_aff a1 a2 n) 0%R (updMap map n q).
Proof.
  intros.
  field_rewrite (0 = 0 * v)%R.
  eapply mult_aff_sound; eauto.
Qed.

Lemma mult_aff_sound' a1 a2 v1 v2 map n m:
  af_evals a1 v1 map ->
  af_evals a2 v2 map ->
  (forall n', n <= n' -> map n' = None)%nat ->
  (1 <= m)%nat ->
  fresh n a1 ->
  fresh n a2 ->
  exists map', contained_map map map' /\
          (forall n', n + m <= n' -> map' n' = None)%nat /\
          af_evals (mult_aff a1 a2 n) (v1 * v2)%R map'.
Proof.
  intros.
  edestruct mult_aff_sound with (a1 := a1) (v1 := v1) as [q Hmult]; eauto.
  exists (updMap map n q).
  repeat split; auto.
  - apply contained_map_extension; auto.
  - intros.
    unfold updMap.
    destruct Nat.eqb eqn: Heq.
    + apply Nat.eqb_eq in Heq.
      lia.
    + apply H1.
      lia.
Qed.

Lemma plus_aff_sound' a1 a2 v1 v2 map n m:
  af_evals a1 v1 map ->
  af_evals a2 v2 map ->
  (forall n', n <= n' -> map n' = None)%nat ->
  exists map', contained_map map map' /\
          (forall n', n + m <= n' -> map' n' = None)%nat /\
          af_evals (plus_aff a1 a2) (v1 + v2)%R map'.
Proof.
  intros.
  exists map.
  repeat split; eauto using contained_map_refl, plus_aff_sound.
  intros.
  apply H1.
  lia.
Qed.

Lemma fresh_from_intv n m iv:
  (n < m)%nat ->
  fresh m (fromIntv iv n).
Proof.
  intros.
  unfold fresh, get_max_index, fromIntv.
  destruct Qeq_bool; cbn; lia.
Qed.

Lemma mult_aff_fresh_compat a1 a2 n m:
  fresh m a1 ->
  fresh m a2 ->
  (m < n)%nat ->
  fresh n (mult_aff a1 a2 m).
Proof.
  intros Hfresh1 Hfresh2 Hle.
  unfold mult_aff.
  destruct Req_dec_sum;
    eauto 7 using fresh_noise, mult_aff_aux_fresh_compat, fresh_monotonic.
Qed.

Lemma updMap_noise_incr noise_map n noise:
  (forall n', (n <= n')%nat -> noise_map n' = None) ->
  (forall n', (n + 1 <= n')%nat -> updMap noise_map n noise n' = None).
Proof.
  intros.
  unfold updMap.
  assert (n' <> n)%nat as Hneq by lia.
  rewrite <- Nat.eqb_neq in Hneq.
  rewrite Hneq.
  apply H; lia.
Qed.

Lemma multiplication_error_af_evals
      af1 af2 v__R1 v__R2 v__FP1 v__FP2 iv1 iv2 err1 err2 bound1 bound2 m delta noise noise_map:
  af_evals (afQ2R af1) (v__R1 - v__FP1) noise_map ->
  af_evals (afQ2R af2) (v__R2 - v__FP2) noise_map ->
  fresh noise (afQ2R af1) ->
  fresh noise (afQ2R af2) ->
  (forall n' : nat, (noise <= n')%nat -> noise_map n' = None) ->
  (Rabs delta <= mTypeToR m)%R ->
  (bound1 <= Q2R err1)%R ->
  toInterval (afQ2R af1) = ((- bound1)%R, bound1) ->
  (bound2 <= Q2R err2)%R ->
  toInterval (afQ2R af2) = ((- bound2)%R, bound2) ->
  (Q2R (fst iv1) <= v__R1 <= Q2R (snd iv1))%R ->
  (Q2R (fst iv2) <= v__R2 <= Q2R (snd iv2))%R ->
  exists noise_map',
    contained_map noise_map noise_map' /\
    (forall n, (noise + 6) <= n -> noise_map' n = None)%nat /\
    fresh (noise + 6) (plus_aff
         (subtract_aff
            (plus_aff
               (mult_aff (afQ2R (fromIntv iv1 noise)) (afQ2R af2) (noise + 2))
               (mult_aff (afQ2R (fromIntv iv2 (noise + 1))) (afQ2R af1) (noise + 3)))
            (mult_aff (afQ2R af1) (afQ2R af2) (noise + 4)))
         (mkErrorPolyR
            (computeErrorR (Q2R (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m)
            (noise + 5))) /\
    af_evals
      (plus_aff
         (subtract_aff
            (plus_aff
               (mult_aff (afQ2R (fromIntv iv1 noise)) (afQ2R af2) (noise + 2))
               (mult_aff (afQ2R (fromIntv iv2 (noise + 1))) (afQ2R af1) (noise + 3)))
            (mult_aff (afQ2R af1) (afQ2R af2) (noise + 4)))
         (mkErrorPolyR
            (computeErrorR (Q2R (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m)
            (noise + 5)))
      (v__R1 * v__R2 - perturb (v__FP1 * v__FP2) m delta) noise_map'.
Proof.
  intros.
  destruct (@af_evals_afQ2R_from_intv_updMap iv1 noise noise_map v__R1) as [q1 Hevalsiv1]; auto.
  pose (noise_map1 := updMap noise_map noise q1).
  assert (contained_map noise_map noise_map1)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 1 <= n')%nat -> noise_map1 n' = None)
    by (apply updMap_noise_incr; auto).
  destruct (@af_evals_afQ2R_from_intv_updMap iv2 (noise + 1)%nat noise_map1 v__R2) as [q2 Hevalsiv2]; auto.
  pose (noise_map2 := updMap noise_map1 (noise + 1)%nat q2).
  assert (contained_map noise_map1 noise_map2)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 1 + 1 <= n')%nat -> noise_map2 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 1 + 1)%nat with (noise + 2)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R (fromIntv iv1 noise)) (afQ2R af2) v__R1
                            (v__R2 - v__FP2) noise_map2 (noise + 2)%nat)%R as [q3 Hevalsmult1];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  1: (eapply fresh_monotonic with (n := noise); eauto; lia).
  pose (noise_map3 := updMap noise_map2 (noise + 2) q3).
  assert (contained_map noise_map2 noise_map3)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 2 + 1 <= n')%nat -> noise_map3 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 2 + 1)%nat with (noise + 3)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R (fromIntv iv2 (noise + 1))) (afQ2R af1) v__R2
                            (v__R1 - v__FP1) noise_map3 (noise + 3)%nat)%R as [q4 Hevalsmult2];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  1: (eapply fresh_monotonic with (n := noise); eauto; lia).
  pose (noise_map4 := updMap noise_map3 (noise + 3) q4).
  assert (contained_map noise_map3 noise_map4)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 3 + 1 <= n')%nat -> noise_map4 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 3 + 1)%nat with (noise + 4)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R af1) (afQ2R af2) (v__R1 - v__FP1) (v__R2 - v__FP2)
                            noise_map4 (noise + 4)%nat)%R as [q5 Hevalsmult3];
    eauto using fresh_monotonic, af_evals_map_extension.
  1-2: (eapply fresh_monotonic with (n := noise); eauto; lia).
  apply af_evals_map_extension with (map2 := noise_map4) in Hevalsmult1; auto.
  pose proof (plus_aff_sound _ _ _ _ _ Hevalsmult1 Hevalsmult2) as Hevalsplus1.
  pose (noise_map5 := updMap noise_map4 (noise + 4) q5).
  assert (contained_map noise_map4 noise_map5)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 4 + 1 <= n')%nat -> noise_map5 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 4 + 1)%nat with (noise + 5)%nat in * by lia.
  apply af_evals_map_extension with (map2 := noise_map5) in Hevalsplus1; auto.
  pose proof (subtract_aff_sound _ _ _ _ _ Hevalsplus1 Hevalsmult3) as Hevalsplus2.
  cbn.
  replace (noise + 6)%nat with (noise + 5 + 1)%nat by lia.
  eapply plus_error_aff_af_evals with (noise_map' := noise_map5) (noise' := (noise + 5)%nat); eauto.
  - field_rewrite (v__R1 * v__R2 - (v__FP1 * v__FP2) = (((v__R1 * (v__R2 - v__FP2)) + (v__R2 * (v__R1 - v__FP1)))
                                                - ((v__R1 - v__FP1) * (v__R2 - v__FP2))))%R; auto.
  - apply plus_aff_fresh_compat.
    + apply plus_aff_fresh_compat;
        apply mult_aff_fresh_compat; try lia.
      * rewrite <- afQ2R_fresh; apply fresh_from_intv; lia.
      * apply fresh_monotonic with (n := noise); eauto; lia.
      * rewrite <- afQ2R_fresh; apply fresh_from_intv; lia.
      * apply fresh_monotonic with (n := noise); eauto; lia.
    + apply mult_aff_const_fresh_compat.
      apply mult_aff_fresh_compat; try lia;
        apply fresh_monotonic with (n := noise); eauto; lia.
  - eauto using contained_map_trans.
  - rewrite Q2RP_multIntv; apply interval_multiplication_valid;
      destruct iv1, iv2; cbn in *;
        try rewrite Q2R_minus, Q2R_plus; eapply contained'; eauto.
Qed.

Lemma Qmin4_nonzero a b c d:
  ~ a == 0 ->
  ~ b == 0 ->
  ~ c == 0 ->
  ~ d == 0 ->
  ~ IntervalArithQ.min4 a b c d == 0.
Proof.
  intros.
  unfold IntervalArithQ.min4.
  do 3 (apply Q.min_case; auto; intros; try lra).
Qed.

Lemma Qmax4_nonzero a b c d:
  ~ a == 0 ->
  ~ b == 0 ->
  ~ c == 0 ->
  ~ d == 0 ->
  ~ IntervalArithQ.max4 a b c d == 0.
Proof.
  intros.
  unfold IntervalArithQ.max4.
  do 3 (apply Q.max_case; auto; intros; try lra).
Qed.

Lemma Rmin4_ltzero a b c d:
  (0 < a)%R ->
  (0 < b)%R ->
  (0 < c)%R ->
  (0 < d)%R ->
  (0 < min4 a b c d)%R.
Proof.
  intros.
  unfold min4.
  do 3 (apply Rmin_case; auto; intros; try lra).
Qed.

Lemma Qmult_Qeq_0_neq a b:
  ~ a == 0 ->
  ~ b == 0 ->
  ~ a * b == 0.
Proof.
  intros Ha Hb Hab.
  eapply Qmult_integral_l in Ha; eauto.
Qed.

Lemma division_error_af_evals
      af1 af2 v__R1 v__R2 v__FP1 v__FP2 iv1 iv2 err1 err2 bound1 bound2 m delta noise noise_map:
  af_evals (afQ2R af1) (v__R1 - v__FP1) noise_map ->
  af_evals (afQ2R af2) (v__R2 - v__FP2) noise_map ->
  fresh noise (afQ2R af1) ->
  fresh noise (afQ2R af2) ->
  (forall n' : nat, (noise <= n')%nat -> noise_map n' = None) ->
  (Rabs delta <= mTypeToR m)%R ->
  (bound1 <= Q2R err1)%R ->
  toInterval (afQ2R af1) = ((- bound1)%R, bound1) ->
  (bound2 <= Q2R err2)%R ->
  toInterval (afQ2R af2) = ((- bound2)%R, bound2) ->
  (Q2R (fst iv1) <= v__R1 <= Q2R (snd iv1))%R ->
  (Q2R (fst iv2) <= v__R2 <= Q2R (snd iv2))%R ->
  (0 <= Q2R err2)%R ->
  ((snd iv2 + err2 <= 0 /\ Qeq_bool (snd iv2 + err2) 0 = false) \/
   (0 <= fst iv2 - err2 /\ Qeq_bool (fst iv2 - err2) 0 = false)) ->
  (v__R2 <> 0 /\ v__FP2 <> 0)%R ->
  exists noise_map',
    contained_map noise_map noise_map' /\
    (forall n, (noise + 8) <= n -> noise_map' n = None)%nat /\
    fresh (noise + 8) (plus_aff
         (plus_aff
            (subtract_aff
               (mult_aff (afQ2R af1) (afQ2R (fromIntv (invertIntv iv2) (noise + 1)))
                         (noise + 4))
               (mult_aff (afQ2R (fromIntv iv1 noise))
                         (mult_aff (afQ2R af2)
                                   (afQ2R (fromIntv (invertIntv (multIntv iv2
                                                                          (widenIntv iv2 err2)))
                                                    (noise + 2)))
                                   (noise + 3)) (noise + 5)))
            (mult_aff (afQ2R af1)
                      (mult_aff (afQ2R af2)
                                (afQ2R (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                 (noise + 2)))
                                (noise + 3)) (noise + 6)))
         (mkErrorPolyR
            (computeErrorR (Q2R (maxAbs (divideIntv (widenIntv iv1 err1)
                                                    (widenIntv iv2 err2)))) m)
            (noise + 7))) /\
    af_evals
      (plus_aff
         (plus_aff
            (subtract_aff
               (mult_aff (afQ2R af1) (afQ2R (fromIntv (invertIntv iv2) (noise + 1)))
                         (noise + 4))
               (mult_aff (afQ2R (fromIntv iv1 noise))
                         (mult_aff (afQ2R af2)
                                   (afQ2R (fromIntv (invertIntv (multIntv iv2
                                                                          (widenIntv iv2 err2)))
                                                    (noise + 2)))
                                   (noise + 3)) (noise + 5)))
            (mult_aff (afQ2R af1)
                      (mult_aff (afQ2R af2)
                                (afQ2R (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                 (noise + 2)))
                                (noise + 3)) (noise + 6)))
         (mkErrorPolyR
            (computeErrorR (Q2R (maxAbs (divideIntv (widenIntv iv1 err1)
                                                    (widenIntv iv2 err2)))) m)
            (noise + 7)))
      (v__R1 / v__R2 - perturb (v__FP1 / v__FP2) m delta) noise_map'.
Proof.
  intros Hevals1 Hevals2 Hfresh1 Hfresh2 Hnoise_map_valid Hdelta Hbounderr1 Hafiv1
         Hbounderr2 Hafiv2 Hiv1 Hiv2 Herr2 Hnonzero Hnonzerov.
  destruct (@af_evals_afQ2R_from_intv_updMap iv1 noise noise_map v__R1) as [q1 Hevalsiv1]; auto.
  pose (noise_map1 := updMap noise_map noise q1).
  assert (contained_map noise_map noise_map1)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 1 <= n')%nat -> noise_map1 n' = None)
    by (apply updMap_noise_incr; auto).
  assert (~ (fst iv2 == 0) /\ ~ (snd iv2 == 0)) as Hiv2_nozero.
  {
    destruct iv2 as [a b]; cbn in Hnonzero, Hiv2 |-*.
    split.
    - intros Haz.
      destruct Hnonzerov as [HnonzerovR HnonzerovFP].
      destruct Hnonzero as [Hnonzero|Hnonzero]; destruct Hnonzero as [Hle Heq].
      + apply Qeq_bool_neq in Heq.
        apply Qeq_eqR in Haz.
        rewrite Haz in Hiv2.
        apply Qle_Rle in Hle.
        rewrite Q2R_plus in Hle.
        lra.
      + apply Qeq_bool_neq in Heq.
        rewrite Haz in Hle.
        replace 0%R with (Q2R 0) in Herr2 by lra.
        apply Rle_Qle in Herr2.
        lra.
    - intros Hbz.
      destruct Hnonzerov as [HnonzerovR HnonzerovFP].
      destruct Hnonzero as [Hnonzero|Hnonzero]; destruct Hnonzero as [Hle Heq].
      + apply Qeq_bool_neq in Heq.
        rewrite Hbz in Hle.
        replace 0%R with (Q2R 0) in Herr2 by lra.
        apply Rle_Qle in Herr2.
        lra.
      + apply Qeq_bool_neq in Heq.
        apply Qeq_eqR in Hbz.
        rewrite Hbz in Hiv2.
        apply Qle_Rle in Hle.
        rewrite Q2R_minus in Hle.
        lra.
  }
  assert (~ (fst iv2 - err2 == 0) /\ ~ (snd iv2 + err2 == 0)) as Hiv2_nozero'.
  {
    destruct iv2 as [a b]; cbn in Hnonzero, Hiv2 |-*.
    assert (Q2R a <= Q2R b)%R as H' by lra.
    apply Rle_Qle in H'.
    replace 0%R with (Q2R 0) in Herr2 by lra.
    apply Rle_Qle in Herr2.
    assert (a - err2 <= b + err2) by lra.
    destruct Hnonzero as [Hz|Hz]; destruct Hz as [Hle Heq]; apply Qeq_bool_neq in Heq; lra.
  }
  destruct (@af_evals_afQ2R_from_intv_updMap (invertIntv iv2) (noise + 1)%nat noise_map1 (/ v__R2)) as [q2 Hevalsiv2]; auto.
  {
    cbn.
    destruct (@interval_inversion_valid (Q2RP iv2) v__R2).
    - destruct iv2 as [a b].
      cbn in Hnonzero |-*.
      destruct Hnonzero as [Hnonzero|Hnonzero]; destruct Hnonzero as [Hle Hneq].
      + apply Qeq_bool_neq in Hneq.
        apply Qle_Rle in Hle.
        left.
        rewrite Q2R_plus in Hle.
        destruct Hle; try lra.
        exfalso; apply Hneq.
        apply eqR_Qeq.
        rewrite Q2R_plus; assumption.
      + apply Qeq_bool_neq in Hneq.
        apply Qle_Rle in Hle.
        right.
        rewrite Q2R_minus in Hle.
        destruct Hle; try lra.
        exfalso; apply Hneq.
        apply eqR_Qeq.
        rewrite Q2R_minus; auto.
    - destruct iv2.
      cbn in *; auto.
    - destruct iv2 as [a b]; cbn in Hnonzero, H1, H2, Hiv2 |-*.
      destruct Hiv2_nozero.
      rewrite Q2R_inv; auto.
      rewrite Q2R_inv; auto.
  }
  pose (noise_map2 := updMap noise_map1 (noise + 1)%nat q2).
  assert (contained_map noise_map1 noise_map2)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 1 + 1 <= n')%nat -> noise_map2 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 1 + 1)%nat with (noise + 2)%nat in * by lia.
  pose (errDenominator := invertIntv (multIntv iv2 (widenIntv iv2 err2))).
  fold errDenominator in |-*.
  pose proof (@interval_multiplication_valid (Q2RP iv2) (Q2RP (widenIntv iv2 err2)) v__R2 v__FP2
                                             ltac:(destruct iv2; auto)
                                             ltac:(cbn; rewrite Q2R_plus, Q2R_minus; eapply contained'; eauto)).
  assert (~ fst (multIntv iv2 (widenIntv iv2 err2)) == 0).
  {
    clear - Hnonzero Hiv2 Hiv2_nozero Hiv2_nozero'.
    cbn.
    destruct iv2 as [a b]; cbn in *.
    assert (Q2R a <= Q2R b)%R as Hle by lra.
    apply Rle_Qle in Hle.
    apply Qmin4_nonzero; destruct Hiv2_nozero; destruct Hiv2_nozero';
      apply Qmult_Qeq_0_neq; lra.
  }
  assert (~ snd (multIntv iv2 (widenIntv iv2 err2)) == 0).
  {
    clear - Hnonzero Hiv2 Hiv2_nozero Hiv2_nozero'.
    cbn.
    destruct iv2 as [a b]; cbn in *.
    assert (Q2R a <= Q2R b)%R as Hle by lra.
    apply Rle_Qle in Hle.
    apply Qmax4_nonzero; destruct Hiv2_nozero; destruct Hiv2_nozero';
      apply Qmult_Qeq_0_neq; lra.
  }
  destruct (@af_evals_afQ2R_from_intv_updMap errDenominator (noise + 2)%nat noise_map2 (/ (v__R2 * v__FP2)))
    as [q3 Hevalsiv3]; auto.
  {
    unfold errDenominator.
    rewrite Q2R_Q2RP_fst, Q2R_Q2RP_snd.
    rewrite Q2RP_invertIntv; auto.
    rewrite Q2RP_multIntv.
    apply interval_inversion_valid; auto.
    unfold IVhi, IVlo.
    clear - Hiv2_nozero Hiv2_nozero' Hnonzero Hiv2 Herr2.
    right.
    destruct iv2 as [a b]; cbn in *.
    assert (Q2R a <= Q2R b)%R by lra.
    destruct Hnonzero as [H'|H']; destruct H' as [Hle Heq]; apply Qeq_bool_neq in Heq.
    - assert (b + err2 < 0) as Hlt by lra.
      apply Qlt_Rlt in Hlt; rewrite Q2R_plus in Hlt.
      replace (Q2R 0) with 0%R in Hlt by lra.
      apply Rmin4_ltzero; try rewrite Q2R_minus; try rewrite Q2R_plus; apply Rmult_neg_nonneg; lra.
    - assert (0 < a - err2) as Hlt by lra.
      apply Qlt_Rlt in Hlt; rewrite Q2R_minus in Hlt.
      replace (Q2R 0) with 0%R in Hlt by lra.
      apply Rmin4_ltzero; try rewrite Q2R_minus; try rewrite Q2R_plus; apply Rmult_nonneg; lra.
  }
  pose (noise_map3 := updMap noise_map2 (noise + 2) q3).
  assert (contained_map noise_map2 noise_map3)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 2 + 1 <= n')%nat -> noise_map3 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 2 + 1)%nat with (noise + 3)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R af2) (afQ2R (fromIntv errDenominator (noise +  2))) (v__R2 - v__FP2)
                            ( / (v__R2 * v__FP2)) noise_map3 (noise + 3)%nat)%R
    as [q4 HevalsErrMultiplier];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (eapply fresh_monotonic with (n := noise); eauto using mult_aff_const_fresh_compat; lia).
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  pose (errMultiplier := mult_aff (afQ2R af2) (afQ2R (fromIntv errDenominator (noise + 2)))
                                  (noise + 3)).
  fold errMultiplier in HevalsErrMultiplier |-*.
  pose (noise_map4 := updMap noise_map3 (noise + 3) q4).
  assert (contained_map noise_map3 noise_map4)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 3 + 1 <= n')%nat -> noise_map4 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 3 + 1)%nat with (noise + 4)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R af1) (afQ2R (fromIntv (invertIntv iv2) (noise + 1)))
           (v__R1 - v__FP1) (/ v__R2) noise_map4 (noise + 4)%nat)%R as [q5 Hevalsmult1];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (eapply fresh_monotonic with (n := noise); eauto; lia).
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  pose (noise_map5 := updMap noise_map4 (noise + 4) q5).
  assert (contained_map noise_map4 noise_map5)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 4 + 1 <= n')%nat -> noise_map5 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 4 + 1)%nat with (noise + 5)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R (fromIntv iv1 noise)) errMultiplier
           v__R1 ((v__R2 - v__FP2) * / (v__R2 * v__FP2)) noise_map5 (noise + 5)%nat)%R as [q6 Hevalsmult2];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  1: (apply mult_aff_fresh_compat; try (rewrite <- afQ2R_fresh; apply fresh_from_intv);
      try apply fresh_monotonic with (n := noise); auto; lia).
  pose (noise_map6 := updMap noise_map5 (noise + 5) q6).
  assert (contained_map noise_map5 noise_map6)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 5 + 1 <= n')%nat -> noise_map6 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 5 + 1)%nat with (noise + 6)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R af1) errMultiplier (v__R1 - v__FP1) ((v__R2 - v__FP2) * / (v__R2 * v__FP2))
                            noise_map6 (noise + 6)%nat)%R as [q7 Hevalsmult3];
    eauto 7 using fresh_monotonic, af_evals_map_extension.
  1: (eapply fresh_monotonic with (n := noise); eauto; lia).
  1: (apply mult_aff_fresh_compat; try (rewrite <- afQ2R_fresh; apply fresh_from_intv);
      try apply fresh_monotonic with (n := noise); auto; lia).
  pose (noise_map7 := updMap noise_map6 (noise + 6) q7).
  assert (contained_map noise_map6 noise_map7)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 6 + 1 <= n')%nat -> noise_map7 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 6 + 1)%nat with (noise + 7)%nat in * by lia.
  apply af_evals_map_extension with (map2 := noise_map6) in Hevalsmult1; auto.
  pose proof (subtract_aff_sound _ _ _ _ _ Hevalsmult1 Hevalsmult2) as Hevalssubtract.
  apply af_evals_map_extension with (map2 := noise_map7) in Hevalssubtract; auto.
  pose proof (plus_aff_sound _ _ _ _ _ Hevalssubtract Hevalsmult3) as Hevalsplus1.
  replace (noise + 8)%nat with (noise + 7 + 1)%nat by lia.
  eapply plus_error_aff_af_evals with (noise_map' := noise_map7) (noise' := (noise + 7)%nat); eauto.
  - field_rewrite (v__R1 / v__R2 - (v__FP1 / v__FP2) =
                   ((v__R1 - v__FP1) / v__R2 - v__R1 * ((v__R2 - v__FP2) / (v__R2 * v__FP2))) +
                   (v__R1 - v__FP1) * ((v__R2 - v__FP2) / (v__R2 * v__FP2)))%R; auto.
  - apply plus_aff_fresh_compat.
    + apply plus_aff_fresh_compat.
      * apply mult_aff_fresh_compat;
          [apply fresh_monotonic with (n := noise); eauto; lia|idtac|lia].
        rewrite <- afQ2R_fresh.
        apply fresh_from_intv; lia.
      * apply mult_aff_const_fresh_compat.
        apply mult_aff_fresh_compat;
          [rewrite <- afQ2R_fresh; apply fresh_from_intv; lia|idtac|lia].
        apply mult_aff_fresh_compat;
          [apply fresh_monotonic with (n := noise); eauto|
           rewrite <- afQ2R_fresh; apply fresh_from_intv|
           idtac]; lia.
    + apply mult_aff_fresh_compat;
        [apply fresh_monotonic with (n := noise); eauto; lia|idtac|lia].
      apply mult_aff_fresh_compat;
        [apply fresh_monotonic with (n := noise); eauto|
         rewrite <- afQ2R_fresh; apply fresh_from_intv|
         idtac]; lia.
  - eauto 7 using contained_map_trans.
  - destruct Hiv2_nozero'.
    rewrite Q2RP_divideIntv; auto.
    apply interval_division_valid;
      destruct iv1 as [a b], iv2 as [c d]; cbn in *;
        try rewrite Q2R_minus, Q2R_plus; try eapply contained'; eauto.
    destruct Hnonzero as [H'|H']; destruct H' as [Hle Heq]; apply Qeq_bool_neq in Heq;
      clear - Hle Heq.
    + apply Qle_Rle in Hle.
      left.
      replace 0%R with (Q2R 0) in * by lra.
      rewrite Q2R_plus in Hle.
      destruct Hle; auto.
      exfalso; apply Heq.
      apply eqR_Qeq.
      now rewrite Q2R_plus.
    + apply Qle_Rle in Hle.
      right.
      replace 0%R with (Q2R 0) in * by lra.
      rewrite Q2R_minus in Hle.
      destruct Hle; auto.
      exfalso; apply Heq.
      apply eqR_Qeq.
      now rewrite Q2R_minus.
Qed.

Lemma fma_error_af_evals
      af1 af2 af3 v__R1 v__R2 v__R3 v__FP1 v__FP2 v__FP3 iv1 iv2 iv3 err1 err2 err3 bound1 bound2 bound3
      m delta noise noise_map:
  af_evals (afQ2R af1) (v__R1 - v__FP1) noise_map ->
  af_evals (afQ2R af2) (v__R2 - v__FP2) noise_map ->
  af_evals (afQ2R af3) (v__R3 - v__FP3) noise_map ->
  fresh noise (afQ2R af1) ->
  fresh noise (afQ2R af2) ->
  fresh noise (afQ2R af3) ->
  (forall n' : nat, (noise <= n')%nat -> noise_map n' = None) ->
  (Rabs delta <= mTypeToR m)%R ->
  (bound1 <= Q2R err1)%R ->
  toInterval (afQ2R af1) = ((- bound1)%R, bound1) ->
  (bound2 <= Q2R err2)%R ->
  toInterval (afQ2R af2) = ((- bound2)%R, bound2) ->
  (bound3 <= Q2R err3)%R ->
  toInterval (afQ2R af3) = ((- bound3)%R, bound3) ->
  (Q2R (fst iv1) <= v__R1 <= Q2R (snd iv1))%R ->
  (Q2R (fst iv2) <= v__R2 <= Q2R (snd iv2))%R ->
  (Q2R (fst iv3) <= v__R3 <= Q2R (snd iv3))%R ->
  exists noise_map',
    contained_map noise_map noise_map' /\
    (forall n, (noise + 6) <= n -> noise_map' n = None)%nat /\
    fresh (noise + 6) (plus_aff
         (plus_aff (subtract_aff
                      (plus_aff
                         (mult_aff (afQ2R (fromIntv iv1 noise)) (afQ2R af2) (noise + 2))
                         (mult_aff (afQ2R (fromIntv iv2 (noise + 1))) (afQ2R af1) (noise + 3)))
                      (mult_aff (afQ2R af1) (afQ2R af2) (noise + 4)))
                   (afQ2R af3))
         (mkErrorPolyR
            (computeErrorR (Q2R (maxAbs
                                   (addIntv (multIntv (widenIntv iv1 err1)
                                                      (widenIntv iv2 err2))
                                            (widenIntv iv3 err3)))) m)
            (noise + 5))) /\
    af_evals
      (plus_aff
         (plus_aff (subtract_aff
                      (plus_aff
                         (mult_aff (afQ2R (fromIntv iv1 noise)) (afQ2R af2) (noise + 2))
                         (mult_aff (afQ2R (fromIntv iv2 (noise + 1))) (afQ2R af1) (noise + 3)))
                      (mult_aff (afQ2R af1) (afQ2R af2) (noise + 4)))
                   (afQ2R af3))
         (mkErrorPolyR
            (computeErrorR (Q2R (maxAbs
                                   (addIntv (multIntv (widenIntv iv1 err1)
                                                      (widenIntv iv2 err2))
                                            (widenIntv iv3 err3)))) m)
            (noise + 5)))
      (v__R1 * v__R2 + v__R3 - perturb (v__FP1 * v__FP2 + v__FP3) m delta) noise_map'.
Proof.
  intros Hevals1 Hevals2 Hevals3 Hfresh1 Hfresh2 Hfresh3; intros.
  destruct (@af_evals_afQ2R_from_intv_updMap iv1 noise noise_map v__R1) as [q1 Hevalsiv1]; auto.
  pose (noise_map1 := updMap noise_map noise q1).
  assert (contained_map noise_map noise_map1)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 1 <= n')%nat -> noise_map1 n' = None)
    by (apply updMap_noise_incr; auto).
  destruct (@af_evals_afQ2R_from_intv_updMap iv2 (noise + 1)%nat noise_map1 v__R2) as [q2 Hevalsiv2]; auto.
  pose (noise_map2 := updMap noise_map1 (noise + 1)%nat q2).
  assert (contained_map noise_map1 noise_map2)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 1 + 1 <= n')%nat -> noise_map2 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 1 + 1)%nat with (noise + 2)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R (fromIntv iv1 noise)) (afQ2R af2) v__R1
                            (v__R2 - v__FP2) noise_map2 (noise + 2)%nat)%R as [q3 Hevalsmult1];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  1: (eapply fresh_monotonic with (n := noise); eauto; lia).
  pose (noise_map3 := updMap noise_map2 (noise + 2) q3).
  assert (contained_map noise_map2 noise_map3)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 2 + 1 <= n')%nat -> noise_map3 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 2 + 1)%nat with (noise + 3)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R (fromIntv iv2 (noise + 1))) (afQ2R af1) v__R2
                            (v__R1 - v__FP1) noise_map3 (noise + 3)%nat)%R as [q4 Hevalsmult2];
    eauto using fresh_monotonic, af_evals_map_extension.
  1: (rewrite <- afQ2R_fresh; apply fresh_from_intv; lia).
  1: (eapply fresh_monotonic with (n := noise); eauto; lia).
  pose (noise_map4 := updMap noise_map3 (noise + 3) q4).
  assert (contained_map noise_map3 noise_map4)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 3 + 1 <= n')%nat -> noise_map4 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 3 + 1)%nat with (noise + 4)%nat in * by lia.
  destruct (@mult_aff_sound (afQ2R af1) (afQ2R af2) (v__R1 - v__FP1) (v__R2 - v__FP2)
                            noise_map4 (noise + 4)%nat)%R as [q5 Hevalsmult3];
    eauto using fresh_monotonic, af_evals_map_extension.
  1-2: (eapply fresh_monotonic with (n := noise); eauto; lia).
  apply af_evals_map_extension with (map2 := noise_map4) in Hevalsmult1; auto.
  pose proof (plus_aff_sound _ _ _ _ _ Hevalsmult1 Hevalsmult2) as Hevalsplus1.
  pose (noise_map5 := updMap noise_map4 (noise + 4) q5).
  assert (contained_map noise_map4 noise_map5)
    by (apply contained_map_extension; auto).
  assert (forall n', (noise + 4 + 1 <= n')%nat -> noise_map5 n' = None)
    by (apply updMap_noise_incr; auto).
  replace (noise + 4 + 1)%nat with (noise + 5)%nat in * by lia.
  apply af_evals_map_extension with (map2 := noise_map5) in Hevalsplus1; auto.
  pose proof (subtract_aff_sound _ _ _ _ _ Hevalsplus1 Hevalsmult3) as Hevalsplus2.
  apply af_evals_map_extension with (map2 := noise_map5) in Hevals3;
    eauto using contained_map_trans.
  pose proof (plus_aff_sound _ _ _ _ _ Hevalsplus2 Hevals3) as Hevalsplus3.
  replace (noise + 6)%nat with (noise + 5 + 1)%nat by lia.
  eapply plus_error_aff_af_evals with (noise_map' := noise_map5) (noise' := (noise + 5)%nat); eauto.
  - field_rewrite ((v__R1 * v__R2 + v__R3) - (v__FP1 * v__FP2 + v__FP3) =
                   (((v__R1 * (v__R2 - v__FP2)) + (v__R2 * (v__R1 - v__FP1))
                    - ((v__R1 - v__FP1) * (v__R2 - v__FP2))) + (v__R3 - v__FP3)))%R; auto.
  - apply plus_aff_fresh_compat;
      [|apply fresh_monotonic with (n := noise); eauto; lia].
    apply plus_aff_fresh_compat.
    + apply plus_aff_fresh_compat;
        apply mult_aff_fresh_compat; try lia.
      * rewrite <- afQ2R_fresh; apply fresh_from_intv; lia.
      * apply fresh_monotonic with (n := noise); eauto; lia.
      * rewrite <- afQ2R_fresh; apply fresh_from_intv; lia.
      * apply fresh_monotonic with (n := noise); eauto; lia.
    + apply mult_aff_const_fresh_compat.
      apply mult_aff_fresh_compat; try lia;
        [apply fresh_monotonic with (n := noise)|
         apply fresh_monotonic with (n := noise)]; eauto; lia.
  - eauto using contained_map_trans.
  - rewrite Q2RP_addIntv; rewrite Q2RP_multIntv.
    apply interval_addition_valid; try apply interval_multiplication_valid;
        destruct iv1, iv2, iv3; cbn in *;
          try rewrite Q2R_minus, Q2R_plus; eapply contained'; eauto.
Qed.

Lemma afQ2R_mult_aff_const a c:
  afQ2R (AffineArithQ.mult_aff_const a c) = mult_aff_const (afQ2R a) (Q2R c).
Proof.
  unfold mult_aff_const, AffineArithQ.mult_aff_const.
  rewrite afQ2R_mult_aff.
  rewrite afQ2R_get_max_index.
  trivial.
Qed.

Lemma flover_map_el_eq_extension V (map: FloverMap.t (affine_form V)) e e' v:
  ~ FloverMap.In e map ->
  FloverMap.In e (FloverMap.add e' v map) ->
  Q_orderedExps.exprCompare e' e = Eq /\
  toRExp e = toRExp e'.
Proof.
  intros Hnin Hin.
  rewrite FloverMapFacts.P.F.add_in_iff in Hin.
  destruct Hin as [Heq|Hin']; intuition.
  symmetry; now apply expr_compare_eq_eval_compat.
Qed.

Lemma flover_map_in_extension e (expr_map1: FloverMap.t (affine_form Q)) expr_map2:
  contained_flover_map expr_map1 expr_map2 ->
  FloverMap.In e expr_map1 ->
  FloverMap.In e expr_map2.
Proof.
  intros Hcontained Hin.
  unfold contained_flover_map in Hcontained.
  assert (exists af, FloverMap.find e expr_map1 = Some af) as [af Hfind].
  {
    rewrite FloverMapFacts.P.F.in_find_iff in Hin.
    destruct (FloverMap.find e expr_map1); eauto.
    congruence.
  }
  apply Hcontained in Hfind.
  assert (FloverMap.find e expr_map2 <> None) as H' by congruence.
  now rewrite <- FloverMapFacts.P.F.in_find_iff in H'.
Qed.

Lemma flover_map_in_add e a (expr_map: FloverMap.t (affine_form Q)):
  FloverMap.In e (FloverMap.add e a expr_map).
Proof.
  rewrite FloverMapFacts.P.F.add_in_iff.
  left.
  apply Q_orderedExps.exprCompare_refl.
Qed.

Definition flover_map_in_dec (V: Type) e exprmap := @FloverMapFacts.P.F.In_dec V exprmap e.
Definition q_expr_eq_dec e e' := FloverMapFacts.O.MO.eq_dec e e'.

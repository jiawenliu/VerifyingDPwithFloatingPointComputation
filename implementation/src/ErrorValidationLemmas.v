From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Flover
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis ErrorBounds
     IntervalValidation RealRangeValidator TypeValidator ErrorValidation.

(* Hide mTypeToQ from simplification since it will blow up the goal buffer *)
Arguments mTypeToQ _ :simpl nomatch.

(**
    Since errors are intervals with 0 as center, we encode them as single values.
    This lemma enables us to deduce from each run of the validator the invariant
    that when it succeeds, the errors must be positive.
**)
Lemma err_always_positive e tmap (A:analysisResult) dVars iv err:
  validErrorbound e tmap A dVars = true ->
    FloverMap.find e A = Some (iv,err) ->
    (0 <= Q2R err)%R.
Proof.
  destruct e; cbn; intros;
    Flover_compute; canonize_hyps;
      auto.
Qed.

Section soundnessProofs.

  Definition eval_Real E1 Gamma (e:expr Q) nR :=
    eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) nR REAL.

  Arguments eval_Real _ _ _ _/.

  Definition eval_Fin E2 Gamma DeltaMap (e:expr Q) nF m :=
    eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) nF m.

  Arguments eval_Fin _ _ _ _ _/.

Lemma validErrorboundCorrectVariable_eval E1 E2 A (v:nat) e nR nlo nhi fVars
      dVars Gamma DeltaMap exprTypes:
  eval_Real E1 Gamma (Var Q v) nR ->
    validTypes (Var Q v) Gamma ->
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    validRanges (Var Q v) A E1 (toRTMap (toRExpMap Gamma)) ->
    validErrorbound (Var Q v) exprTypes A dVars = true ->
    NatSet.Subset (NatSet.diff (freeVars (Var Q v)) dVars) fVars ->
    FloverMap.find (Var Q v) A = Some ((nlo, nhi), e) ->
    exists nF m,
    eval_Fin E2 Gamma DeltaMap (Var Q v) nF m.
Proof.
  intros eval_real typing_ok approxCEnv bounds_valid error_valid v_sound A_var.
  apply validRanges_single in bounds_valid.
  destruct_smart [find_v [eval_real2 bounds_valid]] bounds_valid.
  pose proof (meps_0_deterministic _ eval_real eval_real2); subst.
  cbn in *.
  inversion eval_real; subst.
  Flover_compute; type_conv.
  destruct (approxEnv_gives_value approxCEnv H1); try eauto.
  - set_tac.
    case_eq (NatSet.mem v dVars); intros v_case; set_tac.
    left; apply v_sound.
    apply NatSetProps.FM.diff_3; set_tac.
  - destruct typing_ok as [? [tdef ?]].
    exists x, x0. eapply Var_load; eauto.
    eapply toRExpMap_some; eauto; simpl; auto.
Qed.

Lemma validErrorboundCorrectVariable:
  forall E1 E2 A (v:nat) e nR nF mF nlo nhi fVars dVars Gamma DeltaMap,
    eval_Real E1 Gamma (Var Q v) nR ->
    eval_Fin E2 Gamma DeltaMap (Var Q v) nF mF ->
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    validTypes (Var Q v) (Gamma) ->
    validRanges (Var Q v) A E1 (toRTMap (toRExpMap Gamma)) ->
    validErrorbound (Var Q v) Gamma A dVars = true ->
    NatSet.Subset (NatSet.diff (freeVars (Var Q v)) dVars) fVars ->
    FloverMap.find (Var Q v) A = Some ((nlo, nhi), e) ->
    (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros * eval_real eval_float approxCEnv typing_ok bounds_valid error_valid
                     v_sound A_var.
  apply validRanges_single in bounds_valid.
  destruct_smart [find_v [eval_real2 bounds_valid]] bounds_valid.
  pose proof (meps_0_deterministic _ eval_real eval_real2); subst.
  cbn in *; Flover_compute; type_conv.
  inversion eval_real;
    inversion eval_float;
    subst.
  rename H1 into E1_v.
  rename L into error_pos.
  rename R into error_valid.
  case_eq (v mem dVars); [intros v_dVar | intros v_fVar].
  - rewrite v_dVar in *; simpl in *.
    rewrite NatSet.mem_spec in v_dVar.
    eapply approxEnv_dVar_bounded; eauto.
  - rewrite v_fVar in *; simpl in *.
    apply not_in_not_mem in v_fVar.
    assert (v ∈ fVars) as v_in_fVars by set_tac.
    pose proof (approxEnv_fVar_bounded approxCEnv E1_v H6 v_in_fVars H5).
    eapply Rle_trans; eauto.
    canonize_hyps.
    repeat destr_factorize.
    rewrite computeErrorQ_computeErrorR in error_valid.
    eapply Rle_trans; eauto.
    eapply toRExpMap_some in Heqo; eauto; simpl in *.
    assert (m = mF) by congruence; subst.
    rewrite <- maxAbs_impl_RmaxAbs.
    apply computeErrorR_up.
    apply contained_leq_maxAbs.
    simpl in *; auto.
Qed.

Lemma validErrorboundCorrectConstant_eval E2 m n Gamma DeltaMap:
    (forall (e' : R) (m' : mType),
        exists d : R, DeltaMap e' m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    validTypes (Const m n) Gamma ->
    exists nF m',
      eval_Fin E2 Gamma DeltaMap (Const m n) nF m'.
Proof.
  intros deltas_matched typing_ok.
  simpl in typing_ok.
  destruct typing_ok as [? [type_def [? ?]]]; subst.
  specialize (deltas_matched ((Q2R n)) x) as (delta & delta_matched & delta_bound).
  repeat eexists.
  eapply Const_dist' with (delta := delta); eauto.
Qed.

Lemma validErrorboundCorrectConstant E1 E2 A m n nR nF e nlo nhi dVars Gamma DeltaMap:
    eval_Real E1 Gamma (Const m n) nR ->
    eval_Fin E2 Gamma DeltaMap (Const m n) nF m ->
    validTypes (Const m n) Gamma ->
    validErrorbound (Const m n) Gamma A dVars = true ->
    (Q2R nlo <= nR <= Q2R nhi)%R ->
    FloverMap.find (Const m n) A = Some ((nlo,nhi),e) ->
    (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros eval_real eval_float subexprr_ok error_valid intv_valid A_const.
  unfold eval_Real in *.
  cbn in *; Flover_compute; type_conv.
  eapply Rle_trans.
  eapply const_abs_err_bounded; eauto.
  rename R into error_valid.
  inversion eval_real; subst.
  canonize_hyps.
  eapply Rle_trans; eauto.
  rewrite computeErrorQ_computeErrorR.
  rewrite <- maxAbs_impl_RmaxAbs.
  apply computeErrorR_up.
  apply contained_leq_maxAbs.
  simpl in *; auto.
Qed.

Lemma validErrorboundCorrectAddition E1 E2 A
      (e1:expr Q) (e2:expr Q) (nR nR1 nR2 nF nF1 nF2 :R) (e err1 err2 :error)
      (alo ahi e1lo e1hi e2lo e2hi:Q) dVars m m1 m2 Gamma DeltaMap:
  eval_Real E1 Gamma e1 nR1 ->
  eval_Real E1 Gamma e2 nR2 ->
  eval_Real E1 Gamma (Binop Plus e1 e2) nR ->
  eval_Fin E2 Gamma DeltaMap e1 nF1 m1 ->
  eval_Fin E2 Gamma DeltaMap e2 nF2 m2 ->
  eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
            (updDefVars (Binop Plus (Var R 1) (Var R 2)) m
                        (updDefVars (Var Rdefinitions.R 2) m2
                                    (updDefVars (Var Rdefinitions.R 1) m1 (toRExpMap Gamma))))
            (fun x _ => if Req_dec_sum x (evalBinop Plus nF1 nF2)
                     then DeltaMap (evalBinop Plus nF1 nF2) m
                     else None)
            (toRExp (Binop Plus (Var Q 1) (Var Q 2))) nF m ->
  validErrorbound (Binop Plus e1 e2) Gamma A dVars = true ->
  (Q2R e1lo <= nR1 <= Q2R e1hi)%R ->
  (Q2R e2lo <= nR2 <= Q2R e2hi)%R ->
  FloverMap.find e1 A = Some ((e1lo,e1hi),err1) ->
  FloverMap.find e2 A = Some ((e2lo, e2hi),err2) ->
  FloverMap.find (Binop Plus e1 e2) A = Some ((alo,ahi),e)->
  FloverMap.find (Binop Plus e1 e2) Gamma = Some m ->
  (Rabs (nR1 - nF1) <= (Q2R err1))%R ->
  (Rabs (nR2 - nF2) <= (Q2R err2))%R ->
  (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros e1_real e2_real eval_real e1_float e2_float eval_float
         valid_error valid_intv1 valid_intv2 A_e1 A_e2 A_add
         Gamma_Plus err1_bounded err2_bounded.
  cbn in *; Flover_compute; type_conv.
  eapply Rle_trans.
  eapply
    (add_abs_err_bounded e1 e2);
    try eauto.
  repeat destr_factorize.
  rename R0 into valid_error.
  canonize_hyps.
  eapply Rle_trans; eauto.
  repeat rewrite Q2R_plus.
  repeat apply Rplus_le_compat_l.
  clear L R.
  assert (contained nR1 (Q2R e1lo, Q2R e1hi)) as contained_intv1 by auto.
  pose proof (distance_gives_iv (a:=nR1) _ (Q2R e1lo, Q2R e1hi) contained_intv1 err1_bounded)
       as contained_widen1.
  assert (contained nR2 (Q2R e2lo, Q2R e2hi)) as contained_intv2 by auto.
  pose proof (distance_gives_iv (a:=nR2) _ (Q2R e2lo, Q2R e2hi) contained_intv2 err2_bounded)
       as contained_widen2.
  pose proof (IntervalArith.interval_addition_valid _ _ contained_widen1 contained_widen2).
  subst.
  rewrite computeErrorQ_computeErrorR, <- maxAbs_impl_RmaxAbs_iv.
  apply computeErrorR_up.
  apply contained_leq_maxAbs.
  simpl in *; split.
  - rewrite Q2R_min4.
    repeat rewrite Q2R_plus;
      repeat rewrite Q2R_minus; lra.
  - rewrite Q2R_max4.
    repeat rewrite Q2R_plus;
      repeat rewrite Q2R_minus; lra.
Qed.

Lemma validErrorboundCorrectSubtraction E1 E2 A
      (e1:expr Q) (e2:expr Q) (nR nR1 nR2 nF nF1 nF2 :R) (e err1 err2 :error)
      (alo ahi e1lo e1hi e2lo e2hi:Q) dVars (m m1 m2:mType) Gamma DeltaMap:
  eval_Real E1 Gamma e1 nR1 ->
  eval_Real E1 Gamma e2 nR2 ->
  eval_Real E1 Gamma (Binop Sub e1 e2) nR ->
  eval_Fin E2 Gamma DeltaMap e1 nF1 m1->
  eval_Fin E2 Gamma DeltaMap e2 nF2 m2 ->
  eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
            (updDefVars (Binop Sub (Var R 1) (Var R 2)) m
                        (updDefVars (Var Rdefinitions.R 2) m2
                                    (updDefVars (Var Rdefinitions.R 1) m1 (toRExpMap Gamma))))
            (fun x _ => if Req_dec_sum x (evalBinop Sub nF1 nF2)
                     then DeltaMap (evalBinop Sub nF1 nF2) m
                     else None)
            (toRExp (Binop Sub (Var Q 1) (Var Q 2))) nF m ->
  validErrorbound (Binop Sub e1 e2) Gamma A dVars = true ->
  (Q2R e1lo <= nR1 <= Q2R e1hi)%R ->
  (Q2R e2lo <= nR2 <= Q2R e2hi)%R ->
  FloverMap.find e1 A = Some ((e1lo,e1hi),err1) ->
  FloverMap.find e2 A = Some ((e2lo, e2hi),err2) ->
  FloverMap.find (Binop Sub e1 e2) A = Some ((alo,ahi),e)->
  FloverMap.find (Binop Sub e1 e2) Gamma = Some m ->
  (Rabs (nR1 - nF1) <= (Q2R err1))%R ->
  (Rabs (nR2 - nF2) <= (Q2R err2))%R ->
  (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros e1_real e2_real eval_real e1_float e2_float eval_float
         valid_error valid_intv1 valid_intv2 A_e1 A_e2 A_sub Gamma_sub
         err1_bounded err2_bounded.
  cbn in *; Flover_compute; type_conv.
  eapply Rle_trans.
  eapply (subtract_abs_err_bounded e1 e2); try eauto.
  repeat destr_factorize.
  rename R0 into valid_error.
  canonize_hyps.
  repeat rewrite Q2R_plus in valid_error.
  repeat rewrite Q2R_mult in valid_error.
  repeat rewrite Q2R_plus in valid_error.
  eapply Rle_trans; eauto.
  repeat apply Rplus_le_compat_l.
  rewrite computeErrorQ_computeErrorR, <- maxAbs_impl_RmaxAbs_iv.
  assert (contained nR1 (Q2R e1lo, Q2R e1hi)) as contained_intv1 by auto.
  pose proof (distance_gives_iv (a:=nR1) _ _ contained_intv1 err1_bounded)
       as contained_widen1.
  assert (contained nR2 (Q2R e2lo, Q2R e2hi)) as contained_intv2 by auto.
  pose proof (distance_gives_iv (a:=nR2) _ _ contained_intv2 err2_bounded)
       as contained_widen2.
  pose proof (IntervalArith.interval_subtraction_valid _ _ contained_widen1 contained_widen2).
  apply computeErrorR_up.
  apply contained_leq_maxAbs.
  simpl in *; split.
  - rewrite Q2R_min4.
    repeat rewrite Q2R_plus;
      repeat rewrite Q2R_minus;
      repeat rewrite Q2R_opp;
      repeat rewrite Q2R_plus;
      repeat rewrite Q2R_minus; lra.
  - rewrite Q2R_max4.
    repeat rewrite Q2R_plus;
      repeat rewrite Q2R_minus;
      repeat rewrite Q2R_opp;
      repeat rewrite Q2R_plus;
      repeat rewrite Q2R_minus; lra.
Qed.

Lemma multiplicationErrorBounded e1lo e1hi e2lo e2hi nR1 nF1 nR2 nF2 err1 err2 :
  (Q2R e1lo <= nR1 <= Q2R e1hi)%R ->
  (Q2R e2lo <= nR2 <= Q2R e2hi)%R ->
  (Rabs (nR1 - nF1) <= Q2R err1)%R ->
  (Rabs (nR2 - nF2) <= Q2R err2)%R ->
  (0 <= Q2R err1)%R ->
  (0 <= Q2R err2)%R ->
  (Rabs (nR1 * nR2 - nF1 * nF2) <=
   RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2 + RmaxAbsFun (Q2R e2lo, Q2R e2hi) * Q2R err1 +
   Q2R err1 * Q2R err2)%R.
Proof.
  intros valid_e1 valid_e2 err1_bounded err2_bounded err1_pos err2_pos.
  unfold Rabs in err1_bounded.
  unfold Rabs in err2_bounded.
  (* Before doing case distinction, prove bounds that will be used many times: *)
  assert (nR1 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi))%R
    as upperBound_nR1
      by (apply contained_leq_maxAbs_val; auto).
  assert (nR2 <= RmaxAbsFun (Q2R e2lo, Q2R e2hi))%R
    as upperBound_nR2
      by (apply contained_leq_maxAbs_val; auto).
  assert (-nR1 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi))%R
    as upperBound_Ropp_nR1
      by (apply contained_leq_maxAbs_neg_val; auto).
  assert (- nR2 <= RmaxAbsFun (Q2R e2lo, Q2R e2hi))%R
    as upperBound_Ropp_nR2
      by (apply contained_leq_maxAbs_neg_val; auto).
  assert (nR1 * Q2R err2 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2)%R
    as bound_nR1 by (apply Rmult_le_compat_r; auto).
  assert (- nR1 * Q2R err2 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2)%R
    as bound_neg_nR1 by (apply Rmult_le_compat_r; auto).
  assert (nR2 * Q2R err1 <= RmaxAbsFun (Q2R e2lo, Q2R e2hi) * Q2R err1)%R
    as bound_nR2 by (apply Rmult_le_compat_r; auto).
  assert (- nR2 * Q2R err1 <= RmaxAbsFun (Q2R e2lo, Q2R e2hi) * Q2R err1)%R
    as bound_neg_nR2 by (apply Rmult_le_compat_r; auto).
  assert (- (Q2R err1 * Q2R err2) <= Q2R err1 * Q2R err2)%R as err_neg_bound
      by  (rewrite Ropp_mult_distr_l; apply Rmult_le_compat_r; lra).
  assert (0 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2)%R
    as zero_up_nR1 by lra.
  assert (RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2 + RmaxAbsFun (Q2R e2lo, Q2R e2hi) * Q2R err1)%R
    as nR1_to_sum by lra.
  assert (RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2 + RmaxAbsFun (Q2R e2lo, Q2R e2hi) * Q2R err1 <=  RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2 + RmaxAbsFun (Q2R e2lo, Q2R e2hi) * Q2R err1 + Q2R err1 * Q2R err2)%R
    as sum_to_errsum by lra.
  (* Large case distinction for
         a) different cases of the value of Rabs (...) and
         b) wether arguments of multiplication in (nf1 * nF2) are < or >= 0 *)
  destruct Rcase_abs in err1_bounded; destruct Rcase_abs in err2_bounded.
  + rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded.
    rewrite Ropp_plus_distr in err1_bounded, err2_bounded.
    rewrite Ropp_involutive in err1_bounded, err2_bounded.
    assert (nF1 <= Q2R err1 + nR1)%R by lra.
    assert (nF2 <= Q2R err2 + nR2)%R by lra.
    unfold Rabs.
    destruct Rcase_abs.
    * rewrite Rsub_eq_Ropp_Rplus. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      destruct (Rle_lt_dec 0 nF1).
      { (* Upper Bound ... *)
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l. hnf. left; auto.
          assert (nR1 <= nF1)%R by lra.
          apply H1.
          lra.
      }
      {
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_neg_l.
        hnf. left; auto.
        assert (nR2 < nF2)%R by lra.
        apply Rlt_le in H1; apply H1.
        destruct (Rle_lt_dec 0 nR2).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          assert (nR1 < nF1)%R by lra.
          apply Rlt_le in H1; apply H1.
          lra.
      }
    * rewrite Rsub_eq_Ropp_Rplus.
      destruct (Rle_lt_dec 0 nF1).
      {
        rewrite Ropp_mult_distr_r.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        assert (- nF2 <= - nR2)%R by lra.
        apply H1.
        destruct (Rle_lt_dec 0 (- nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          assert (nR1 < nF1)%R by lra.
          apply Rlt_le in H1; apply H1.
          lra.
      }
      {
        rewrite Ropp_mult_distr_l.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l.
        rewrite <- (Ropp_involutive 0).
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite Ropp_0.
        hnf. left; auto.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          assert (- nF1 <= -nR1)%R by lra.
          apply H1.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          apply Ropp_le_ge_contravar in H.
          apply Rge_le in H.
          apply H.
          lra.
      }
  + rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded.
    rewrite Ropp_plus_distr in err1_bounded.
    rewrite Ropp_involutive in err1_bounded.
    assert (nF1 <= Q2R err1 + nR1)%R by lra.
    assert (nF2 <= Q2R err2 + nR2)%R by lra.
    unfold Rabs.
    destruct Rcase_abs.
    * rewrite Rsub_eq_Ropp_Rplus. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      destruct (Rle_lt_dec 0 nF1).
      { (* Upper Bound ... *)
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l. hnf. left; auto.
          assert (nR1 <= nF1)%R by lra.
          apply H1.
          lra.
      }
      {
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_neg_l.
        hnf. left; auto.
        assert (- nF2 <= - (nR2 - Q2R err2))%R by lra.
        apply Ropp_le_ge_contravar in H1.
        repeat rewrite Ropp_involutive in H1.
        apply Rge_le in H1.
        apply H1.
        destruct (Rle_lt_dec 0 (nR2 - Q2R err2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          assert (nR1 < nF1)%R by lra.
          apply Rlt_le in H1; apply H1.
          lra.
      }
    * rewrite Rsub_eq_Ropp_Rplus.
      destruct (Rle_lt_dec 0 nF1).
      {
        rewrite Ropp_mult_distr_r.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        assert (- nF2 <= - nR2 + Q2R err2)%R by lra.
        apply H1.
        destruct (Rle_lt_dec 0 (- nR2 + Q2R err2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          assert (nR1 < nF1)%R by lra.
          apply Rlt_le in H1; apply H1.
          lra.
      }
      {
        rewrite Ropp_mult_distr_l.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l.
        rewrite <- (Ropp_involutive 0).
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite Ropp_0.
        hnf. left; auto.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          assert (- nF1 <= -nR1)%R by lra.
          apply H1.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          apply Ropp_le_ge_contravar in H.
          apply Rge_le in H.
          apply H.
          lra.
      }
  + rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded.
    rewrite Ropp_plus_distr in err2_bounded.
    rewrite Ropp_involutive in err2_bounded.
    assert (nF1 <= Q2R err1 + nR1)%R by lra.
    assert (nF2 <= Q2R err2 + nR2)%R by lra.
    unfold Rabs.
    destruct Rcase_abs.
    * rewrite Rsub_eq_Ropp_Rplus. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      destruct (Rle_lt_dec 0 nF1).
      { (* Upper Bound ... *)
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l. hnf. left; auto.
          assert (- nF1 <= - (nR1 - Q2R err1))%R by lra.
          apply Ropp_le_ge_contravar in H1.
          repeat rewrite Ropp_involutive in H1.
          apply Rge_le in H1.
          apply H1.
          lra.
      }
      {
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_neg_l.
        hnf. left; auto.
        assert (nR2 < nF2)%R by lra.
        apply Rlt_le in H1; apply H1.
        destruct (Rle_lt_dec 0 nR2).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          assert (- nF1 <= - (nR1 - Q2R err1))%R by lra.
          apply Ropp_le_ge_contravar in H1.
          repeat rewrite Ropp_involutive in H1.
          apply Rge_le in H1.
          apply H1.
          lra.
      }
    * rewrite Rsub_eq_Ropp_Rplus.
      destruct (Rle_lt_dec 0 nF1).
      {
        rewrite Ropp_mult_distr_r.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        assert (- nF2 <= - nR2)%R by lra.
        apply H1.
        destruct (Rle_lt_dec 0 (- nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          hnf. left; auto.
          assert (- nF1 <= - (nR1 - Q2R err1))%R by lra.
          apply Ropp_le_ge_contravar in H1.
          repeat rewrite Ropp_involutive in H1.
          apply Rge_le in H1.
          apply H1.
          lra.
      }
      {
        rewrite Ropp_mult_distr_l.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l.
        lra.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          assert (- nF1 <= - (nR1 - Q2R err1))%R by lra.
          apply H1.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l; try lra.
          apply Ropp_le_ge_contravar in H.
          apply Rge_le in H.
          apply H.
          lra.
      }
  (* All positive *)
  + assert (nF1 <= Q2R err1 + nR1)%R by lra.
    assert (nF2 <= Q2R err2 + nR2)%R by lra.
    unfold Rabs.
    destruct Rcase_abs.
    * rewrite Rsub_eq_Ropp_Rplus. rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      destruct (Rle_lt_dec 0 nF1).
      { (* Upper Bound ... *)
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l. hnf. left; auto.
          assert (nR1 - Q2R err1 <= nF1)%R by lra.
          apply H1.
          lra.
      }
      {
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_neg_l.
        hnf. left; auto.
        assert (nR2 - Q2R err2 <= nF2)%R by lra.
        apply H1.
        destruct (Rle_lt_dec 0 (nR2 - Q2R err2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          lra.
          assert (nR1 - Q2R err1 <= nF1)%R by lra.
          apply H1.
          lra.
      }
    * rewrite Rsub_eq_Ropp_Rplus.
      destruct (Rle_lt_dec 0 nF1).
      {
        rewrite Ropp_mult_distr_r.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l; auto.
        assert (- nF2 <= Q2R err2 - nR2)%R by lra.
        apply H1.
        destruct (Rle_lt_dec 0 (Q2R err2 - nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          apply H.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          lra.
          assert (nR1 - Q2R err1 <= nF1)%R by lra.
          apply H1.
          lra.
      }
      {
        rewrite Ropp_mult_distr_l.
        eapply Rle_trans.
        eapply Rplus_le_compat_l.
        eapply Rmult_le_compat_l.
        rewrite <- (Ropp_involutive 0).
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite Ropp_0.
        lra.
        apply H0.
        destruct (Rle_lt_dec 0 (Q2R err2 + nR2)).
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          eapply Rmult_le_compat_r; auto.
          assert (- nF1 <= Q2R err1 - nR1)%R by lra.
          apply H1.
          lra.
        - eapply Rle_trans.
          eapply Rplus_le_compat_l.
          rewrite Rmult_comm.
          eapply Rmult_le_compat_neg_l.
          lra.
          apply Ropp_le_ge_contravar in H.
          apply Rge_le in H.
          apply H.
          lra.
      }
Qed.

Lemma validErrorboundCorrectMult E1 E2 A
      (e1:expr Q) (e2:expr Q) (nR nR1 nR2 nF nF1 nF2 :R) (e err1 err2 :error)
      (alo ahi e1lo e1hi e2lo e2hi:Q) dVars (m m1 m2:mType) Gamma DeltaMap:
  eval_Real E1 Gamma e1 nR1 ->
  eval_Real E1 Gamma e2 nR2 ->
  eval_Real E1 Gamma (Binop Mult e1 e2) nR ->
  eval_Fin E2 Gamma DeltaMap e1 nF1 m1->
  eval_Fin E2 Gamma DeltaMap e2 nF2 m2 ->
  eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
            (updDefVars (Binop Mult (Var R 1) (Var R 2)) m
                        (updDefVars (Var Rdefinitions.R 2) m2
                                    (updDefVars (Var Rdefinitions.R 1) m1 (toRExpMap Gamma))))
            (fun x _ => if Req_dec_sum x (evalBinop Mult nF1 nF2)
                     then DeltaMap (evalBinop Mult nF1 nF2) m
                     else None)
            (toRExp (Binop Mult (Var Q 1) (Var Q 2))) nF m ->
  validErrorbound (Binop Mult e1 e2) Gamma A dVars = true ->
  (Q2R e1lo <= nR1 <= Q2R e1hi)%R ->
  (Q2R e2lo <= nR2 <= Q2R e2hi)%R ->
  FloverMap.find e1 A = Some ((e1lo,e1hi),err1) ->
  FloverMap.find e2 A = Some ((e2lo, e2hi),err2) ->
  FloverMap.find (Binop Mult e1 e2) A = Some ((alo,ahi),e)->
  FloverMap.find (Binop Mult e1 e2) Gamma = Some m ->
  (Rabs (nR1 - nF1) <= (Q2R err1))%R ->
  (Rabs (nR2 - nF2) <= (Q2R err2))%R ->
  (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros e1_real e2_real eval_real e1_float e2_float eval_float
         valid_error valid_intv1 valid_intv2 A_e1 A_e2 A_sub Gamma_sub
         err1_bounded err2_bounded.
  cbn in *; Flover_compute; type_conv.
  canonize_hyps.
  eapply Rle_trans.
  eapply (mult_abs_err_bounded e1 e2); eauto.
  rename R0 into valid_error.
  assert (0 <= Q2R err1)%R as err1_pos.
  { pose proof (err_always_positive e1 Gamma A dVars);
      eauto. }
  assert (0 <= Q2R err2)%R as err2_pos.
  { pose proof (err_always_positive e2 Gamma A dVars); eauto. }
  repeat rewrite Q2R_plus in valid_error.
  repeat rewrite Q2R_mult in valid_error.
  repeat rewrite <- maxAbs_impl_RmaxAbs in valid_error.
  eapply Rle_trans; eauto.
  apply Rplus_le_compat.
  - eauto using multiplicationErrorBounded.
  - rewrite computeErrorQ_computeErrorR, <- maxAbs_impl_RmaxAbs_iv.
    apply computeErrorR_up.
    apply contained_leq_maxAbs.
    assert (contained nR1 (Q2R e1lo, Q2R e1hi)) as contained_intv1 by auto.
    pose proof (distance_gives_iv (a:=nR1) _ _ contained_intv1 err1_bounded)
      as cont_err1.
    assert (contained nR2 (Q2R e2lo, Q2R e2hi)) as contained_intv2 by auto.
    pose proof (distance_gives_iv (a:=nR2) _ _ contained_intv2 err2_bounded)
      as cont_err2.
    pose proof (IntervalArith.interval_multiplication_valid _ _ cont_err1 cont_err2)
      as valid_mult.
    simpl in *; split.
    + rewrite Q2R_min4.
      repeat rewrite Q2R_mult;
        repeat rewrite Q2R_minus;
        repeat rewrite Q2R_plus. lra.
    + rewrite Q2R_max4.
      repeat rewrite Q2R_mult;
        repeat rewrite Q2R_minus;
        repeat rewrite Q2R_plus; lra.
Qed.

Lemma validErrorboundCorrectDiv E1 E2 A
      (e1:expr Q) (e2:expr Q) (nR nR1 nR2 nF nF1 nF2 :R) (e err1 err2 :error)
      (alo ahi e1lo e1hi e2lo e2hi:Q) dVars (m m1 m2:mType) Gamma DeltaMap:
  eval_Real E1 Gamma e1 nR1 ->
  eval_Real E1 Gamma e2 nR2 ->
  eval_Real E1 Gamma (Binop Div e1 e2) nR ->
  eval_Fin E2 Gamma DeltaMap e1 nF1 m1->
  eval_Fin E2 Gamma DeltaMap e2 nF2 m2 ->
  eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
            (updDefVars (Binop Div (Var R 1) (Var R 2)) m
                        (updDefVars (Var Rdefinitions.R 2) m2
                                    (updDefVars (Var Rdefinitions.R 1) m1 (toRExpMap Gamma))))
            (fun x _ => if Req_dec_sum x (evalBinop Div nF1 nF2)
                     then DeltaMap (evalBinop Div nF1 nF2) m
                     else None)
            (toRExp (Binop Div (Var Q 1) (Var Q 2))) nF m ->
  validErrorbound (Binop Div e1 e2) Gamma A dVars = true ->
  (Q2R e1lo <= nR1 <= Q2R e1hi)%R ->
  (Q2R e2lo <= nR2 <= Q2R e2hi)%R ->
  (Qleb e2hi 0 && negb (Qeq_bool e2hi 0) || Qleb 0 e2lo && negb (Qeq_bool e2lo 0) = true) ->
  FloverMap.find e1 A = Some ((e1lo,e1hi),err1) ->
  FloverMap.find e2 A = Some ((e2lo, e2hi),err2) ->
  FloverMap.find (Binop Div e1 e2) A = Some ((alo,ahi),e)->
  FloverMap.find (Binop Div e1 e2) Gamma = Some m ->
  (Rabs (nR1 - nF1) <= (Q2R err1))%R ->
  (Rabs (nR2 - nF2) <= (Q2R err2))%R ->
  (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros e1_real e2_real eval_real e1_float e2_float eval_float valid_error
         valid_intv1 valid_intv2 no_div_zero_real A_e1 A_e2 A_sub Gamma_sub
         err1_bounded err2_bounded.
  cbn in *; Flover_compute; type_conv.
  canonize_hyps.
  eapply Rle_trans.
  eapply (div_abs_err_bounded e1 e2); eauto.
  rename L0 into no_div_zero_float.
  assert (contained nR1 (Q2R e1lo, Q2R e1hi)) as contained_intv1 by auto.
  pose proof (distance_gives_iv (a:=nR1) _ _ contained_intv1 err1_bounded).
  assert (contained nR2 (Q2R e2lo, Q2R e2hi)) as contained_intv2 by auto.
  pose proof (distance_gives_iv (a:=nR2) _ _ contained_intv2 err2_bounded).
  assert (0 <= Q2R err1)%R as err1_pos.
  { pose proof (err_always_positive e1 Gamma A); eauto. }
  assert (0 <= Q2R err2)%R as err2_pos.
  { pose proof (err_always_positive e2 Gamma A); eauto. }
  canonize_hyps.
  rename R1 into valid_error.
  repeat rewrite Q2R_plus in valid_error.
  repeat rewrite Q2R_mult in valid_error.
  rewrite Q2R_div in valid_error.
  - rewrite Q2R_mult in valid_error.
    repeat rewrite <- maxAbs_impl_RmaxAbs in valid_error.
    rewrite <- maxAbs_impl_RmaxAbs_iv in valid_error.
    repeat rewrite <- minAbs_impl_RminAbs_iv in valid_error.
    apply le_neq_bool_to_lt_prop in no_div_zero_float; apply le_neq_bool_to_lt_prop in no_div_zero_real.
    assert ((IVhi (Q2R e2lo,Q2R e2hi) < 0)%R \/ (0 < IVlo (Q2R e2lo,Q2R e2hi))%R) as no_div_zero_real_R
          by (simpl; rewrite <- Q2R0_is_0; simpl in no_div_zero_real;
              destruct no_div_zero_real as [ndiv | ndiv]; apply Qlt_Rlt in ndiv; auto).
    apply Q_case_div_to_R_case_div in no_div_zero_float; apply Q_case_div_to_R_case_div in no_div_zero_real.
    assert (Q2R e2lo = 0 -> False)%R by (apply (lt_or_gt_neq_zero_lo _ (Q2R e2hi)); try auto; lra).
    assert (Q2R e2hi = 0 -> False)%R by (apply (lt_or_gt_neq_zero_hi (Q2R e2lo)); try auto; lra).
    eapply Rle_trans; eauto.
    apply Rplus_le_compat.
    (* Error Propagation proof *)
    + clear A_e1 A_e2 valid_error eval_float eval_real e1_float
            e1_real e2_float e2_real A_sub E1 E2 alo ahi nR nF e L.
      unfold widenInterval in *.
      simpl in *.
      rewrite Q2R_plus, Q2R_minus in no_div_zero_float.
      assert (Q2R e2lo - Q2R err2 = 0 -> False)%R by (apply (lt_or_gt_neq_zero_lo _ (Q2R e2hi + Q2R err2)); try auto; lra).
      assert (Q2R e2hi + Q2R err2 = 0 -> False)%R by (apply (lt_or_gt_neq_zero_hi (Q2R e2lo - Q2R err2)); try auto; lra).
      pose proof (interval_inversion_valid (Q2R e2lo,Q2R e2hi) no_div_zero_real_R valid_intv2) as valid_bounds_inv_e2.
      clear no_div_zero_real_R.
      (* Before doing case distinction, prove bounds that will be used many times: *)
      assert (nR1 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi))%R
        as upperBound_nR1
          by (apply contained_leq_maxAbs_val; auto).
      assert (/ nR2 <= RmaxAbsFun (invertInterval (Q2R e2lo, Q2R e2hi)))%R
        as upperBound_nR2
          by (apply contained_leq_maxAbs_val; auto).
      assert (-nR1 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi))%R
        as upperBound_Ropp_nR1
          by (apply contained_leq_maxAbs_neg_val; auto).
      assert (- / nR2 <= RmaxAbsFun (invertInterval (Q2R e2lo, Q2R e2hi)))%R
        as upperBound_Ropp_nR2
          by (apply contained_leq_maxAbs_neg_val; auto).
      assert (nR1 * Q2R err2 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2)%R
        as bound_nR1
          by (apply Rmult_le_compat_r; auto).
      assert (- nR1 * Q2R err2 <= RmaxAbsFun (Q2R e1lo, Q2R e1hi) * Q2R err2)%R
        as bound_neg_nR1
          by (apply Rmult_le_compat_r; auto).
      unfold invertInterval in *; simpl in upperBound_nR2, upperBound_Ropp_nR2.
      (* Case distinction for the divisor range
         positive or negative in float and real valued execution *)
      destruct no_div_zero_real as [ real_iv_neg | real_iv_pos];
        destruct no_div_zero_float as [float_iv_neg | float_iv_pos].
      (* The range of the divisor lies in the range from -infinity until 0 *)
      * unfold widenIntv in *; simpl in *.
        rewrite <- Q2R_plus in float_iv_neg.
        rewrite <- Q2R0_is_0 in float_iv_neg.
        rewrite <- Q2R0_is_0 in real_iv_neg.
        pose proof (err_prop_inversion_neg float_iv_neg real_iv_neg err2_bounded valid_intv2 H0 err2_pos) as err_prop_inv.
        rewrite Q2R_plus in float_iv_neg.
        rewrite Q2R0_is_0 in float_iv_neg.
        rewrite Q2R0_is_0 in real_iv_neg.
        rewrite Q2R_minus, Q2R_plus.
        repeat rewrite minAbs_negative_iv_is_hi; try lra.
        unfold Rdiv.
        repeat rewrite Q2R1.
        rewrite Rmult_1_l.
        (* Prove inequality to 0 in Q *)
        assert (e2lo == 0 -> False)
               by (rewrite <- Q2R0_is_0 in real_iv_neg; apply Rlt_Qlt in real_iv_neg;
                   assert (e2lo < 0) by (apply (Qle_lt_trans _ e2hi); try auto; apply Rle_Qle; lra);
                   lra).
        assert (e2hi == 0 -> False)
          by (rewrite <- Q2R0_is_0 in real_iv_neg; apply Rlt_Qlt in real_iv_neg; lra).
        rewrite Rabs_case_inverted in err1_bounded, err2_bounded.
        assert (nF1 <= Q2R err1 + nR1)%R as ub_nF1 by lra.
        assert (nR1 - Q2R err1 <= nF1)%R as lb_nF1 by lra.
        destruct err2_bounded as [[nR2_sub_pos err2_bounded] | [nR2_sub_neg err2_bounded]].
        (* Positive case for abs (nR2 - nF2) <= err2 *)
        { rewrite <- Ropp_mult_distr_l, <- Ropp_mult_distr_r, Ropp_involutive.
          apply Rgt_lt in nR2_sub_pos.
          assert (nF2 < nR2)%R as nF2_le_nR2 by lra.
          apply Ropp_lt_contravar in nF2_le_nR2.
          apply Rinv_lt_contravar in nF2_le_nR2; [ | apply Rmult_0_lt_preserving; try lra].
          repeat (rewrite <- Ropp_inv_permute in nF2_le_nR2; try lra).
          apply Ropp_lt_contravar in nF2_le_nR2.
          repeat rewrite Ropp_involutive in nF2_le_nR2.
          assert (/ nR2 - / nF2 < 0)%R as abs_inv_neg by lra.
          rewrite Rabs_left in err_prop_inv; try lra.
          rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded, err_prop_inv.
          assert (/nF2 <= /nR2 + Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R as error_prop_inv_up by lra.
          assert (/nR2 - Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) <= /nF2)%R as error_prop_inv_down by lra.
          (* Next do a case distinction for the absolute value*)
          unfold Rabs.
          destruct Rcase_abs.
          (* Case 1: Absolute value negative *)
          - rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr.
            rewrite Ropp_involutive.
            (* To upper bound terms, do a case distinction for nF1 *)
            destruct (Rle_lt_dec 0 nF1).
            (* 0 <= nF1 *)
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_l; try lra.
              apply error_prop_inv_up.
              destruct (Rle_lt_dec 0 (/ nR2 + Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                apply Rmult_le_compat_r; try lra.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 + err_inv) = nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                apply Rmult_le_compat_r; try lra.
                repeat (rewrite Q2R_inv; try auto).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                apply Rmult_le_compat_neg_l; try lra.
                apply lb_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (/ nR2 + err_inv) * (nR1 - Q2R err1) =
                          nR1 * err_inv - / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                repeat rewrite Rsub_eq_Ropp_Rplus.
                apply Rplus_le_compat.
                { apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                  rewrite Ropp_mult_distr_l.
                  apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
            (* nF1 < 0 *)
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                apply Rplus_le_compat_l.
                eapply Rmult_le_compat_r; try lra.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 - err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                    repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply lb_nF1.
                rewrite Rmult_comm.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (/ nR2 * nR1) + (/ nR2 - err_inv) * (nR1 - Q2R err1) = - nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
          (* Case 2: Absolute value positive *)
          - rewrite Rsub_eq_Ropp_Rplus, Ropp_mult_distr_l.
            destruct (Rle_lt_dec 0 (- nF1)).
            (* 0 <= - nF1 *)
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_l; try lra.
              apply error_prop_inv_up.
              destruct (Rle_lt_dec 0 (/ nR2 + Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                apply Rmult_le_compat_r; try lra.
                apply Ropp_le_contravar.
                apply lb_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + - (nR1 - Q2R err1) * (/ nR2 + err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                apply Rmult_le_compat_r; try lra.
                repeat (rewrite Q2R_inv; try auto).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                apply Rmult_le_compat_neg_l; try lra.
                apply Ropp_le_contravar.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 + err_inv) *  - (Q2R err1 + nR1) =  - nR1 * err_inv + - / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                repeat rewrite Rsub_eq_Ropp_Rplus.
                apply Rplus_le_compat.
                { apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                  apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
            (* - nF1 <= 0 *)
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                apply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_l; try lra.
                apply Ropp_le_contravar.
                apply lb_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 - err_inv) * - (nR1 - Q2R err1) = nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                    repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply Ropp_le_contravar.
                apply ub_nF1.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 - err_inv) * - (Q2R err1 + nR1) = nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
        }
        { rewrite <- Ropp_mult_distr_l, <- Ropp_mult_distr_r, Ropp_involutive.
          assert (nR2 <= nF2)%R as nR2_le_nF2 by lra.
          apply Ropp_le_contravar in nR2_le_nF2.
          apply Rinv_le_contravar in nR2_le_nF2; [ | lra].
          repeat (rewrite <- Ropp_inv_permute in nR2_le_nF2; try lra).
          apply Ropp_le_contravar in nR2_le_nF2.
          repeat rewrite Ropp_involutive in nR2_le_nF2.
          assert (0 <= / nR2 - / nF2)%R as abs_inv_pos by lra.
          rewrite Rabs_right in err_prop_inv; try lra.
          rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded, err_prop_inv.
          assert (/nF2 <= /nR2 + Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R as error_prop_inv_up by lra.
          assert (/nR2 - Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) <= /nF2)%R as error_prop_inv_down by lra.
          (* Next do a case distinction for the absolute value*)
          unfold Rabs.
          destruct Rcase_abs.
          - rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr.
            rewrite Ropp_involutive.
            (* To upper bound terms, do a case distinction for nF1 *)
            destruct (Rle_lt_dec 0 nF1).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_l; try lra.
              apply error_prop_inv_up.
              destruct (Rle_lt_dec 0 (/ nR2 + Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                apply Rmult_le_compat_r; try lra.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 + err_inv) = nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                apply Rmult_le_compat_r; try lra.
                repeat (rewrite Q2R_inv; try auto).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                apply Rmult_le_compat_neg_l; try lra.
                apply lb_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (/ nR2 + err_inv) * (nR1 - Q2R err1) = nR1 * err_inv - / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                repeat rewrite Rsub_eq_Ropp_Rplus.
                apply Rplus_le_compat.
                { apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                  rewrite Ropp_mult_distr_l.
                  apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                apply Rplus_le_compat_l.
                eapply Rmult_le_compat_r; try lra.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 - err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                    repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply lb_nF1.
                rewrite Rmult_comm.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (/ nR2 * nR1) + (/ nR2 - err_inv) * (nR1 - Q2R err1) = - nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
          - rewrite Rsub_eq_Ropp_Rplus.
            rewrite Ropp_mult_distr_l.
            destruct (Rle_lt_dec 0 (- nF1)).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_l; try lra.
              apply error_prop_inv_up.
              destruct (Rle_lt_dec 0 (/ nR2 + Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                apply Rmult_le_compat_r; try lra.
                apply Ropp_le_contravar.
                apply lb_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + - (nR1 - Q2R err1) * (/ nR2 + err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                apply Rmult_le_compat_r; try lra.
                repeat (rewrite Q2R_inv; try auto).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                apply Rmult_le_compat_neg_l; try lra.
                apply Ropp_le_contravar.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2) _).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 + err_inv) *  - (Q2R err1 + nR1) =  - nR1 * err_inv + - / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                repeat rewrite Rsub_eq_Ropp_Rplus.
                apply Rplus_le_compat.
                { apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
                  apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))).
              * eapply Rle_trans.
                apply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_l; try lra.
                apply Ropp_le_contravar.
                apply lb_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 - err_inv) * - (nR1 - Q2R err1) = nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                    repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_lt_0_inverting; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply Ropp_le_contravar.
                apply ub_nF1.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2hi + Q2R err2) * (Q2R e2hi + Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 - err_inv) * - (Q2R err1 + nR1) = nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
        }
      * unfold widenIntv in *; simpl in *.
        exfalso.
        assert (Q2R e2lo - Q2R err2 <= Q2R e2hi)%R by lra.
        assert (Q2R e2hi < Q2R e2lo - Q2R err2)%R by (apply (Rlt_trans _ 0 _); auto).
        lra.
      * unfold widenIntv in *; simpl in *.
        exfalso.
        assert (Q2R e2lo <= Q2R e2hi + Q2R err2)%R by lra.
        assert (Q2R e2hi + Q2R err2 < Q2R e2lo)%R as hierr_lt_lo by (apply (Rlt_trans _ 0 _); auto).
        apply Rlt_not_le in hierr_lt_lo.
        apply hierr_lt_lo; auto.
      * (** FIXME: Get rid of rewrites by fixing Lemma **)
        rewrite <- Q2R_minus in float_iv_pos.
        rewrite <- Q2R0_is_0 in float_iv_pos.
        rewrite <- Q2R0_is_0 in real_iv_pos.
        pose proof (err_prop_inversion_pos float_iv_pos real_iv_pos err2_bounded valid_intv2 H0 err2_pos) as err_prop_inv.
        rewrite Q2R_minus in float_iv_pos.
        rewrite Q2R0_is_0 in float_iv_pos.
        rewrite Q2R0_is_0 in real_iv_pos.
        rewrite Q2R_minus, Q2R_plus.
        repeat rewrite minAbs_positive_iv_is_lo; try lra.
        unfold Rdiv.
        repeat rewrite Q2R1.
        rewrite Rmult_1_l.
        (* Prove inequality to 0 in Q *)
        assert (e2lo == 0 -> False)
          by (rewrite <- Q2R0_is_0 in real_iv_pos; apply Rlt_Qlt in real_iv_pos; lra).
        assert (e2hi == 0 -> False)
          by (rewrite <- Q2R0_is_0 in real_iv_pos; apply Rlt_Qlt in real_iv_pos;
              assert (0 < e2hi) by (apply (Qlt_le_trans _ e2lo); try auto; apply Rle_Qle; lra);
              lra).
        rewrite Rabs_case_inverted in err1_bounded, err2_bounded.
        assert (nF1 <= Q2R err1 + nR1)%R as ub_nF1 by lra.
        assert (nR1 - Q2R err1 <= nF1)%R as lb_nF1 by lra.
        destruct err2_bounded as [[nR2_sub_pos err2_bounded] | [nR2_sub_neg err2_bounded]].
        { apply Rgt_lt in nR2_sub_pos.
          assert (nF2 < nR2)%R as nF2_le_nR2 by lra.
          apply Rinv_lt_contravar in nF2_le_nR2; [ | apply Rmult_0_lt_preserving; try lra].
          assert (/ nR2 - / nF2 <= 0)%R as abs_inv_neg by lra.
          rewrite Rabs_left in err_prop_inv; try lra.
          rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded.
          assert (/nR2 - Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) <= /nF2)%R as error_prop_inv_down by lra.
          assert (/nF2 <= /nR2 + Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))%R as error_prop_inv_up by lra.
          (* Next do a case distinction for the absolute value*)
          unfold Rabs.
          destruct Rcase_abs.
          - rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr.
            rewrite Ropp_involutive.
            (* To upper bound terms, do a case distinction for nF1 *)
            destruct (Rle_lt_dec 0 nF1).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat; try lra.
              hnf. left.
              apply Rinv_0_lt_compat; try lra.
              apply ub_nF1.
              apply error_prop_inv_up.
              rewrite (Rmult_comm (Q2R err2) _).
              remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
              assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 + err_inv) = nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
              rewrite simpl_properr.
              apply Rplus_le_compat_r.
              apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
              apply Rmult_le_compat; try lra.
              * hnf; left. apply Rinv_0_lt_compat; lra.
              * repeat (rewrite Q2R_inv; try auto).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))).
              * eapply Rle_trans.
                apply Rplus_le_compat_l.
                eapply Rmult_le_compat_r; try lra.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 - err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                    repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_0_lt_preserving; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply lb_nF1.
                rewrite Rmult_comm.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (/ nR2 * nR1) + (/ nR2 - err_inv) * (nR1 - Q2R err1) = - nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
          - rewrite Rsub_eq_Ropp_Rplus.
            rewrite Ropp_mult_distr_l.
            destruct (Rle_lt_dec 0 (- nF1)).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat; try lra.
              hnf; left.
              apply Rinv_0_lt_compat.
              apply (Rlt_le_trans _ (Q2R e2lo - Q2R err2)); try lra.
              apply Ropp_le_contravar.
              apply lb_nF1.
              apply error_prop_inv_up.
              rewrite (Rmult_comm (Q2R err2) _).
              remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
              assert ((nR1 * / nR2) + - (nR1 - Q2R err1) * (/ nR2 + err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                as simpl_properr by lra.
              rewrite simpl_properr.
              apply Rplus_le_compat_r.
              apply Rplus_le_compat.
              * apply Rmult_le_compat_r; try lra.
              * apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                eapply Rmult_le_compat_r; try lra.
                apply Ropp_le_contravar.
                apply lb_nF1.
                rewrite Rmult_comm.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (/ nR2 * nR1 + - (nR1 - Q2R err1) * (/ nR2 - err_inv) = nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_0_lt_preserving; try lra).
                          lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply Ropp_le_contravar.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 - err_inv) * - (Q2R err1 + nR1) = nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
        }
        {
          apply Rminus_le in nR2_sub_neg.
          apply Rinv_le_contravar in nR2_sub_neg; [ | lra].
          assert (0 <= / nR2 - / nF2)%R as abs_inv_pos by lra.
          rewrite Rabs_right in err_prop_inv; try lra.
          rewrite Rsub_eq_Ropp_Rplus in err1_bounded, err2_bounded.
          rewrite Ropp_plus_distr in err2_bounded.
          rewrite Ropp_involutive in err2_bounded.
          assert (/nR2 - Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) <= /nF2)%R as error_prop_inv_down by lra.
          assert (/nF2 <= /nR2 + Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))%R as error_prop_inv_up by lra.
          (* Next do a case distinction for the absolute value*)
          unfold Rabs.
          destruct Rcase_abs.
          - rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr.
            rewrite Ropp_involutive.
            (* To upper bound terms, do a case distinction for nF1 *)
            destruct (Rle_lt_dec 0 nF1).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat; try lra.
              hnf. left.
              apply Rinv_0_lt_compat; try lra.
              apply ub_nF1.
              apply error_prop_inv_up.
              rewrite (Rmult_comm (Q2R err2) _).
              remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
              assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 + err_inv) = nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
              rewrite simpl_properr.
              apply Rplus_le_compat_r.
              apply Rplus_le_compat; [ apply Rmult_le_compat_r; lra | ].
              apply Rmult_le_compat; try lra.
              * hnf; left. apply Rinv_0_lt_compat; lra.
              * repeat (rewrite Q2R_inv; try auto).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))).
              * eapply Rle_trans.
                apply Rplus_le_compat_l.
                eapply Rmult_le_compat_r; try lra.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (nR1 * / nR2) + (Q2R err1 + nR1) * (/ nR2 - err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                    repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_0_lt_preserving; try lra).
                    lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply lb_nF1.
                rewrite Rmult_comm.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (- (/ nR2 * nR1) + (/ nR2 - err_inv) * (nR1 - Q2R err1) = - nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
          - rewrite Rsub_eq_Ropp_Rplus.
            rewrite Ropp_mult_distr_l.
            destruct (Rle_lt_dec 0 (- nF1)).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat; try lra.
              hnf; left.
              apply Rinv_0_lt_compat.
              apply (Rlt_le_trans _ (Q2R e2lo - Q2R err2)); try lra.
              apply Ropp_le_contravar.
              apply lb_nF1.
              apply error_prop_inv_up.
              rewrite (Rmult_comm (Q2R err2) _).
              remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
              assert ((nR1 * / nR2) + - (nR1 - Q2R err1) * (/ nR2 + err_inv) = - nR1 * err_inv + / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                as simpl_properr by lra.
              rewrite simpl_properr.
              apply Rplus_le_compat_r.
              apply Rplus_le_compat.
              * apply Rmult_le_compat_r; try lra.
              * apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto).
            + eapply Rle_trans.
              eapply Rplus_le_compat_l.
              eapply Rmult_le_compat_neg_l; try lra.
              apply error_prop_inv_down.
              destruct (Rle_lt_dec 0 (/ nR2 - Q2R err2 * / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))).
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                eapply Rmult_le_compat_r; try lra.
                apply Ropp_le_contravar.
                apply lb_nF1.
                rewrite Rmult_comm.
                setoid_rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (/ nR2 * nR1 + - (nR1 - Q2R err1) * (/ nR2 - err_inv) = nR1 * err_inv + / nR2 * Q2R err1 - Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
                { assert (0 <= err_inv)%R.
                  - subst.
                    assert (0 < / ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)))%R
                      by (apply Rinv_0_lt_compat; apply Rmult_0_lt_preserving; try lra).
                          lra.
                  - assert (0 <= (Q2R err1 * err_inv))%R
                      by (rewrite <- (Rmult_0_l 0); apply Rmult_le_compat; lra).
                    apply (Rle_trans _ 0); lra. }
              * eapply Rle_trans.
                eapply Rplus_le_compat_l.
                rewrite Rmult_comm.
                eapply Rmult_le_compat_neg_l.
                hnf; left; auto.
                apply Ropp_le_contravar.
                apply ub_nF1.
                rewrite (Rmult_comm (Q2R err2)).
                remember (/ ((Q2R e2lo - Q2R err2) * (Q2R e2lo - Q2R err2)) * Q2R err2)%R as err_inv.
                assert (nR1 * / nR2 + (/ nR2 - err_inv) * - (Q2R err1 + nR1) = nR1 * err_inv + - / nR2 * Q2R err1 + Q2R err1 * err_inv)%R
                  as simpl_properr by lra.
                rewrite simpl_properr.
                apply Rplus_le_compat_r.
                apply Rplus_le_compat.
                { apply Rmult_le_compat_r; try lra. }
                { apply Rmult_le_compat_r; try lra.
                  repeat (rewrite Q2R_inv; try auto). }
        }
    + assert (IVhi (widenInterval (Q2R e2lo, Q2R e2hi) (Q2R err2)) < 0 \/ 0 < IVlo (widenInterval (Q2R e2lo, Q2R e2hi) (Q2R err2)))%R
        as no_div_zero_widen
             by (unfold widenInterval in *; simpl in *; rewrite Q2R_plus, Q2R_minus in no_div_zero_float; auto).
      pose proof (IntervalArith.interval_division_valid _ _ no_div_zero_widen H H0) as valid_div_float.
      unfold widenInterval in *; simpl in *.
      assert (e2lo - err2 == 0 -> False).
      * hnf; intros.
        destruct no_div_zero_float as [float_iv | float_iv]; rewrite <- Q2R0_is_0 in float_iv; apply Rlt_Qlt in float_iv; try lra.
        assert (Q2R e2lo - Q2R err2 <= Q2R e2hi + Q2R err2)%R by lra.
        rewrite<- Q2R_minus, <- Q2R_plus in H4.
        apply Rle_Qle in H4. lra.
      * assert (e2hi + err2 == 0 -> False).
        { hnf; intros.
          destruct no_div_zero_float as [float_iv | float_iv]; rewrite <- Q2R0_is_0 in float_iv; apply Rlt_Qlt in float_iv; try lra.
          assert (Q2R e2lo - Q2R err2 <= Q2R e2hi + Q2R err2)%R by lra.
          rewrite<- Q2R_minus, <- Q2R_plus in H5.
          apply Rle_Qle in H5. lra. }
        { destruct valid_div_float.
          rewrite computeErrorQ_computeErrorR, <- maxAbs_impl_RmaxAbs_iv.
          apply computeErrorR_up.
          apply contained_leq_maxAbs.
          simpl in *; split.
          - rewrite Q2R_min4.
            repeat rewrite Q2R_mult.
            repeat (rewrite Q2R_inv; auto).
            repeat rewrite Q2R_minus, Q2R_plus; auto.
          - rewrite Q2R_max4.
            repeat rewrite Q2R_mult.
            repeat (rewrite Q2R_inv; auto).
            repeat rewrite Q2R_minus.
            repeat rewrite Q2R_plus; auto. }
  - apply le_neq_bool_to_lt_prop in no_div_zero_float.
    unfold widenInterval in *; simpl in *.
    assert (e2lo - err2 == 0 -> False).
    + hnf; intros.
      destruct no_div_zero_float as [float_iv | float_iv]; try lra.
      assert (Q2R e2lo - Q2R err2 <= Q2R e2hi + Q2R err2)%R by lra.
      rewrite<- Q2R_minus, <- Q2R_plus in H2.
      apply Rle_Qle in H2. lra.
    + assert (e2hi + err2 == 0 -> False).
      * hnf; intros.
        destruct no_div_zero_float as [float_iv | float_iv]; try lra.
        assert (Q2R e2lo - Q2R err2 <= Q2R e2hi + Q2R err2)%R by lra.
        rewrite<- Q2R_minus, <- Q2R_plus in H3.
        apply Rle_Qle in H3. lra.
      * unfold widenIntv; simpl.
        hnf. intros.
        assert (forall a, Qabs a == 0 -> a == 0).
        { intros. unfold Qabs in H4. destruct a.
          rewrite <- Z.abs_0 in H4. inversion H4. rewrite Zmult_1_r in *.
          rewrite Z.abs_0_iff in H6.
          rewrite H6. rewrite Z.abs_0. hnf. simpl; auto. }
        { assert (minAbs (e2lo - err2, e2hi + err2) == 0 -> False).
          - unfold minAbs. unfold fst, snd. apply Q.min_case_strong.
            + intros. apply H6; rewrite H5; auto.
            + intros. apply H1. rewrite (H4 (e2lo-err2) H6). hnf. auto.
            + intros. apply H2. rewrite H4; auto. hnf; auto.
          - rewrite <- (Qmult_0_l (minAbs (e2lo - err2, e2hi + err2))) in H3.
            rewrite (Qmult_inj_r) in H3; auto. }
Qed.

Lemma validErrorboundCorrectFma E1 E2 A
      (e1:expr Q) (e2:expr Q) (e3: expr Q) (nR nR1 nR2 nR3 nF nF1 nF2 nF3: R)
      (e err1 err2 err3 :error) (alo ahi e1lo e1hi e2lo e2hi e3lo e3hi:Q) dVars
      (m m1 m2 m3:mType) Gamma DeltaMap:
  eval_Real E1 Gamma e1 nR1 ->
  eval_Real E1 Gamma e2 nR2 ->
  eval_Real E1 Gamma e3 nR3 ->
  eval_Real E1 Gamma (Fma e1 e2 e3) nR ->
  eval_Fin E2 Gamma DeltaMap e1 nF1 m1 ->
  eval_Fin E2 Gamma DeltaMap e2 nF2 m2 ->
  eval_Fin E2 Gamma DeltaMap e3 nF3 m3 ->
  eval_expr (updEnv 3 nF3 (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv)))
            (updDefVars (Fma (Var R 1) (Var R 2) (Var R 3)) m
                        (updDefVars (Var Rdefinitions.R 3) m3
                        (updDefVars (Var Rdefinitions.R 2) m2
                                    (updDefVars (Var Rdefinitions.R 1) m1 (toRExpMap Gamma)))))
            (fun x _ => if Req_dec_sum x (evalFma nF1 nF2 nF3)
                     then DeltaMap (evalFma nF1 nF2 nF3) m
                     else None)
            (toRExp (Fma (Var Q 1) (Var Q 2) (Var Q 3))) nF m ->
  validErrorbound (Fma e1 e2 e3) Gamma A dVars = true ->
  (Q2R e1lo <= nR1 <= Q2R e1hi)%R ->
  (Q2R e2lo <= nR2 <= Q2R e2hi)%R ->
  (Q2R e3lo <= nR3 <= Q2R e3hi)%R ->
  FloverMap.find e1 A = Some ((e1lo,e1hi),err1) ->
  FloverMap.find e2 A = Some ((e2lo, e2hi),err2) ->
  FloverMap.find e3 A = Some ((e3lo, e3hi),err3) ->
  FloverMap.find (Fma e1 e2 e3) A = Some ((alo,ahi),e)->
  FloverMap.find (Fma e1 e2 e3) Gamma = Some m ->
  (Rabs (nR1 - nF1) <= (Q2R err1))%R ->
  (Rabs (nR2 - nF2) <= (Q2R err2))%R ->
  (Rabs (nR3 - nF3) <= (Q2R err3))%R ->
  (Rabs (nR - nF) <= (Q2R e))%R.
Proof.
  intros e1_real e2_real e3_real eval_real e1_float e2_float e3_float eval_float
         valid_error valid_e1 valid_e2 valid_e3 A_e1 A_e2 A_e3 A_fma type_fma
         err1_bounded err2_bounded err3_bounded.
  cbn in *; Flover_compute; type_conv; subst.
  eapply Rle_trans.
  eapply (fma_abs_err_bounded e1 e2 e3); eauto.
  rename R0 into valid_error.
  assert (0 <= Q2R err1)%R as err1_pos by (eapply (err_always_positive e1 Gamma A dVars); eauto).
  assert (0 <= Q2R err2)%R as err2_pos by (eapply (err_always_positive e2 Gamma A dVars); eauto).
  assert (0 <= Q2R err3)%R as err3_pos by (eapply (err_always_positive e3 Gamma A dVars); eauto).
  canonize_hyps.
  repeat rewrite Q2R_plus in valid_error.
  repeat rewrite Q2R_mult in valid_error.
  repeat rewrite Q2R_plus in valid_error.
  repeat rewrite <- Rabs_eq_Qabs in valid_error.
  repeat rewrite Q2R_plus in valid_error.
  repeat rewrite <- maxAbs_impl_RmaxAbs in valid_error.
  eapply Rle_trans. 2: eauto.
  apply Rplus_le_compat.
  - eauto using Rle_trans, Rabs_triang, Rplus_le_compat, multiplicationErrorBounded.
  - assert (contained nR1 (Q2R e1lo, Q2R e1hi)) as contained_intv1 by auto.
    pose proof (distance_gives_iv (a:=nR1) _ (Q2R e1lo, Q2R e1hi) contained_intv1 err1_bounded)
         as valid_err1.
    assert (contained nR2 (Q2R e2lo, Q2R e2hi)) as contained_intv2 by auto.
    pose proof (distance_gives_iv (a:=nR2) _ _ contained_intv2 err2_bounded)
         as valid_err2.
    assert (contained nR3 (Q2R e3lo, Q2R e3hi)) as contained_intv3 by auto.
    pose proof (distance_gives_iv (a:=nR3) _ _ contained_intv3 err3_bounded)
         as valid_err3.
    pose proof (IntervalArith.interval_multiplication_valid _ _ valid_err1 valid_err2)
         as valid_err_mult.
    pose proof (IntervalArith.interval_addition_valid _ _ valid_err_mult valid_err3).
    rewrite computeErrorQ_computeErrorR, <- maxAbs_impl_RmaxAbs_iv.
    apply computeErrorR_up.
    apply contained_leq_maxAbs.
    simpl in *; split.
    + rewrite Q2R_min4.
      repeat rewrite Q2R_mult;
        repeat rewrite Q2R_minus;
        repeat rewrite Q2R_plus;
        repeat rewrite Q2R_minus.
      rewrite Q2R_max4.
      rewrite Q2R_min4.
      repeat rewrite Q2R_mult;
        repeat rewrite Q2R_minus;
        repeat rewrite Q2R_plus;
        repeat rewrite Q2R_minus.
      lra.
    + rewrite Q2R_max4.
      repeat rewrite Q2R_mult;
        repeat rewrite Q2R_minus;
        repeat rewrite Q2R_plus;
        repeat rewrite Q2R_minus.
      rewrite Q2R_max4.
      rewrite Q2R_min4.
      repeat rewrite Q2R_mult;
        repeat rewrite Q2R_minus;
        repeat rewrite Q2R_plus;
        repeat rewrite Q2R_minus.
      lra.
Qed.

Lemma validErrorboundCorrectRounding E1 E2 A (e: expr Q) (nR nF nF1: R)
      (err err':error) (elo ehi alo ahi: Q) dVars (m: mType)
      (mEps:mType) Gamma DeltaMap:
  eval_Real E1 Gamma e nR ->
  eval_Fin E2 Gamma DeltaMap e nF1 m ->
  eval_expr (updEnv 1 nF1 emptyEnv)
            (updDefVars (Downcast mEps (Var R 1)) mEps (updDefVars (Var R 1) m (toRExpMap Gamma)))
            (fun x _ => if Req_dec_sum x nF1
                     then DeltaMap nF1 mEps
                     else None)
            (toRExp (Downcast mEps (Var Q 1))) nF mEps ->
  validErrorbound (Downcast mEps e) Gamma A dVars = true ->
  (Q2R elo <= nR <= Q2R ehi)%R ->
  FloverMap.find e A = Some ((elo, ehi), err) ->
  FloverMap.find (Downcast mEps e) A = Some ((alo, ahi), err') ->
  FloverMap.find (Downcast mEps e) Gamma = Some mEps ->
  (Rabs (nR - nF1) <= (Q2R err))%R ->
  (Rabs (nR - nF) <= (Q2R err'))%R.
Proof.
  intros eval_real eval_float eval_float_rnd subexprr_ok valid_error valid_intv
         A_e A_rnd err_bounded.
  cbn in *; Flover_compute; type_conv; subst.
  inversion eval_float_rnd; subst.
  clear H6.
  inversion H7; subst. cbn in H0, H5.
  eapply Rle_trans.
  eapply round_abs_err_bounded; eauto.
  assert (contained nR (Q2R elo, Q2R ehi)) as valid_intv_c by (auto).
  pose proof (distance_gives_iv _ _ valid_intv_c err_bounded) as dgi.
  destruct dgi as [dgi1 dgi2]; simpl in dgi1, dgi2.
  canonize_hyps.
  eapply Rle_trans; eauto.
  rewrite Q2R_plus.
  apply Rplus_le_compat_l.
  rewrite computeErrorQ_computeErrorR, <- maxAbs_impl_RmaxAbs_iv.
  apply computeErrorR_up.
  apply contained_leq_maxAbs.
  simpl in *; split; try rewrite Q2R_plus in *;
    try rewrite Q2R_minus in *;
    lra.
Qed.

End soundnessProofs.
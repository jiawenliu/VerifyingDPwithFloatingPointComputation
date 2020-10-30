(**
Proofs of general bounds on the error of arithmetic exprressions.
This shortens soundness proofs later.
Bounds are exprlained in section 5, Deriving Computable Error Bounds
**)
From Coq
     Require Import Reals.Reals micromega.Psatz QArith.QArith QArith.Qreals.

From Snapv
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealSimps
     Infra.RealRationalProps Environments Infra.ExpressionAbbrevs
     ExpressionSemantics.

Lemma const_abs_err_bounded (n:R) (nR:R) (nF:R) (E1 E2:env) (m:mType) defVars DeltaMap:
  eval_expr E1 (toRTMap defVars) DeltaMapR (Const REAL n) nR REAL ->
  eval_expr E2 defVars DeltaMap (Const m n) nF m ->
  (Rabs (nR - nF) <= computeErrorR n m)%R.
Proof.
  intros eval_real eval_float.
  inversion eval_real; subst.
  rewrite delta_0_deterministic; auto.
  inversion eval_float; subst.
  unfold perturb; simpl.
  unfold computeErrorR.
  destruct m.
  { unfold Rminus. rewrite Rplus_opp_r. rewrite Rabs_R0; lra. }
  all: try rewrite Rabs_err_simpl, Rabs_mult.
  all: try apply Rmult_le_compat_l; try auto using Rabs_pos.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r, Rplus_0_l.
  rewrite Rabs_Ropp; auto.
Qed.

Lemma add_abs_err_bounded (e1:expr Q) (e1R:R) (e1F:R) (e2:expr Q) (e2R:R) (e2F:R)
      (vR:R) (vF:R) (E1 E2:env) (err1 err2 :Q) (m m1 m2:mType) defVars DeltaMap:
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e1)) e1R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e1) e1F m1->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e2)) e2R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e2) e2F m2 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (Binop Plus (toRExp e1) (toRExp e2))) vR REAL ->
  eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
            (updDefVars (Binop Plus (Var R 1) (Var R 2)) m
                        (updDefVars (Var R 2) m2 (updDefVars (Var R 1) m1 defVars)))
            (fun x _ => if Req_dec_sum x (evalBinop Plus e1F e2F)
                     then DeltaMap (evalBinop Plus e1F e2F) m
                     else None)
            (Binop Plus (Var R 1) (Var R 2)) vF m ->
  (Rabs (e1R - e1F) <= Q2R err1)%R ->
  (Rabs (e2R - e2F) <= Q2R err2)%R ->
  (Rabs (vR - vF) <= Q2R err1 + Q2R err2 + computeErrorR (e1F + e2F) m)%R.
Proof.
  intros e1_real e1_float e2_real e2_float plus_real plus_float bound_e1 bound_e2.
  (* Prove that e1R and e2R are the correct values and that vR is e1R + e2R *)
  inversion plus_real; subst.
  assert (m0 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  assert (m3 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  subst; simpl in H3; auto.
  rewrite delta_0_deterministic in plus_real; auto.
  rewrite (delta_0_deterministic (evalBinop Plus v1 v2) REAL delta); auto.
  unfold evalBinop in *; simpl in *.
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real);
    rewrite (meps_0_deterministic (toRExp e2) H9 e2_real).
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real) in plus_real.
  rewrite (meps_0_deterministic (toRExp e2) H9 e2_real) in plus_real.
  (* Now unfold the float valued evaluation to get the deltas we need for the inequality *)
  inversion plus_float; subst.
  unfold perturb; simpl.
  inversion H13; subst; inversion H16; subst.
  unfold updEnv in H1, H15; simpl in *.
  symmetry in H1,H15.
  inversion H1; inversion H15; subst.
  (* We have now obtained all necessary values from the evaluations --> remove them for readability *)
  clear plus_float H4 H7 plus_real e1_real e1_float e2_real e2_float H8 H6 H1.
  repeat rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite Rsub_eq_Ropp_Rplus.
  unfold computeErrorR.
  pose proof (Rabs_triang (e1R + - e1F) ((e2R + - e2F) + - ((e1F + e2F) * delta0))).
  destruct m;
    repeat rewrite Ropp_plus_distr; try rewrite plus_bounds_simplify; try rewrite Rplus_assoc.
  { repeat rewrite <- Rplus_assoc.
    assert (e1R + e2R + - e1F + - e2F = e1R + - e1F + e2R + - e2F)%R by lra.
    rewrite H1; clear H1.
    rewrite Rplus_assoc.
    eapply Rle_trans.
    apply Rabs_triang; apply Rplus_le_compat; try auto.
    rewrite Rplus_0_r.
    apply Rplus_le_compat; try auto. }
  4: {
    eapply Rle_trans; [ apply Rabs_triang | rewrite (Rplus_assoc (Q2R err1)) ].
    apply Rplus_le_compat; try auto.
    eapply Rle_trans; [ apply Rabs_triang |].
    apply Rplus_le_compat; try auto.
    rewrite Rabs_Ropp; simpl. auto. }
  all: eapply Rle_trans; try eapply H.
  all: setoid_rewrite Rplus_assoc at 2.
  all: eapply Rplus_le_compat; try auto.
  all: eapply Rle_trans; try eapply Rabs_triang.
  all: eapply Rplus_le_compat; try auto.
  all: rewrite Rabs_Ropp, Rabs_mult.
  all: eapply Rmult_le_compat_l; try auto using Rabs_pos.
Qed.

(**
  Copy-Paste proof with minor differences, was easier then manipulating the evaluations and then applying the lemma
**)
Lemma subtract_abs_err_bounded (e1:expr Q) (e1R:R) (e1F:R) (e2:expr Q) (e2R:R)
      (e2F:R) (vR:R) (vF:R) (E1 E2:env) err1 err2 (m m1 m2:mType) defVars DeltaMap:
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e1)) e1R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e1) e1F m1 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e2)) e2R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e2) e2F m2 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (Binop Sub (toRExp e1) (toRExp e2))) vR REAL ->
  eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
            (updDefVars (Binop Sub (Var R 1) (Var R 2)) m
                        (updDefVars (Var R 2) m2 (updDefVars (Var R 1) m1 defVars)))
            (fun x _ => if Req_dec_sum x (evalBinop Sub e1F e2F)
                     then DeltaMap (evalBinop Sub e1F e2F) m
                     else None)
            (Binop Sub (Var R 1) (Var R 2)) vF m ->
  (Rabs (e1R - e1F) <= Q2R err1)%R ->
  (Rabs (e2R - e2F) <= Q2R err2)%R ->
  (Rabs (vR - vF) <= Q2R err1 + Q2R err2 + computeErrorR (e1F - e2F) m)%R.
Proof.
  intros e1_real e1_float e2_real e2_float sub_real sub_float bound_e1 bound_e2.
  (* Prove that e1R and e2R are the correct values and that vR is e1R + e2R *)
  inversion sub_real; subst.
  assert (m0 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  assert (m3 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  subst; simpl in H3; auto.
  rewrite delta_0_deterministic in sub_real; auto.
  rewrite (delta_0_deterministic (evalBinop Sub v1 v2) REAL delta); auto.
  unfold evalBinop in *; simpl in *.
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real);
    rewrite (meps_0_deterministic (toRExp e2) H9 e2_real).
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real) in sub_real.
  rewrite (meps_0_deterministic (toRExp e2) H9 e2_real) in sub_real.
  (* Now unfold the float valued evaluation to get the deltas we need for the inequality *)
  inversion sub_float; subst.
  unfold perturb; simpl.
  inversion H13; subst; inversion H16; subst.
  unfold updEnv in H1,H15; simpl in *.
  symmetry in H1,H15.
  inversion H1; inversion H15; subst.
  (* We have now obtained all necessary values from the evaluations --> remove them for readability *)
  clear sub_float H4 H7 sub_real e1_real e1_float e2_real e2_float H8 H6 H1.
  repeat rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  repeat rewrite Rsub_eq_Ropp_Rplus.
  unfold computeErrorR.
  pose proof (Rabs_triang (e1R + - e1F) ((e2R + - e2F) + - ((e1F + e2F) * delta))).
  destruct m;
    repeat rewrite Ropp_plus_distr; try rewrite Ropp_involutive;
      try rewrite plus_bounds_simplify; try rewrite Rplus_assoc.
  { repeat rewrite <- Rplus_assoc.
    assert (e1R + - e2R + - e1F + e2F = e1R + - e1F + - e2R + e2F)%R by lra.
    rewrite H1; clear H1.
    rewrite Rplus_assoc.
    eapply Rle_trans.
    apply Rabs_triang; apply Rplus_le_compat; try auto.
    rewrite Rplus_0_r.
    apply Rplus_le_compat; try auto.
    rewrite Rplus_comm, <- Rsub_eq_Ropp_Rplus, Rabs_minus_sym.
    auto. }
  4: {
    eapply Rle_trans.
    apply Rabs_triang. setoid_rewrite Rplus_assoc at 2.
    apply Rplus_le_compat; try auto.
    eapply Rle_trans.
    apply Rabs_triang.
    rewrite Rabs_Ropp. apply Rplus_le_compat; try auto.
    rewrite Rplus_comm, <- Rsub_eq_Ropp_Rplus, Rabs_minus_sym.
    auto. }
  all: eapply Rle_trans; try eapply Rabs_triang.
  all: setoid_rewrite Rplus_assoc at 2.
  all: eapply Rplus_le_compat; try auto.
  all: eapply Rle_trans; try eapply Rabs_triang.
  all: eapply Rplus_le_compat.
  all: try (rewrite Rplus_comm, <- Rsub_eq_Ropp_Rplus, Rabs_minus_sym; auto; fail).
  all: rewrite Rabs_Ropp, Rabs_mult, <- Rsub_eq_Ropp_Rplus.
  all: eapply Rmult_le_compat_l; try auto using Rabs_pos.
Qed.

Lemma mult_abs_err_bounded (e1:expr Q) (e1R:R) (e1F:R) (e2:expr Q) (e2R:R) (e2F:R)
      (vR:R) (vF:R) (E1 E2:env) (m m1 m2:mType) defVars DeltaMap:
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e1)) e1R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e1) e1F m1 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e2)) e2R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e2) e2F m2 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (Binop Mult (toRExp e1) (toRExp e2))) vR REAL ->
  eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
            (updDefVars (Binop Mult (Var R 1) (Var R 2)) m
                        (updDefVars (Var R 2) m2 (updDefVars (Var R 1) m1 defVars)))
            (fun x _ => if Req_dec_sum x (evalBinop Mult e1F e2F)
                     then DeltaMap (evalBinop Mult e1F e2F) m
                     else None)
            (Binop Mult (Var R 1) (Var R 2)) vF m ->
  (Rabs (vR - vF) <= Rabs (e1R * e2R - e1F * e2F) + computeErrorR (e1F * e2F) m)%R.
Proof.
  intros e1_real e1_float e2_real e2_float mult_real mult_float.
  (* Prove that e1R and e2R are the correct values and that vR is e1R * e2R *)
  inversion mult_real; subst;
  assert (m0 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  assert (m3 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  subst; simpl in H3; auto.
  rewrite delta_0_deterministic in mult_real; auto.
  rewrite delta_0_deterministic; auto.
  unfold evalBinop in *; simpl in *.
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real);
    rewrite (meps_0_deterministic (toRExp e2) H9 e2_real).
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real) in mult_real.
  rewrite (meps_0_deterministic (toRExp e2) H9 e2_real) in mult_real.
  (* Now unfold the float valued evaluation to get the deltas we need for the inequality *)
  inversion mult_float; subst.
  unfold perturb; simpl.
  inversion H13; subst; inversion H16; subst.
  unfold updEnv in H1,H15; simpl in *.
  symmetry in H1,H15.
  inversion H1; inversion H15; subst.
  (* We have now obtained all necessary values from the evaluations --> remove them for readability *)
  clear mult_float H7 mult_real e1_real e1_float e2_real e2_float H6 H1.
  repeat rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite Rsub_eq_Ropp_Rplus.
  unfold computeErrorR.
  destruct m.
  all: try rewrite Ropp_plus_distr, <- Rplus_assoc.
  { rewrite Rplus_0_r. rewrite <- Rsub_eq_Ropp_Rplus; lra. }
  all: eapply Rle_trans; try apply Rabs_triang.
  all: try rewrite <- Rsub_eq_Ropp_Rplus, Rabs_Ropp; try rewrite Rabs_mult.
  all: eapply Rplus_le_compat_l; try auto.
  all: eapply Rmult_le_compat_l; try auto using Rabs_pos.
Qed.

Lemma div_abs_err_bounded (e1:expr Q) (e1R:R) (e1F:R) (e2:expr Q) (e2R:R) (e2F:R)
      (vR:R) (vF:R) (E1 E2:env) (m m1 m2:mType) defVars DeltaMap:
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e1)) e1R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e1) e1F m1 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (toRExp e2)) e2R REAL ->
  eval_expr E2 defVars DeltaMap (toRExp e2) e2F m2 ->
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval (Binop Div (toRExp e1) (toRExp e2))) vR REAL ->
  eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
            (updDefVars (Binop Div (Var R 1) (Var R 2)) m
                        (updDefVars (Var R 2) m2 (updDefVars (Var R 1) m1 defVars)))
            (fun x _ => if Req_dec_sum x (evalBinop Div e1F e2F)
                     then DeltaMap (evalBinop Div e1F e2F) m
                     else None)
            (Binop Div (Var R 1) (Var R 2)) vF m ->
  (Rabs (vR - vF) <= Rabs (e1R / e2R - e1F / e2F) + computeErrorR (e1F / e2F) m)%R.
Proof.
  intros e1_real e1_float e2_real e2_float div_real div_float.
  (* Prove that e1R and e2R are the correct values and that vR is e1R * e2R *)
  inversion div_real; subst;
  assert (m0 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  assert (m3 = REAL) by (eapply toRTMap_eval_REAL; eauto).
  subst; simpl in H3; auto.
  rewrite delta_0_deterministic in div_real; auto.
  rewrite delta_0_deterministic; auto.
  unfold evalBinop in *; simpl in *.
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real);
    rewrite (meps_0_deterministic (toRExp e2) H9 e2_real).
  rewrite (meps_0_deterministic (toRExp e1) H6 e1_real) in div_real.
  rewrite (meps_0_deterministic (toRExp e2) H9 e2_real) in div_real.
  (* Now unfold the float valued evaluation to get the deltas we need for the inequality *)
  inversion div_float; subst.
  unfold perturb; simpl.
  inversion H13; subst; inversion H16; subst.
  unfold updEnv in H1,H15; simpl in *.
  symmetry in H1,H15.
  inversion H1; inversion H15; subst.
  (* We have now obtained all necessary values from the evaluations --> remove them for readability *)
  clear div_float H0 H1 div_real e1_real e1_float e2_real e2_float.
  repeat rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite Rsub_eq_Ropp_Rplus.
  unfold computeErrorR.
  destruct m.
  all: try rewrite Ropp_plus_distr, <- Rplus_assoc.
  { rewrite Rplus_0_r. rewrite <- Rsub_eq_Ropp_Rplus; lra. }
  all: eapply Rle_trans; try apply Rabs_triang.
  all: try rewrite <- Rsub_eq_Ropp_Rplus, Rabs_Ropp; try rewrite Rabs_mult.
  all: eapply Rplus_le_compat_l; try auto.
  all: eapply Rmult_le_compat_l; try auto using Rabs_pos.
Qed.

(*
Lemma round_abs_err_bounded (e:expr R) (nR nF1 nF:R) (E1 E2: env) (err:R)
      (mEps m:mType) defVars DeltaMap:
  eval_expr E1 (toRTMap defVars) DeltaMapR (toREval e) nR REAL ->
  eval_expr E2 defVars DeltaMap e nF1 m ->
  eval_expr (updEnv 1 nF1 emptyEnv)
            (updDefVars (Downcast mEps (Var R 1)) mEps
                        (updDefVars (Var R 1) m defVars))
            (fun x _ => if Req_dec_sum x nF1
                     then DeltaMap nF1 mEps
                     else None)
            (toRExp (Downcast mEps (Var Q 1))) nF mEps->
  (Rabs (nR - nF1) <= err)%R ->
  (Rabs (nR - nF) <= err + computeErrorR nF1 mEps)%R.
Proof.
  intros eval_real eval_float eval_float_rnd err_bounded.
  replace (nR - nF)%R with ((nR - nF1) + (nF1 - nF))%R by lra.
  eapply Rle_trans.
  apply (Rabs_triang (nR - nF1) (nF1 - nF)).
  apply (Rle_trans _ (err + Rabs (nF1 - nF))  _).
  - apply Rplus_le_compat_r; assumption.
  - apply Rplus_le_compat_l.
    inversion eval_float_rnd; subst.
    inversion H7; subst.
    inversion H0; subst.
    unfold perturb; simpl.
    unfold updEnv in H5; simpl in H5; inversion H5; subst.
    unfold computeErrorR.
    destruct mEps.
    { unfold Rminus. rewrite Rplus_opp_r, Rabs_R0; lra. }
    all: replace (v1 - v1 * (1 + delta))%R with (- (v1 * delta))%R by lra.
    all: replace (Rabs (-(v1*delta))) with (Rabs (v1*delta)) by (symmetry; apply Rabs_Ropp).
    all: try rewrite Rabs_mult; try apply Rmult_le_compat_l; auto using Rabs_pos.
    unfold Rminus.
    rewrite Ropp_plus_distr, <- Rplus_assoc.
    rewrite Rplus_opp_r, Rplus_0_l, Rabs_Ropp; auto.
Qed.*)

Lemma err_prop_inversion_pos_real nF nR err elo ehi
      (float_iv_pos : (0 < elo - err)%R)
      (real_iv_pos : (0 < elo)%R)
      (err_bounded : (Rabs (nR - nF) <= err)%R)
      (valid_bounds_e2 : (elo <= nR <= ehi)%R)
      (valid_bounds_e2_err : (elo - err <= nF <= ehi + err)%R)
      (err_pos : (0 <= err)%R):
  (Rabs (/nR - / nF) <= err * / ((elo - err) * (elo- err)))%R.
Proof.
  rewrite Rabs_case_inverted in err_bounded.
  assert (0 < nF)%R as nF_pos by lra.
  destruct err_bounded as [ [diff_pos err_bounded] | [diff_neg err_bounded]].
  - cut (0 < /nF - / nR)%R.
    + intros abs_neg.
      rewrite Rabs_left; try lra.
      rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr, Ropp_involutive.
      rewrite Ropp_inv_permute; try lra.
      apply (Rle_trans _ (/ - nR + / (nR - err))).
      * apply Rplus_le_compat_l.
        apply Rinv_le_contravar; lra.
      * rewrite equal_naming_inv; try lra.
        assert (- nR + (nR - err) = - err)%R as simplify_up by lra.
        rewrite simplify_up.
        unfold Rdiv.
        repeat(rewrite <- Ropp_mult_distr_l); rewrite <- Ropp_inv_permute.
        {
          rewrite <- Ropp_mult_distr_r, Ropp_involutive.
          apply Rmult_le_compat_l; try lra.
          apply Rinv_le_contravar.
          - apply Rmult_0_lt_preserving; lra.
          - apply Rmult_le_compat; lra.
        }
        { assert (0 < nR * (nR - err))%R by (apply Rmult_0_lt_preserving; lra); lra. }
    + cut (/ nR < /nF)%R.
      * intros; lra.
      * apply Rinv_lt_contravar; try lra.
        apply Rmult_0_lt_preserving; lra.
  - cut (0 <= /nR - /nF)%R.
    + intros abs_pos.
      rewrite Rabs_right; try lra.
      rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr, Ropp_involutive in err_bounded.
      rewrite Rsub_eq_Ropp_Rplus.
      apply (Rle_trans _ (/nR - / (nR + err))).
      * apply Rplus_le_compat_l.
        apply Ropp_le_contravar.
        apply Rinv_le_contravar; lra.
      * rewrite Rsub_eq_Ropp_Rplus, Ropp_inv_permute; try lra.
        rewrite equal_naming_inv; try lra.
        assert (nR + - (nR + err) = - err)%R as simpl_up by lra.
        rewrite simpl_up.
        unfold Rdiv.
        rewrite <- Ropp_mult_distr_l, <- Ropp_mult_distr_r, <- Ropp_inv_permute.
        { rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
          apply Rmult_le_compat_l; try auto.
          apply Rinv_le_contravar.
          - apply Rmult_0_lt_preserving; lra.
          - apply Rmult_le_compat; lra.
        }
        { assert (0 < nR * (nR + err))%R by (apply Rmult_0_lt_preserving; lra); lra. }
    + cut (/nF <= /nR)%R.
      * intros; lra.
      * apply Rinv_le_contravar; try lra.
Qed.

Lemma err_prop_inversion_pos nF nR err (elo ehi:Q)
      (float_iv_pos : (Q2R 0 < Q2R (elo - err))%R)
      (real_iv_pos : (Q2R 0 < Q2R elo)%R)
      (err_bounded : (Rabs (nR - nF) <= Q2R err)%R)
      (valid_bounds_e2 : (Q2R elo <= nR <= Q2R ehi)%R)
      (valid_bounds_e2_err : (Q2R elo - Q2R err <= nF <= Q2R ehi + Q2R err)%R)
      (err_pos : (0 <= Q2R err)%R):
  (Rabs (/nR - / nF) <= Q2R err * / ((Q2R elo- Q2R err) * (Q2R elo- Q2R err)))%R.
Proof.
  eapply err_prop_inversion_pos_real; try rewrite <- Q2R0_is_0; eauto.
  rewrite <- Q2R_minus; auto.
  rewrite Q2R0_is_0; auto.
Qed.

Lemma err_prop_inversion_neg_real nF nR err elo ehi
      (float_iv_neg : (ehi + err < 0)%R)
      (real_iv_neg : (ehi < 0)%R)
      (err_bounded : (Rabs (nR - nF) <= err)%R)
      (valid_bounds_e : (elo <= nR <= ehi)%R)
      (valid_bounds_e_err : (elo - err <= nF <= ehi + err)%R)
      (err_pos : (0 <= err)%R):
  (Rabs (/nR - / nF) <= err * / ((ehi + err) * (ehi + err)))%R.
Proof.
  rewrite Rabs_case_inverted in err_bounded.
  assert (nF < 0)%R as nF_neg by lra.
  destruct err_bounded as [ [diff_pos err_bounded] | [diff_neg err_bounded]].
  - cut (0 < /nF - / nR)%R.
    + intros abs_neg.
      rewrite Rabs_left; try lra.
      rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr, Ropp_involutive.
      rewrite Ropp_inv_permute; try lra.
      apply (Rle_trans _ (/ - nR + / (nR - err))).
      * apply Rplus_le_compat_l.
        assert (0 < - nF)%R by lra.
        assert (0 < - (nR - err))%R by lra.
        assert (nR - err <= nF)%R as nR_lower by lra.
        apply Ropp_le_contravar in nR_lower.
        apply Rinv_le_contravar in nR_lower; try lra.
        repeat (rewrite <- Ropp_inv_permute in nR_lower; try lra).
      * rewrite equal_naming_inv; try lra.
        assert (- nR + (nR - err) = - err)%R as simplify_up by lra.
        rewrite simplify_up.
        unfold Rdiv.
        repeat(rewrite <- Ropp_mult_distr_l); rewrite <- Ropp_inv_permute.
        {
          rewrite <- Ropp_mult_distr_r, Ropp_involutive.
          apply Rmult_le_compat_l; try lra.
          apply Rinv_le_contravar.
          - apply Rmult_lt_0_inverting; lra.
          - eapply Rle_trans.
            eapply Rmult_le_compat_neg_l; try lra.
            instantiate (1 := (nR - err)%R); try lra.
            setoid_rewrite Rmult_comm.
            eapply Rmult_le_compat_neg_l; lra.
        }
        { assert (0 < nR * (nR - err))%R by (apply Rmult_lt_0_inverting; lra); lra. }
    + cut (/ nR < /nF)%R.
      * intros; lra.
      * apply Rinv_lt_contravar; try lra.
        apply Rmult_lt_0_inverting; lra.
  - cut (0 <= /nR - /nF)%R.
    + intros abs_pos.
      rewrite Rabs_right; try lra.
      rewrite Rsub_eq_Ropp_Rplus, Ropp_plus_distr, Ropp_involutive in err_bounded.
      rewrite Rsub_eq_Ropp_Rplus.
      apply (Rle_trans _ (/nR - / (nR + err))).
      * apply Rplus_le_compat_l.
        apply Ropp_le_contravar.
        assert (0 < - nF)%R by lra.
        assert (0 < - (nR + err))%R by lra.
        assert (nF <= nR + err)%R as nR_upper by lra.
        apply Ropp_le_contravar in nR_upper.
        apply Rinv_le_contravar in nR_upper; try lra.
        repeat (rewrite <- Ropp_inv_permute in nR_upper; try lra).
      * rewrite Rsub_eq_Ropp_Rplus, Ropp_inv_permute; try lra.
        rewrite equal_naming_inv; try lra.
        assert (nR + - (nR + err) = - err)%R as simpl_up by lra.
        rewrite simpl_up.
        unfold Rdiv.
        rewrite <- Ropp_mult_distr_l, <- Ropp_mult_distr_r, <- Ropp_inv_permute.
        { rewrite <- Ropp_mult_distr_r. rewrite Ropp_involutive.
          apply Rmult_le_compat_l; try auto.
          apply Rinv_le_contravar.
          - apply Rmult_lt_0_inverting; lra.
          - eapply Rle_trans.
            eapply Rmult_le_compat_neg_l; try lra.
            instantiate (1:= (nR + err)%R); try lra.
            setoid_rewrite Rmult_comm.
            eapply Rmult_le_compat_neg_l; lra.
        }
        { assert (0 < nR * (nR + err))%R by (apply Rmult_lt_0_inverting; lra); lra. }
    + cut (/nF <= /nR)%R.
      * intros; lra.
      * assert (nR <= nF)%R by lra.
        assert (- nF <= - nR)%R as le_inv by lra.
        apply Rinv_le_contravar in le_inv; try lra.
        repeat (rewrite <- Ropp_inv_permute in le_inv; try lra).
Qed.

Lemma err_prop_inversion_neg nF nR err (elo ehi:Q)
      (float_iv_neg : (Q2R (ehi + err) < Q2R 0)%R)
      (real_iv_neg : (Q2R ehi < Q2R 0)%R)
      (err_bounded : (Rabs (nR - nF) <= Q2R err)%R)
      (valid_bounds_e : (Q2R elo <= nR <= Q2R ehi)%R)
      (valid_bounds_e_err : (Q2R elo - Q2R err <= nF <= Q2R ehi + Q2R err)%R)
      (err_pos : (0 <= Q2R err)%R):
  (Rabs (/nR - / nF) <= Q2R err * / ((Q2R ehi + Q2R err) * (Q2R ehi + Q2R err)))%R.
Proof.
  eapply err_prop_inversion_neg_real; try rewrite <- Q2R0_is_0; try lra.
  rewrite <- Q2R_plus ; auto.
  apply valid_bounds_e.
  auto.
Qed.

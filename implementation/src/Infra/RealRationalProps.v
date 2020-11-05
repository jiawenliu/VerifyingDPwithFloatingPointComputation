(**
Some rewriting properties for translating between rationals and real numbers.
These are used in the soundness proofs since we want to have the final theorem on the real valued evaluation.
 **)
From Coq.QArith
     Require Export Qreals.

From Snapv.Infra
     Require Export RationalSimps RealSimps.

Lemma Q2R0_is_0:
  Q2R 0 = 0%R.
Proof.
  unfold Q2R; simpl; lra.
Qed.

Lemma Q2R1:
  (Q2R 1 = 1)%R.
Proof.
  unfold Q2R; simpl; lra.
Qed.

Lemma Rabs_eq_Qabs:
  forall x, Rabs (Q2R x) = Q2R (Qabs x).
Proof.
  intro.
  apply Qabs_case; unfold Rabs; destruct Rcase_abs; intros; try auto.
  - apply Qle_Rle in H. exfalso.
    apply Rle_not_lt in H; apply H.
    assert (Q2R 0 = 0%R) by (unfold Q2R; simpl; lra).
    rewrite H0.
    apply r.
  - unfold Q2R. simpl. rewrite (Ropp_mult_distr_l).
    f_equal. rewrite opp_IZR; auto.
  - apply Qle_Rle in H. hnf in r; hnf in H. destruct r, H.
    + exfalso. apply Rlt_not_ge in H. apply H; hnf.
      left; rewrite Q2R0_is_0; auto.
    + rewrite H in H0.
      apply Rgt_not_le in H0.
      exfalso; apply H0.
      rewrite Q2R0_is_0.
      hnf; right; auto.
    + rewrite H0 in H. rewrite Q2R0_is_0 in H.
      apply Rlt_not_ge in H; exfalso; apply H.
      hnf; right; auto.
    + unfold Q2R in *; simpl in *.
      rewrite opp_IZR; lra.
Qed.

Lemma Q2R_max (a:Q) (b:Q) :
  Rmax (Q2R a) (Q2R b) = Q2R (Qmax a b).
Proof.
  destruct (Qlt_le_dec a b).
  -  pose proof (Qlt_Rlt _ _ q) as Rlt_H.
     rewrite Rmax_right; try lra.
     f_equal. unfold Qmax. unfold GenericMinMax.gmax.
     rewrite Qlt_alt in *.
     rewrite q; auto.
  - pose proof (Qle_Rle _ _ q) as Rle_H.
    hnf in Rle_H.
    destruct Rle_H.
    + rewrite Rmax_left; try lra.
      apply Rlt_Qlt in H.
      f_equal; unfold Qmax. unfold GenericMinMax.gmax.
      rewrite Qgt_alt in *.
      rewrite H; auto.
    + rewrite Rmax_left; try lra.
      f_equal.
      unfold Qmax, GenericMinMax.gmax.
      apply eqR_Qeq in H.
      symmetry in H.
      rewrite Qeq_alt in H. rewrite H; auto.
Qed.

Lemma Q2R_min (a:Q) (b:Q) :
    Rmin (Q2R a) (Q2R b) = Q2R (Qmin a b).
Proof.
  destruct (Qlt_le_dec a b).
  -  pose proof (Qlt_Rlt _ _ q) as Rlt_H.
     rewrite Rmin_left; try lra.
     f_equal. unfold Qmin. unfold GenericMinMax.gmin.
     rewrite Qlt_alt in *.
     rewrite q; auto.
  - pose proof (Qle_Rle _ _ q) as Rle_H.
    hnf in Rle_H.
    destruct Rle_H.
    + rewrite Rmin_right; try lra.
      apply Rlt_Qlt in H.
      f_equal; unfold Qmin. unfold GenericMinMax.gmin.
      rewrite Qgt_alt in *.
      rewrite H; auto.
    + rewrite Rmin_left; try lra.
      f_equal.
      unfold Qmin, GenericMinMax.gmin.
      apply eqR_Qeq in H.
      symmetry in H.
      rewrite Qeq_alt in H. rewrite H; auto.
Qed.

Lemma maxAbs_impl_RmaxAbs (ivlo:Q) (ivhi:Q):
  RmaxAbsFun (Q2R ivlo, Q2R ivhi) = Q2R (maxAbs (ivlo, ivhi)).
Proof.
  unfold RmaxAbsFun, maxAbs.
  simpl; repeat rewrite Rabs_eq_Qabs.
  rewrite Q2R_max; auto.
Qed.

Definition Q2RP (iv:Q*Q) :=
  let (lo,hi) := iv in (Q2R lo, Q2R hi).

Corollary maxAbs_impl_RmaxAbs_iv iv:
  RmaxAbsFun (Q2RP iv) = Q2R (maxAbs iv).
Proof.
  unfold Q2RP; destruct iv; apply maxAbs_impl_RmaxAbs.
Qed.

Lemma minAbs_impl_RminAbs (ivlo ivhi:Q) :
  RminAbsFun (Q2R ivlo, Q2R ivhi) = Q2R (minAbs (ivlo, ivhi)).
Proof.
  unfold RminAbsFun, minAbs; simpl.
  repeat rewrite Rabs_eq_Qabs.
  rewrite Q2R_min; auto.
Qed.

Corollary minAbs_impl_RminAbs_iv iv:
  RminAbsFun (Q2RP iv) = Q2R (minAbs iv).
Proof.
  unfold Q2RP; destruct iv; apply minAbs_impl_RminAbs.
Qed.

Lemma Q_case_div_to_R_case_div a b:
  (b < 0 \/ 0 < a)%Q ->
  (Q2R b < 0 \/ 0 < Q2R a)%R.
Proof.
  intros [le | gr]; [left | right]; rewrite <- Q2R0_is_0; apply Qlt_Rlt; auto.
Qed.

Lemma Rabs_0_equiv:
  (Rbasic_fun.Rabs 0 <= Q2R 0)%R.
Proof.
  rewrite Q2R0_is_0, Rbasic_fun.Rabs_R0; lra.
Qed.

Lemma bounded_inAbs a b c:
  (a <= b <= c -> (Rabs b <= Rabs c) \/ Rabs b <= Rabs a)%R.
Proof.
  intros.
  unfold Rabs.
  destruct (Rcase_abs b); destruct (Rcase_abs c); destruct (Rcase_abs a);
    lra.
Qed.
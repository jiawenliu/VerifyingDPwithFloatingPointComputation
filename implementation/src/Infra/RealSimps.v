(**
  Some simplification properties of real numbers, not proven in the Standard Library
**)

From Coq
     Require Import Setoids.Setoid.

From Coq
     Require Export Reals.Reals micromega.Psatz.

(** Define the maxAbs function on R and prove some minor properties of it.
TODO: Make use of IVLO and IVhi
 **)
Definition RmaxAbsFun (iv:R * R) :=
  Rmax (Rabs (fst iv)) (Rabs (snd iv)).

Definition RminAbsFun (iv: R * R) :=
  Rmin (Rabs (fst iv)) (Rabs (snd iv)).

Lemma Rsub_eq_Ropp_Rplus (a:R) (b:R) :
  (a - b = a + (- b))%R.
Proof.
  field_simplify; reflexivity.
Qed.

Lemma Rabs_simplify (a b: R) :
  (Rabs a <= b <-> ((a <= 0) /\ a >= - b) \/ (a >= 0 /\ a <= b))%R.
Proof.
  split.
  - intros abs.
    unfold Rabs in abs.
    destruct Rcase_abs in abs; lra.
  - intros cases_abs.
    unfold Rabs.
    destruct Rcase_abs; lra.
Qed.

Lemma bound_flip_sub:
  forall a b e,
    (Rabs (a - b) <= e ->
     Rabs ( - a - (- b)) <= e)%R.
Proof.
  intros a b e abs_less.
  rewrite Rsub_eq_Ropp_Rplus.
  rewrite <- Ropp_plus_distr.
  rewrite Rabs_Ropp.
  rewrite <- Rsub_eq_Ropp_Rplus; auto.
Qed.

Lemma plus_bounds_simplify:
  forall a b c d e, (a + b + ( c + d + e) = (a + c) + (b + d) + e)%R.
Proof.
  intros.
  repeat rewrite <- Rplus_assoc.
  setoid_rewrite Rplus_comm at 4.
  setoid_rewrite Rplus_assoc at 3.
  setoid_rewrite Rplus_comm at 3; auto.
Qed.

Lemma Rabs_err_simpl:
  forall a b,
    (Rabs (a - (a * (1 + b))) = Rabs (a * b))%R.
Proof.
  intros a b.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite Rsub_eq_Ropp_Rplus.
  rewrite Ropp_plus_distr.
  assert (- a + (- (a * b)) = ( - (a * b) + - a))%R by (rewrite Rplus_comm; auto).
  rewrite H.
  rewrite <- Rsub_eq_Ropp_Rplus.
  rewrite Rplus_minus.
  rewrite Rabs_Ropp; reflexivity.
Qed.

(**
  Prove that using eps = 0 makes the evaluation deterministic
 **)
Lemma Rabs_0_impl_eq (d:R):
  Rle (Rabs d) 0 -> d = 0%R.
Proof.
  intros abs_leq_0.
  pose proof (Rabs_pos d) as abs_geq_0.
  pose proof (Rle_antisym (Rabs d) 0%R abs_leq_0 abs_geq_0) as Rabs_eq.
  rewrite <- Rabs_R0 in Rabs_eq.
  apply Rsqr_eq_asb_1 in Rabs_eq.
  rewrite Rsqr_0 in Rabs_eq.
  apply Rsqr_0_uniq in Rabs_eq; assumption.
Qed.

Lemma Rabs_bounded (x y: R):
  (-1 <= x <= 1)%R ->
  (Rabs(x*y) <= Rabs y)%R.
Proof.
  intros.
  rewrite Rabs_mult.
  assert (Rabs y = 1 * Rabs y)%R as tmp by lra; rewrite tmp at 2; clear tmp.
  eapply Rmult_le_compat_r; eauto using Rabs_pos, Rabs_le.
Qed.

Lemma RmaxAbs_peel_Rabs a b:
  Rmax (Rabs a) (Rabs b) = Rabs (Rmax (Rabs a) (Rabs b)).
Proof.
  apply Rmax_case_strong; intros; rewrite Rabs_Rabsolu; auto.
Qed.

Lemma equal_naming a b c d:
  (b = 0 -> False)%R ->
  (d = 0 -> False)%R ->
  (a / b + c / d = (a * d + c * b) / (b * d))%R.
Proof.
  intros b_neq_zero d_neq_zero.
  rewrite Rdiv_plus_distr.
  unfold Rdiv.
  repeat (rewrite Rinv_mult_distr; try auto).
  setoid_rewrite (Rmult_comm (/b) (/d)) at 1.
  repeat rewrite <- Rmult_assoc.
  repeat (rewrite Rinv_r_simpl_l; try auto).
Qed.

Lemma inv_eq_1_div a:
  (/ a = 1 / a)%R.
Proof.
  lra.
Qed.

Lemma equal_naming_inv a b:
  (a = 0 -> False)%R ->
  (b = 0 -> False)%R ->
  (/ a + / b = (a + b) / (a * b))%R.
Proof.
  repeat rewrite inv_eq_1_div.
  intros; rewrite equal_naming; auto.
  lra.
Qed.

Lemma Rmult_0_lt_preserving a b:
  (0 < a)%R ->
  (0 < b)%R ->
  (0 < a * b)%R.
Proof.
  intros; rewrite <- (Rmult_0_l 0); apply Rmult_le_0_lt_compat; lra.
Qed.

Lemma Rmult_lt_0_inverting a b:
  (a < 0)%R ->
  (b < 0)%R ->
  (0 < a * b)%R.
Proof.
  intros.
  rewrite <- (Ropp_involutive (a * b)).
  rewrite Ropp_mult_distr_r, Ropp_mult_distr_l.
  rewrite <- (Rmult_0_l 0).
  apply Rmult_le_0_lt_compat; lra.
Qed.

Lemma Rabs_case_inverted a b c:
  (Rabs (a - b) <= c)%R <-> ((a - b > 0 /\ a - b <= c) \/ ( a - b <= 0 /\ - (a - b) <= c))%R.
Proof.
  split.
  - intros rabs_leq.
    unfold Rabs in *; destruct Rcase_abs in rabs_leq; lra.
  - intros [ abs_hi | abs_lo]; unfold Rabs; destruct Rcase_abs; try lra.
Qed.

Lemma lt_or_gt_neq_zero_hi a b:
  (b < 0 \/ 0 < a)%R ->
  (a <= b)%R ->
  (b = 0)%R -> False.
Proof.
  intros neq_zero a_leq_b b_zero.
  destruct neq_zero; subst; lra.
Qed.

Lemma lt_or_gt_neq_zero_lo a b:
  (b < 0 \/ 0 < a)%R ->
  (a <= b)%R ->
  (a = 0)%R -> False.
Proof.
  intros neq_zero a_leq_b a_zero.
  destruct neq_zero; subst; lra.
Qed.

Open Scope R.

Lemma Rle_trans2 a b x y z :
  a <= x -> z <= b -> x <= y <= z -> a <= y <= b.
Proof. lra. Qed.

Lemma Req_dec_sum (x y: R):
  {x = y} + {x <> y}.
Proof.
  pose proof (Rle_dec x y) as H.
  destruct H.
  - destruct (Rge_dec x y).
    + left; lra.
    + right; lra.
  - right; lra.
Qed.

Lemma Req_trans (x y z: R):
  x = y -> y = z -> x = z.
Proof.
  now intros A B; rewrite A, B.
Qed.

Lemma Rabs_Rle_condition x y:
  Rabs x <= y <-> -y <= x <= y.
Proof.
  split; try apply Rabs_le.
  destruct (Req_dec x 0) as [H | H].
  - rewrite H, Rabs_R0.
    lra.
  - destruct (Rle_dec x 0) as [H' | H'].
    + rewrite Rabs_left; lra.
    + rewrite Rabs_pos_eq; lra.
Qed.

Lemma Rdiv_le_ubounds x y z:
  0 < y -> (x / y <= z <-> x <= z * y).
Proof.
  intros A.
  split; intros H.
  * unfold Rdiv in H.
    eapply Rmult_le_reg_r; try apply (Rinv_0_lt_compat _ A).
    rewrite Rinv_r_simpl_l; lra.
  * eapply Rmult_le_reg_r; try exact A.
    replace (x / y * y) with (x * y / y) by lra.
    unfold Rdiv.
    rewrite Rinv_r_simpl_l; lra.
Qed.

Lemma Rdiv_le_lbounds x y z:
  y > 0 -> (-z <= x / y <-> -(z * y) <= x).
Proof.
  intros A.
  split.
  * intros H.
    apply Ropp_le_contravar in H.
    rewrite Ropp_involutive in H.
    replace (- (x / y)) with ((-x) / y) in H by lra.
    rewrite (Rdiv_le_ubounds _ _ _ A) in H; lra.
  * intros H.
    apply Ropp_le_contravar in H.
    rewrite Ropp_involutive in H.
    rewrite <- Rdiv_le_ubounds in H; lra.
Qed.

Lemma Rdiv_le_bounds x y z:
  y > 0 -> ((-z <= x / y <= z) <-> (-(z * y) <= x <= z * y)).
Proof.
  intros H; split; split; destruct H0; try (now apply Rdiv_le_lbounds); now apply Rdiv_le_ubounds.
Qed.

Lemma Rdiv_abs_le_bounds x y z:
  y > 0 -> Rabs (x / y) <= z <-> Rabs x <= z * y.
Proof.
  repeat rewrite Rabs_Rle_condition; apply Rdiv_le_bounds.
Qed.

Lemma Rmult_nonneg x y :
  x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros xpos ypos.
  replace 0 with (0 * y) by lra.
  now apply Rmult_gt_compat_r.
Qed.

Lemma Rdiv_pos x y:
  x > 0 -> y > 0 -> x / y > 0.
Proof.
  intros xpos ypos.
  unfold Rdiv.
  apply Rinv_0_lt_compat in ypos.
  apply Rmult_nonneg; lra.
Qed.

Lemma Rpos_1_div_pos x:
  x > 0 -> 1 / x > 0.
Proof.
  apply Rdiv_pos; lra.
Qed.

Lemma Rlt_inverse_lt x y:
  x > 0 -> y > 0 -> x > y -> 1/y > 1/x.
Proof.
  intros xpos ypos rel.
  apply Rlt_gt.
  eapply Rmult_lt_reg_r.
  apply xpos.
  eapply Rmult_lt_reg_r.
  apply ypos.
  repeat rewrite <- inv_eq_1_div.
  rewrite Rinv_l; try lra.
  replace (/ y * x * y) with (/ y * y * x) by lra.
  rewrite Rinv_l; try lra.
Qed.

Lemma Rmult_piecewise_le x y u v:
  x > 0 -> u > 0 -> x <= y -> u <= v -> x * u <= y * v.
Proof.
  intros A B C D.
  apply Rle_trans with (r2 := x * v); try apply Rmult_le_compat_l;
    try apply Rmult_le_compat_r; try lra.
Qed.

Lemma Rle_minus_iff x y:
  x <= y <-> 0 <= y + - x.
Proof.
  lra.
Qed.

Lemma Rminus_le_iff x y:
  x <= y <-> x + - y <= 0.
Proof.
  lra.
Qed.

Lemma Rmult_neg_nonneg x y:
  x < 0 -> y < 0 -> x * y > 0.
Proof.
  intros xneg yneg.
  replace (x * y) with ((-x)*(-y)) by lra.
  assert (-x > 0) by lra.
  assert (-y > 0) by lra.
  apply Rmult_nonneg; assumption.
Qed.

Lemma Rsquare_nonneg x: 
  0 <= x * x.
Proof.
  replace (x * x) with (x ^ 2) by lra.
  apply pow2_ge_0.
Qed.

Close Scope R.

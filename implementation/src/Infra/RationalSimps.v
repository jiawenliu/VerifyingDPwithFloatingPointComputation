(**
  Some simplification properties of rationals, not proven in the Standard Library
 **)
From Coq.QArith
     Require Export QArith Qminmax Qabs Qround.
From Coq
     Require Export micromega.Psatz.

Definition Qleb := Qle_bool.
Definition Qeqb := Qeq_bool.

Definition maxAbs (iv:Q*Q) :=
  Qmax (Qabs (fst iv)) (Qabs (snd iv)).

Definition minAbs (iv:Q*Q) :=
  Qmin (Qabs (fst iv)) (Qabs (snd iv)).

Lemma maxAbs_pointIntv a:
  maxAbs (a,a) == Qabs a.
Proof.
  unfold maxAbs; simpl.
  apply Qabs_case; intros; eapply Q.max_id.
Qed.

Lemma Qsub_eq_Qopp_Qplus (a:Q) (b:Q) :
  (a - b = a + (- b))%Q.
Proof.
  field_simplify; reflexivity.
Qed.

(* Based on stdlib proof of reals *)
Lemma Qmult_le_compat_neg_l (r r1 r2:Q) :
  r <= 0 -> r1 <= r2 -> r * r2 <= r * r1.
Proof.
  intros.  rewrite <- (Qopp_involutive r).
  apply Qopp_le_compat in H.
  assert (-0 == 0) by field.
  rewrite H1 in H.
  assert (forall a b, - a*b == - (a * b)) by (intros; field).
  setoid_rewrite H2 at 1 2.
  apply Qopp_le_compat.
  setoid_rewrite Qmult_comm at 1 2.
  apply Qmult_le_compat_r; auto.
Qed.

Lemma le_neq_bool_to_lt_prop a b:
  (Qleb a 0 && negb (Qeq_bool a 0) || Qleb 0 b && negb (Qeq_bool b 0)) = true ->
  a < 0 \/ 0 < b.
Proof.
  intros le_neq_bool.
  apply Is_true_eq_left in le_neq_bool.
  apply orb_prop_elim in le_neq_bool.
  destruct le_neq_bool as [lt_0 | lt_0];
    apply andb_prop_elim in lt_0; destruct lt_0 as [le_0 neq_0];
      apply Is_true_eq_true in le_0; apply Is_true_eq_true in neq_0;
        apply negb_true_iff in neq_0; apply Qeq_bool_neq in neq_0;
          rewrite Qle_bool_iff in le_0;
          rewrite Qle_lteq in le_0; destruct le_0 as [lt_0 | eq_0];
            [ | exfalso; apply neq_0; auto | | exfalso; apply neq_0; symmetry; auto]; auto.
Qed.

Lemma equal_naming a b c d:
  (a#b) + (c#d) = (a*Zpos d + c * Zpos b)#(b*d).
Proof.
  unfold Qplus, Qeq; auto.
Qed.

Lemma Qeq_bool_sym a b:
  Qeq_bool a b = Qeq_bool b a.
Proof.
  unfold Qeq_bool.
  case_eq (Zeq_bool (Qnum a * (Zpos (Qden b))) (Qnum b * (Zpos (Qden a)))); intros.
  - rewrite <- Zeq_is_eq_bool in H.
    rewrite H; symmetry.
    rewrite <- Zeq_is_eq_bool; auto.
  - apply Zeq_bool_neq in H.
    case_eq (Zeq_bool (Qnum b * Zpos (Qden a)) (Qnum a * Zpos (Qden b))); intros.
    + apply Zeq_is_eq_bool in H0.
      rewrite H0 in H; auto.
    + auto.
Qed.

Lemma Qeq_bool_refl v:
  (Qeq_bool v v = true).
Proof.
  apply Qeq_bool_iff; lra.
Qed.

Definition Qlt_bool (x y: Q) :=
  (Qle_bool x y) && (negb (Qeq_bool x y)).

Lemma Qlt_bool_iff x y:
  Qlt_bool x y = true <-> x < y.
Proof.
  split; intros A.
  - unfold Qlt_bool in A.
    apply andb_prop in A; destruct A.
    apply Qle_bool_iff in H.
    apply Qle_lt_or_eq in H.
    destruct H; try assumption.
    rewrite H in H0.
    pose proof (Qeq_refl y).
    apply Qeq_bool_iff in H1.
    rewrite H1 in H0.
    now trivial.
  - unfold Qlt_bool.
    apply andb_true_intro.
    split.
    + apply Qlt_le_weak in A.
      now apply Qle_bool_iff.
    + assert (negb false = true) by auto.
      rewrite <- H.
      clear H.
      f_equal.
      apply Qlt_not_eq in A.
      rewrite <- Qeq_bool_iff in A.
      destruct (Qeq_bool); congruence.
Qed.

Lemma Qabs_nonzero_positive (q: Q):
  ~ q == 0 -> (Qabs q) > 0.
Proof.
  intros qnzero.
  apply Qabs_case; lra.
Qed.

Theorem Qmult_div_l : forall x y, ~ y == 0 -> (x/y)*y == x.
  intros.
  rewrite Qmult_comm.
  apply Qmult_div_r; auto.
Qed.

Lemma Qdiv_le_ubounds x y z:
  y > 0 -> (x / y <= z <-> x <= z * y).
Proof.
  intros A.
  split.
  * intros H.
    unfold Qdiv in H.
    apply Qinv_lt_0_compat in A.
    epose proof (Qle_shift_div_l _ _ _ A H).
    unfold Qdiv in H0.
    rewrite Qinv_involutive in H0.
    assumption.
  * intros H.
    apply Qle_shift_div_r; lra.
Qed.

Lemma Qdiv_le_lbounds x y z:
  y > 0 -> (-z <= x / y <-> -(z * y) <= x).
Proof.
  intros A.
  split.
  * intros H.
    apply Qopp_le_compat in H.
    rewrite Qopp_opp in H.
    assert (- (x / y) == (-x) / y) as tmp by (field; try lra); rewrite tmp in H; clear tmp.
    rewrite (Qdiv_le_ubounds _ _ _ A) in H.
    lra.
  * intros H.
    apply Qle_shift_div_l; lra.
Qed.

Lemma Qdiv_le_bounds x y z:
  y > 0 -> ((-z <= x / y <= z) <-> (-(z * y) <= x <= z * y)).
Proof.
  intros H; split; split; destruct H0; try (now apply Qdiv_le_lbounds); now apply Qdiv_le_ubounds.
Qed.

Lemma Qdiv_abs_le_bounds x y z:
  y > 0 -> Qabs (x / y) <= z <-> Qabs x <= z * y.
Proof.
  repeat rewrite Qabs_Qle_condition; apply Qdiv_le_bounds.
Qed.

Lemma Qmult_le_compat_l: forall x y z: Q, x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros.
  rewrite Qmult_comm.
  assert (z * y == y * z) as tmp by lra; rewrite tmp; clear tmp.
  apply Qmult_le_compat_r; auto.
Qed.

Lemma Qmult_nonneg x y :
  x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros xpos ypos.
  assert (0 == 0 * y) as tmp by lra; rewrite tmp; clear tmp.
  now apply Qmult_lt_r.
Qed.

Lemma Qdiv_pos x y:
  x > 0 -> y > 0 -> x / y > 0.
Proof.
  intros xpos ypos.
  apply Qlt_shift_div_l; lra.
Qed.

Lemma Qpos_1_div_pos x:
  x > 0 -> 1 / x > 0.
Proof.
  apply Qdiv_pos; lra.
Qed.

Lemma Qlt_inverse_lt x y:
  x > 0 -> y > 0 -> x > y -> 1/y > 1/x.
Proof.
  intros xpos ypos rel.
  apply (Qlt_shift_div_l (1/x) 1 _ ypos).
  field_simplify; try lra.
  apply (Qlt_shift_div_r y x 1 xpos).
  rewrite Qmult_1_l; assumption.
Qed.

Lemma Qmult_piecewise_le x y u v:
  x > 0 -> u > 0 -> x <= y -> u <= v -> x * u <= y * v.
Proof.
  intros A B C D.
  apply Qle_trans with (y := x * v); try apply Qmult_le_l; try apply Qmult_le_r; try lra.
Qed.

Lemma Qminus_le_iff x y:
  x <= y <-> x + - y <= 0.
Proof.
  lra.
Qed.

Lemma Qmult_neg_nonneg x y:
  x < 0 -> y < 0 -> x * y > 0.
Proof.
  intros xneg yneg.
  assert (x * y == (-x)*(-y)) as tmp by lra; rewrite tmp; clear tmp.
  assert (-x > 0) by lra.
  assert (-y > 0) by lra.
  apply Qmult_nonneg; assumption.
Qed.

Lemma Qsquare_nonneg x: 
  0 <= x * x.
Proof.
  unfold Qmult.
  unfold Qle.
  simpl.
  pose proof (Z.square_nonneg (Qnum x)).
  lia.
Qed.

Lemma Qabs_0_impl_eq (d:Q):
  Qabs d <= 0 -> d == 0.
Proof.
  intros abs_leq_0.
  rewrite Qabs_Qle_condition in abs_leq_0.
  lra.
Qed.

Lemma Qabs_bounded (x y: Q):
  -(1) <= x <= 1 ->
  Qabs(x*y) <= Qabs y.
Proof.
  intros.
  rewrite Qabs_Qmult.
  assert (Qabs y == 1 * Qabs y) as tmp by lra; rewrite tmp at 2; clear tmp.
  eapply Qmult_le_compat_r.
  - apply Qabs_Qle_condition; auto.
  - apply Qabs_nonneg.
Qed.

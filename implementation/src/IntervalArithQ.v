(**
  Formalization of rational valued interval arithmetic
  Used in soundness proofs and computations of range validator.
**)
Require Import Coq.QArith.QArith Coq.QArith.Qminmax Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Snapv.Infra.Abbrevs Snapv.Infra.RationalSimps.

(**
  Define validity of an intv, requiring that the lower bound is less than or equal to the upper bound.
  Containement is defined such that if x is contained in the intv, it must lie between the lower and upper bound.
**)
Definition valid (iv:intv) :Prop :=
  (ivlo iv <= ivhi iv)%Q.

Definition contained (x:Q) (iv:intv) :=
  (ivlo iv <= x <= ivhi iv)%Q.

Lemma contained_implies_valid (x:Q) (iv:intv) :
  contained x iv ->
  valid iv.
Proof.
  unfold contained, valid; intros inIv; apply (Qle_trans _ x _); destruct inIv; auto.
Qed.

(**
  Subset definition; when an intv is a subintv of another
**)
Definition isSupersetIntv (iv1:intv) (iv2:intv) :=
  andb (Qleb (ivlo iv2) (ivlo iv1)) (Qleb (ivhi iv1) (ivhi iv2)).

Definition pointIntv (x:Q) := mkIntv x x.

Lemma contained_implies_subset (x:Q) (iv:intv):
  contained x iv ->
  isSupersetIntv (pointIntv x) iv = true.
Proof.
  intros containedIv.
  unfold contained, isSupersetIntv, pointIntv in *; destruct containedIv.
  apply Is_true_eq_true. apply andb_prop_intro.
  split.
  - apply Qle_bool_iff in H.
    unfold Qleb; simpl in *.
    rewrite H; unfold Is_true; auto.
  - apply Qle_bool_iff in H0.
    unfold Qleb; simpl in *.
    rewrite H0. unfold Is_true; auto.
Qed.

Definition isEqIntv (iv1:intv) (iv2:intv) :=
  (ivlo iv1 == ivlo iv2) /\ (ivhi iv1 == ivhi iv2).

Lemma isEqIntv_refl iv:
  isEqIntv iv iv.
Proof.
  now trivial.
Qed.

Lemma isEqIntv_sym iv1 iv2:
  isEqIntv iv1 iv2 -> isEqIntv iv2 iv1.
Proof.
  unfold isEqIntv; lra.
Qed.

Lemma isEqIntv_trans iv1 iv2 iv3:
  isEqIntv iv1 iv2 -> isEqIntv iv2 iv3 -> isEqIntv iv1 iv3.
Proof.
  unfold isEqIntv; lra.
Qed.

Instance isEqIntv_Equivalence : Equivalence isEqIntv.
Proof.
  constructor; eauto using isEqIntv_refl, isEqIntv_sym, isEqIntv_trans.
Qed.

Lemma supIntvAntisym (iv1:intv) (iv2:intv) :
  isSupersetIntv iv1 iv2 = true ->
  isSupersetIntv iv2 iv1 = true ->
  isEqIntv iv1 iv2.
Proof.
  intros incl12 incl21.
  unfold isSupersetIntv in *.
  apply andb_true_iff in incl12.
  apply andb_true_iff in incl21.
  destruct incl12 as [incl12_low incl12_hi].
  destruct incl21 as [incl21_low incl21_hi].
  apply Qle_bool_iff in incl12_low.
  apply Qle_bool_iff in incl12_hi.
  apply Qle_bool_iff in incl21_low.
  apply Qle_bool_iff in incl21_hi.
  split.
  - apply (Qle_antisym (ivlo iv1) (ivlo iv2)); auto.
  - apply (Qle_antisym (ivhi iv1) (ivhi iv2)); auto.
Qed.

Definition unionIntv (iv1 iv2: intv) := mkIntv (Qmin (ivlo iv1) (ivlo iv2)) (Qmax (ivhi iv1) (ivhi iv2)).

Lemma subset_union_left iv1 iv2 : isSupersetIntv iv1 (unionIntv iv1 iv2) = true.
Proof.
  destruct iv1, iv2. unfold unionIntv, isSupersetIntv; cbn.
  apply Is_true_eq_true. apply andb_prop_intro. split.
  - apply Is_true_eq_left. apply Qle_bool_iff. apply Q.le_min_l.
  - apply Is_true_eq_left. apply Qle_bool_iff. apply Q.le_max_l.
Qed.

Lemma subset_union_right iv1 iv2 : isSupersetIntv iv2 (unionIntv iv1 iv2) = true.
Proof.
  destruct iv1, iv2. unfold unionIntv, isSupersetIntv; cbn.
  apply Is_true_eq_true. apply andb_prop_intro. split.
  - apply Is_true_eq_left. apply Qle_bool_iff. apply Q.le_min_r.
  - apply Is_true_eq_left. apply Qle_bool_iff. apply Q.le_max_r.
Qed.

(**
  Definition of validity conditions for intv operations, Addition, Subtraction, Multiplication and Division
 **)
Definition validIntvAdd (iv1:intv) (iv2:intv) (iv3:intv) :=
  forall a b, contained a iv1 -> contained b iv2 ->
         contained (a + b) iv3.

Definition validIntvSub (iv1:intv) (iv2:intv) (iv3:intv) :=
  forall a b, contained a iv1 -> contained b iv2 ->
         contained (a - b) iv3.

Definition validIntvMult (iv1:intv) (iv2:intv) (iv3:intv) :=
  forall a b, contained a iv1 -> contained b iv2 ->
         contained (a * b) iv3.

Definition validIntvDiv (iv1:intv) (iv2:intv) (iv3:intv) :=
  forall a b, contained a iv1 -> contained b iv2 ->
         contained (a / b) iv3.

Lemma validPointIntv (a:Q) :
  contained a (pointIntv a).
Proof.
  unfold contained; split; simpl; apply Qle_refl; auto.
Qed.

(**
  Now comes the old part with the computational definitions.
  Where possible within time, they are shown sound with respect to the definitions from before, where not, we leave this as proof obligation for Snapv.
 **)

(**
  TODO: Refactor into a list manipulating function instead
**)
Definition min4 (a:Q) (b:Q) (c:Q) (d:Q) := Qmin a (Qmin b (Qmin c d)).
Definition max4 (a:Q) (b:Q) (c:Q) (d:Q) := Qmax a (Qmax b (Qmax c d)).

Ltac Qmin_l := intros; apply Q.min_le_iff; left; apply Qle_refl.
Ltac Qmin_r := intros; apply Q.min_le_iff; right; apply Qle_refl.

Lemma min4_correct (a b c d:Q) :
  (let m := min4 a b c d in
   m <= a /\ m <= b /\ m <= c /\ m <= d)%Q.
Proof.
  intros m.
  repeat split; unfold m, min4.
  - Qmin_l.
  - assert (forall c,  Qmin b c <= b)%Q by Qmin_l.
    apply (Qle_trans _ (Qmin b (Qmin c d)) _); auto.
    Qmin_r.

  - assert (Qmin c d <= c)%Q by Qmin_l.
    assert (Qmin b (Qmin c d) <= c)%Q.
    + apply (Qle_trans _ (Qmin c d) _); auto. Qmin_r.
    + apply (Qle_trans _ (Qmin b (Qmin c d)) _); auto. Qmin_r.
  - assert (Qmin c d <= d)%Q by Qmin_r.
    assert (Qmin b (Qmin c d) <= d)%Q.
    + apply (Qle_trans _ (Qmin c d) _); auto. Qmin_r.
    + apply (Qle_trans _ (Qmin b (Qmin c d)) _); auto. Qmin_r.
Qed.

Ltac Qmax_l := intros; apply Q.max_le_iff; left; apply Qle_refl.
Ltac Qmax_r := intros; apply Q.max_le_iff; right; apply Qle_refl.

Lemma max4_correct (a b c d:Q) :
  (let m := max4 a b c d in
   a <= m /\ b <= m /\ c <= m /\ d <= m)%Q.
Proof.
  intros m.
  repeat split; unfold m, max4.
  - Qmax_l.
  - assert (forall c,  b <= Qmax b c)%Q by Qmax_l.
    apply (Qle_trans _ (Qmax b (Qmax c d)) _); auto.
    Qmax_r.
  - assert (c <= Qmax c d)%Q by Qmax_l.
    assert (c <= Qmax b (Qmax c d))%Q.
    + apply (Qle_trans _ (Qmax c d) _); auto. Qmax_r.
    + apply (Qle_trans _ (Qmax b (Qmax c d)) _); auto. Qmax_r.
  - assert (d <= Qmax c d)%Q by Qmax_r.
    assert (d <= Qmax b (Qmax c d))%Q.
    + apply (Qle_trans _ (Qmax c d) _); auto. Qmax_r.
    + apply (Qle_trans _ (Qmax b (Qmax c d)) _); auto. Qmax_r.
Qed.

(**
 Asbtract intv update function, parametric by actual operator applied.
**)
Definition absIvUpd (op:Q->Q->Q) (I1:intv) (I2:intv) :=
  (
    min4 (op (ivlo I1) (ivlo I2))
         (op (ivlo I1) (ivhi I2))
         (op (ivhi I1) (ivlo I2))
         (op (ivhi I1) (ivhi I2)),
    max4 (op (ivlo I1) (ivlo I2))
         (op (ivlo I1) (ivhi I2))
         (op (ivhi I1) (ivlo I2))
         (op (ivhi I1) (ivhi I2))
  ).

Definition widenIntv (Iv:intv) (v:Q) := mkIntv (ivlo Iv - v) (ivhi Iv + v).

Definition negateIntv (iv:intv) := mkIntv (- ivhi iv) (- ivlo iv).

Lemma intv_negation_valid (iv:intv) (a:Q) :
  contained a iv-> contained (- a) (negateIntv iv).
Proof.
  unfold contained; destruct iv as [ivlo ivhi]; simpl; intros [ivlo_le_a a_le_ivhi].
  split; apply Qopp_le_compat; auto.
Qed.

Definition invertIntv (iv:intv) := mkIntv (/ ivhi iv) (/ ivlo iv).

(*
Lemma zero_not_contained_cases (iv:intv) :
  ivlo iv <= ivhi iv -> ~ contained 0 iv -> ivhi iv < 0 \/ 0 < ivlo iv.
Proof.
  unfold contained; destruct iv as [lo hi]; simpl; intros.
  hnf in H0; rewrite Decidable.not_and_iff in H0.
  case_eq (lo ?= 0); case_eq (hi ?= 0); intros.
  - exfalso.
    rewrite <- Qeq_alt in H1, H2.
    apply H0; [rewrite H2; auto | rewrite H1; auto]; apply Qle_refl.
  - rewrite <- Qlt_alt in H1.
    rewrite <- Qeq_alt in H2.
    rewrite H2 in H.
    exfalso.
    apply Qle_not_lt in H; auto.
  - rewrite <- Qgt_alt in H1.
    rewrite <- Qeq_alt in H2.
 *)
Lemma Qinv_Qopp_compat (a:Q) :
  / - a = - / a.
Proof.
  unfold Qinv.
  case_eq (Qnum a); intros; unfold Qopp; rewrite H; simpl; auto.
Qed.

Lemma intv_inversion_valid (iv:intv) (a:Q) :
  ivhi iv < 0 \/ 0 < ivlo iv -> contained a iv -> contained (/ a) (invertIntv iv).
Proof.
  unfold contained; destruct iv as [ivlo ivhi]; simpl;
    intros [ivhi_lt_zero | zero_lt_ivlo]; intros [ivlo_le_a a_le_ivhi];
      assert (ivlo <= ivhi) by (eapply Qle_trans; eauto);
      split.
  - assert (- / a <= - / ivhi).
    + assert (0 < - ivhi) by lra.
      repeat rewrite <- Qinv_Qopp_compat.
      eapply Qle_shift_inv_l; try auto.
      assert (- ivhi <= - a) by lra.
      apply (Qmult_le_r _ 1 (- a)); try lra.
      rewrite Qmult_1_l.
      setoid_rewrite Qmult_comm at 1.
      rewrite Qmult_assoc.
      rewrite Qmult_inv_r; lra.
    + apply Qopp_le_compat in H0;
        repeat rewrite Qopp_involutive in H0; auto.
  - assert (- / ivlo <= - / a).
    +  repeat rewrite <- Qinv_Qopp_compat.
       eapply Qle_shift_inv_l; try lra.
       apply (Qmult_le_r _ _ (- ivlo)); try lra.
       rewrite Qmult_comm, Qmult_assoc, Qmult_inv_r, Qmult_1_l; lra.
    + apply Qopp_le_compat in H0.
      repeat rewrite Qopp_involutive in H0; auto.
  - apply Qle_shift_inv_l; try lra.
    apply (Qmult_le_r _ _ (ivhi)); try lra.
    rewrite Qmult_comm, Qmult_assoc, Qmult_inv_r, Qmult_1_l; lra.
  - apply Qle_shift_inv_l; try lra.
    apply (Qmult_le_r _ _ a); try lra.
    rewrite Qmult_comm, Qmult_assoc, Qmult_inv_r, Qmult_1_l; lra.
Qed.

Definition addIntv (iv1:intv) (iv2:intv) :=
  absIvUpd Qplus iv1 iv2.

Lemma interval_addition_valid iv1 iv2:
  validIntvAdd iv1 iv2 (addIntv iv1 iv2).
Proof.
  unfold validIntvAdd.
  intros a b.
  unfold contained, addIntv, absIvUpd, min4, max4.
  intros [lo_leq_a a_leq_hi] [lo_leq_b b_leq_hi].
  simpl; split.
  (** Lower Bound **)
  - assert ( fst iv1 + fst iv2 <= a + b)%Q as lower_bound by (apply Qplus_le_compat; auto).
    apply (Qle_trans _ (fst iv1 + fst iv2) _); [Qmin_l | auto].
  (** Upper Bound **)
  - assert (a + b <= snd iv1 + snd iv2)%Q as upper_bound by (apply Qplus_le_compat; auto).
    apply (Qle_trans _ (snd iv1 + snd iv2) _); [ auto | ].
    apply (Qle_trans _ (Qmax (fst iv1 + snd iv2) (Qmax (snd iv1 + fst iv2) (snd iv1 + snd iv2))) _);
      [ | Qmax_r].
    apply (Qle_trans _ (Qmax (snd iv1 + fst iv2) (snd iv1 + snd iv2)) _ ); [ | Qmax_r].
    apply (Qle_trans _ (snd iv1 + snd iv2) _); [ apply Qle_refl; auto | Qmax_r].
Qed.

Definition subtractIntv (I1:intv) (I2:intv) :=
  addIntv I1 (negateIntv I2).

Corollary interval_subtraction_valid iv1 iv2:
  validIntvSub iv1 iv2 (subtractIntv iv1 iv2).
Proof.
  unfold subtractIntv.
  intros a b.
  intros contained_1 contained_I2.
  rewrite Qsub_eq_Qopp_Qplus.
  apply interval_addition_valid; auto.
  apply intv_negation_valid; auto.
Qed.

Definition multIntv (iv1:intv) (iv2:intv) :=
  absIvUpd Qmult iv1 iv2.

(**
  Prove validity of multiplication for the intv lattice.
  Prove is structurally the same as the proof done Jourdan et al. in Verasco, in FloatIntvsForward.v
  TODO: Credit
 **)
Lemma intv_multiplication_valid (I1:intv) (I2:intv) (a:Q) (b:Q) :
  contained a I1 ->
  contained b I2 ->
  contained (a * b) (multIntv I1 I2).
Proof.
  unfold contained, multIntv, absIvUpd, ivlo, ivhi.
  destruct I1 as [ivlo1 ivhi1]; destruct I2 as [ivlo2 ivhi2]; simpl.
  intros [lo_leq_a a_leq_hi] [lo_leq_b b_leq_hi].
  pose proof (min4_correct (ivlo1 * ivlo2) (ivlo1 * ivhi2) (ivhi1 * ivlo2) (ivhi1 * ivhi2))
    as [leq_lolo [leq_lohi [leq_hilo leq_hihi]]];
    pose proof (max4_correct (ivlo1 * ivlo2) (ivlo1 * ivhi2) (ivhi1 * ivlo2) (ivhi1 * ivhi2))
    as [lolo_leq [lohi_leq [hilo_leq hihi_leq]]].
  split.
  (* Lower Bound *)
  - destruct (Qlt_le_dec a 0).
    + apply Qlt_le_weak in q.
      destruct (Qlt_le_dec ivhi2 0).
      * apply Qlt_le_weak in  q0.
        pose proof (Qmult_le_compat_neg_l _ _ _ q b_leq_hi) as ahi2_leq_ab.
        pose proof (Qmult_le_compat_neg_l _ _ _ q0 a_leq_hi) as hihi_leq_ahi2.
        eapply Qle_trans.
        apply leq_hihi. rewrite Qmult_comm.
        eapply Qle_trans. apply hihi_leq_ahi2.
        rewrite Qmult_comm; auto.
      * eapply Qle_trans.
        apply leq_lohi.
        setoid_rewrite Qmult_comm at 1 2.
        pose proof (Qmult_le_compat_r ivlo1 a ivhi2 lo_leq_a q0).
        rewrite Qmult_comm.
        eapply (Qle_trans).
        apply H; auto.
        rewrite Qmult_comm.
        setoid_rewrite Qmult_comm at 1 2.
        eapply (Qmult_le_compat_neg_l); auto.
    + destruct (Qlt_le_dec ivlo2 0).
      * eapply Qle_trans.
        apply leq_hilo.
        rewrite Qmult_comm.
        eapply Qle_trans.
        apply Qlt_le_weak in q0.
        apply (Qmult_le_compat_neg_l _ _ _ q0 a_leq_hi).
        rewrite Qmult_comm.
        setoid_rewrite Qmult_comm at 1 2.
        eapply (Qmult_le_compat_r _ _ a); auto.
      * eapply Qle_trans.
        apply leq_lolo.
        rewrite Qmult_comm.
        apply (Qle_trans _ (ivlo2 * a)).
        setoid_rewrite Qmult_comm at 1 2.
        eapply (Qmult_le_compat_r _ _ ivlo2 ); auto.
        rewrite Qmult_comm.
        setoid_rewrite Qmult_comm at 1 2.
        eapply (Qmult_le_compat_r _ _ a); auto.
  - destruct (Qlt_le_dec a 0).
    + apply Qlt_le_weak in q.
      eapply Qle_trans.
      eapply (Qmult_le_compat_neg_l); eauto.
      destruct (Qlt_le_dec ivlo2 0).
      * rewrite Qmult_comm.
        eapply Qle_trans.
        eapply (Qmult_le_compat_neg_l); eauto.
        apply Qlt_le_weak; auto.
        rewrite Qmult_comm; auto.
      * eapply Qle_trans.
        eapply (Qmult_le_compat_r _ _ ivlo2); auto.
        apply a_leq_hi.
        apply hilo_leq.
    + rewrite Qmult_comm.
      eapply Qle_trans.
      eapply (Qmult_le_compat_r); auto.
      apply b_leq_hi.
      destruct (Qlt_le_dec ivhi2 0).
      * eapply Qle_trans.
        eapply (Qmult_le_compat_neg_l); auto.
        apply Qlt_le_weak; auto.
        apply lo_leq_a.
        rewrite Qmult_comm; auto.
      * eapply Qle_trans.
        rewrite Qmult_comm.
        eapply (Qmult_le_compat_r); auto.
        apply a_leq_hi.
        apply hihi_leq.
Qed.

Definition divideIntv (I1:intv) (I2:intv) :=
  multIntv I1 (mkIntv (/ (ivhi I2)) (/ (ivlo I2))).

Corollary interval_division_valid a b (I1:intv) (I2:intv) :
  ivhi I2 < 0 \/ 0 < ivlo I2 -> contained a I1 -> contained b I2 -> contained (a / b) (divideIntv I1 I2).
Proof.
  intros nodiv0 c_a c_b.
  pose proof (intv_inversion_valid nodiv0 c_b).
  unfold divideIntv, Qdiv.
  apply intv_multiplication_valid; auto.
Qed.

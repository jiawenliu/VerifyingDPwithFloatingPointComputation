(**
  Implementation of machine-precision as a datatype for mixed-precision computations

  @author: Raphael Monat
  @maintainer: Heiko Becker
 **)

From Coq.QArith
     Require Import Qpower.

From Snapv
     Require Import Infra.RealRationalProps Infra.Ltacs.
(**
  Injection of machine types into Q
  To support fixed-point values, we add an additional paramer, v which is the
  value represented, as the error depends on the fraction bits which in turn
  depend on the value represented
   Define machine precision as datatype. We treat Fixed-point types as floats,
   like Flocq, where f:positive specifies the fraction size and w: the width of
   the base field.
 **)

Require Import Omega.

Inductive mType: Type := REAL (* real valued computations *)
                       | M16 | M32 | M64 (* floating-point precisions *)
                       | F (w:positive) (f:N). (* fixed-point precisions *)
Definition isFixedPoint m :Prop :=
  match m with
  |F _ _ => True
  | _ => False
  end.

Definition isFixedPointB m :bool :=
  match m with
  |F _ _ => true
  | _ => false
  end.

Lemma isFixedPoint_isFixedPointB m :
  isFixedPoint m <-> isFixedPointB m = true.
Proof.
  destruct m; unfold isFixedPoint; simpl; split; try congruence; try auto.
Qed.

Lemma isFixedPoint_isFixedPointB_false m:
  (~ isFixedPoint m) <-> isFixedPointB m = false.
Proof.
  destruct m; unfold isFixedPoint; simpl; split; try congruence; try auto.
  intros.
  exfalso; auto.
Qed.

(**
  Compute a machine epsilon from a  machine types in Q
**)
Definition mTypeToR (m:mType) :R :=
  match m with
  | REAL => 0%R
  | M16 => 1 / 2^11
  | M32 => 1/ 2^24
  | M64 => 1/ 2^53
  | F w f => 1/ 2^(N.to_nat f)
  end.

Definition mTypeToQ (m:mType) :Q :=
  match m with
  | REAL => 0
  | M16 => (Qpower (2#1) (Zneg 11))
  | M32 => (Qpower (2#1) (Zneg 24))
  | M64 => (Qpower (2#1) (Zneg 53))
  | F w f => Qpower (2#1) (- Z.of_N f)
  end.

Definition computeErrorR v m :R :=
  match m with
  |REAL => 0
  |F w f => mTypeToR m
  |_ => Rabs v * mTypeToR m
  end.

Definition computeErrorQ v m :Q :=
  match m with
  |REAL => 0
  |F w f => mTypeToQ m
  |_ => Qabs v * mTypeToQ m
  end.

Lemma Pos_pow_1_l p:
  Pos.pow 1 p = 1%positive.
Proof.
  induction p; unfold Pos.pow in *; cbn in *; try auto.
  all: repeat rewrite IHp; auto.
Qed.

Lemma mTypeToQ_mTypeToR m :
  Q2R (mTypeToQ m) = mTypeToR m.
Proof.
  destruct m; cbn; try auto using Q2R0_is_0; try (unfold Q2R; simpl; lra).
  pose proof (Qpower_opp (2#1) (Z.of_N f)) as Qpower_eq.
  apply Qeq_eqR in Qpower_eq.
  rewrite Qpower_eq.
  rewrite Q2R_inv.
  - unfold Rdiv. rewrite Rmult_1_l.
    f_equal.
    destruct (Z.of_N f) eqn:z_nat; try (destruct f; cbn in z_nat; congruence).
    + cbn. destruct f; simpl in *; try congruence.
      lra.
    + unfold Qpower.
      rewrite Qpower_decomp.
      unfold Q2R; simpl.
      rewrite Zpower_pos_powerRZ.
      rewrite pow_powerRZ.
      rewrite N_nat_Z.
      rewrite z_nat.
      assert (IZR (Z.pos (1 ^ p)) = 1%R) as pow_1.
      { unfold IZR.
        f_equal.
        rewrite Pos_pow_1_l; auto. }
      rewrite pow_1.
      rewrite Rinv_1, Rmult_1_r; auto.
  - hnf; intros power_0.
    destruct f; simpl in *; try lra.
    rewrite Qpower_decomp in *.
    unfold Qeq in *; simpl in *.
    pose proof (Zpow_facts.Zpower_pos_pos 2 p) as Zpower_pos.
    assert (0 <2)%Z as pos2 by (omega).
    specialize (Zpower_pos pos2).
    rewrite Z.mul_1_r in *.
    rewrite power_0 in *. inversion Zpower_pos.
Qed.

Arguments mTypeToR _/.
Arguments mTypeToQ _/.

Lemma computeErrorQ_computeErrorR m v:
  Q2R (computeErrorQ v m) = computeErrorR (Q2R v) m.
Proof.
  destruct m; unfold computeErrorQ, computeErrorR; try lra.
  all: try rewrite Q2R_mult; rewrite mTypeToQ_mTypeToR; try auto.
  all: f_equal; try auto.
  all: rewrite Rabs_eq_Qabs; auto.
Qed.

Open Scope R_scope.

Lemma mTypeToR_pos_R m:
  0 <= mTypeToR m.
Proof.
  destruct m; simpl; try lra.
  unfold Rdiv.
  apply Rmult_le_pos; try lra.
  hnf; left; apply Rinv_0_lt_compat.
  apply pow_lt; lra.
Qed.

Lemma computeErrorR_up (v a b:R) m:
  Rabs v <= RmaxAbsFun (a,b) ->
  computeErrorR v m <= computeErrorR (RmaxAbsFun (a,b)) m.
Proof.
  intros.
  unfold computeErrorR; destruct m; try lra.
  all:apply Rmult_le_compat_r; try auto using mTypeToR_pos_R.
  all:unfold RmaxAbsFun in *.
  all:setoid_rewrite Rabs_right at 2; try auto.
  all:apply Rle_ge; rewrite Rmax_Rle; auto using Rabs_pos.
Qed.

Close Scope R_scope.

Lemma mTypeToQ_pos_Q m:
  0 <= mTypeToQ m.
Proof.
  destruct m; simpl; cbn; try lra.
  unfold Qpower.
  destruct f; simpl in *; try lra.
  apply Qinv_le_0_compat.
  apply Qpower_pos_positive.
  lra.
Qed.

Lemma mTypeToQ_pos_R m:
  (0 <= Q2R (mTypeToQ m))%R.
Proof.
  intros *.
  rewrite <- Q2R0_is_0.
  apply Qle_Rle.
  apply mTypeToQ_pos_Q.
Qed.

Definition mTypeEq (m1:mType) (m2:mType) :=
  match m1, m2 with
  | REAL, REAL => true
  | M16, M16 => true
  | M32, M32 => true
  | M64, M64 => true
  | F w1 f1, F w2 f2 => (w1 =? w2)%positive && (f1 =? f2)%N
  | _, _ => false
  end.

Lemma mTypeEq_refl (m:mType):
  mTypeEq m m = true.
Proof.
  intros. destruct m; try auto; simpl.
  rewrite Pos.eqb_refl, N.eqb_refl; auto.
Qed.

Lemma mTypeEq_compat_eq(m1:mType) (m2:mType):
  mTypeEq m1 m2 = true <-> m1 = m2.
Proof.
  split; intros eq_case;
    case_eq m1; intros * m1_case;
      case_eq m2; intros * m2_case; subst;
        try congruence; try auto;
          try simpl in eq_case; try inversion eq_case.
  - andb_to_prop eq_case. f_equal; auto using Peqb_true_eq.
    rewrite <- N.eqb_eq; auto.
  - inversion m2_case. apply mTypeEq_refl.
Qed.

Lemma mTypeEq_compat_eq_false (m1:mType) (m2:mType):
  mTypeEq m1 m2 = false <-> ~(m1 = m2).
Proof.
  split; intros eq_case.
  - hnf; intros; subst. rewrite mTypeEq_refl in eq_case.
    congruence.
  - case_eq m1; intros; case_eq m2; intros; subst; simpl; try congruence.
    destruct (w =? w0)%positive eqn:?; try auto.
    destruct (f =? f0)%N eqn:?; try auto.
    rewrite Pos.eqb_eq, N.eqb_eq in *; subst. congruence.
Qed.

Ltac type_conv :=
  repeat
    (match goal with
     | [H : mTypeEq _ _ = true |- _] => rewrite mTypeEq_compat_eq in H; subst
     | [H : mTypeEq _ _ = false |- _] => rewrite mTypeEq_compat_eq_false in H
     end).

Lemma mTypeEq_sym (m1:mType) (m2:mType):
  mTypeEq m1 m2 = mTypeEq m2 m1.
Proof.
  intros.
  destruct m1, m2; simpl; auto.
  rewrite Pos.eqb_sym; f_equal.
  apply N.eqb_sym.
Qed.

(**
  Check if machine precision m1 is more precise than machine precision m2.
  REAL is real-valued evaluation, hence the most precise.
  All floating-point types are compared by
    mTypeToQ m1 <= mTypeToQ m2
  All fixed-point types are compared by comparing only the word size
  We consider a 32 bit fixed-point number to be more precise than a 16 bit
  fixed-point number, no matter what the fractional bits may be.
  For the moment, fixed-point and floating-point formats are incomparable.
 **)
Definition isMorePrecise (m1:mType) (m2:mType) :=
  match m1, m2 with
  |REAL, _ => true
  | F w1 f1, F w2 f2 => (w2 <=? w1)%positive (*&& (f1 <=? f2)%positive *)
  | F w f, _ => false
  | _ , F w f => false
  | _, _ => Qle_bool (mTypeToQ m1) (mTypeToQ m2)
  end.

(**
   More efficient version for performance, unfortunately we cannot do better
   for fixed-points
**)
Definition morePrecise (m1:mType) (m2:mType) :=
  match m1, m2 with
  | REAL, _ => true
  | F w1 f1, F w2 f2 => (w2 <=? w1)%positive (*&& (f1 <=? f2)%positive*)
  | _ , F w f => false
  | F w f, _ => false
  | M16, M16 => true
  | M32, M32 => true
  | M32, M16 => true
  | M64, REAL => false
  | M64, _ => true
  | _, _ => false
  end.

Lemma morePrecise_refl m:
  morePrecise m m = true.
Proof.
  destruct m; cbn; auto using Pos.leb_refl.
Qed.

Lemma morePrecise_trans m1 m2 m3:
  morePrecise m1 m2 = true ->
  morePrecise m2 m3 = true ->
  morePrecise m1 m3 = true.
Proof.
  destruct m1; destruct m2; destruct m3; simpl; auto;
    intros le1 le2; try congruence.
  apply Pos.leb_le in le1; apply Pos.leb_le in le2.
  apply Pos.leb_le;
    eapply Pos.le_trans; eauto.
Qed.

Lemma isMorePrecise_morePrecise m1 m2:
  isMorePrecise m1 m2 = morePrecise m1 m2.
Proof.
  destruct m1 eqn:?, m2 eqn:?; simpl; auto.
Qed.

Lemma isMorePrecise_refl (m:mType) :
  isMorePrecise m m = true.
Proof.
  unfold isMorePrecise; destruct m; simpl; try auto.
  (* split_bool; *)
  apply Pos.leb_le; apply Pos.le_refl.
Qed.

Lemma REAL_least_precision (m:mType) :
  isMorePrecise m REAL = true -> m = REAL.
Proof.
  intro m_morePrecise.
  unfold isMorePrecise in *.
  destruct m; cbv in m_morePrecise; congruence.
Qed.

Lemma REAL_lower_bound (m:mType) :
  isMorePrecise REAL m = true.
Proof.
  destruct m; unfold isMorePrecise; cbv; auto.
Qed.

(**
  Function computing the join of two precisions, this is the most precise type,
  in which evaluation has to be performed, e.g. addition of 32 and 64 bit floats
  has to happen in 64 bits
**)
Definition join_fl (m1:mType) (m2:mType) :option mType :=
  match m1, m2 with
  |F _ _, F _ _ => None
  | _, _ => if (morePrecise m1 m2) then Some m1 else Some m2
  end.

Definition join_fl3 (m1:mType) (m2:mType) (m3:mType) :=
  olet msub := join_fl m2 m3 in
    join_fl m1 msub.

(** Since we cannot compute a join for Fixed-Points, we give a
    isJoin predicate which returns true for fixed-points, but needs to inspect
    it for floating-points **)
Definition isCompat m1 m2 :bool :=
  match m1, m2 with
  |REAL, REAL => true
  |F _ _, F _ _ => morePrecise m1 m2
  |F _ _, _ => false
  |_, F _ _ => false
  | _ , _ => mTypeEq m1 m2
  end.

Definition isJoin m1 m2 mj :bool :=
  if (isFixedPointB m1 && isFixedPointB m2)
  then morePrecise m1 mj && morePrecise m2 mj
  else
    match join_fl m1 m2 with
    | None => false
    | Some mNew => mTypeEq mNew mj end.

Definition isJoin3 m1 m2 m3 mj :bool :=
  if (isFixedPointB m1 && isFixedPointB m2 && isFixedPointB m3)
  then morePrecise m1 mj && morePrecise m2 mj && morePrecise m3 mj
  else
    match join_fl3 m1 m2 m3 with
    | None => false
    | Some mNew => mTypeEq mNew mj end.

Definition maxExponent (m:mType) :N :=
  match m with
  | REAL => 1
  | M16 => 15
  | M32 => 127
  | M64 => 1023
  | F w f => f
  end.

Definition minExponentPos (m:mType) :N :=
  match m with
  | REAL => 1
  | M16 => 14
  | M32 => 126
  | M64 => 1022
  | F w f => f
  end.

(**
Floating-point types:
  Goldberg - Handbook of Floating-Point Arithmetic: (p.183)
  (𝛃 - 𝛃^(1 - p)) * 𝛃^(e_max)
  which simplifies to 2^(e_max) for base 2

Fixed-Points:
  it is maximum possible representable integer for the given bits w
  times the maximum possible exponent (f)
**)
Definition maxValue (m:mType) :=
  match m with
  |F w f => (((Z.pow_pos 2 (w -1))-1)#1) * Qinv ((Z.pow 2 (Z.of_N (maxExponent m)))#1)
  |_ => (Z.pow 2 (Z.of_N (maxExponent m))) # 1
  end.

(* Similarly: minimum values: we return 0 for fixed-point numbers here to make no fixed-point number be a denormal number ever*)
Definition minValue_pos (m:mType) :=
  match m with
  |F w f => 0
  | _ => Qinv ((Z.pow 2 (Z.of_N (minExponentPos m))) # 1)
  end.

(* (** Goldberg - Handbook of Floating-Point Arithmetic: (p.183) *)
(*   𝛃^(e_min -p + 1) = 𝛃^(e_min -1) for base 2 *)
(* **) *)
(* Definition minDenormalValue (m:mType) := *)
(*   Qinv (Z.pow_pos 2 (minExponentPos m - 1) # 1). *)

Definition normal (v:Q) (m:mType) :=
  Qle_bool (minValue_pos m) (Qabs v) && Qle_bool (Qabs v) (maxValue m).

Definition denormal (v:Q) (m:mType) :=
  Qle_bool (Qabs v) (minValue_pos m) && negb (Qeq_bool v 0).

Definition Normal (v:R) (m:mType) :=
  (Q2R (minValue_pos m) <= (Rabs v) /\ (Rabs v) <= Q2R (maxValue m))%R.

Definition Denormal (v:R) (m:mType) :=
  ((Rabs v) < Q2R (minValue_pos m) /\ ~ (v = 0))%R.
(**
  Predicate that is true if and only if the given value v is a valid
  floating-point value according to the the type m.
  Since we use the 1 + 𝝳 abstraction, the value must either be
  in normal range or 0.
**)
Definition validFloatValue (v:R) (m:mType) :=
  match m with
  | REAL => True
  | _ => Normal v m \/ Denormal v m \/ v = 0%R
  end.

Definition validValue (v:Q) (m:mType) :=
  match m with
  | REAL => true
  | _ => Qle_bool (Qabs v) (maxValue m)
  end.

Lemma no_underflow_fixed_point v f w:
  Denormal v (F w f) -> False.
Proof.
  unfold Denormal, minValue_pos.
  intros [abs_le non_zero].
  rewrite Q2R0_is_0 in *.
  unfold Rabs in abs_le.
  destruct (Rcase_abs v); lra.
Qed.

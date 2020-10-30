(**
  Some abbreviations that require having defined exprressions beforehand
  If we would put them in the Abbrevs file, this would create a circular dependency which Coq cannot resolve.
**)
Require Import Coq.QArith.QArith Coq.Reals.Reals Coq.QArith.Qreals Coq.QArith.QOrderedType Coq.FSets.FMapAVL Coq.FSets.FMapFacts Coq.Reals.ROrderedType Recdef.

Require Export Snapv.Infra.Abbrevs Snapv.AffineForm Snapv.Expressions Snapv.Infra.Ltacs Snapv.OrderedExpressions.

Module Q_orderedExps := ExprOrderedType (Q_as_OT).
Module legacy_OrderedQExps := Structures.OrdersAlt.Backport_OT (Q_orderedExps).

Module R_orderedExps := ExprOrderedType (R_as_OT).

Functional Scheme exprCompare_ind := Induction for Q_orderedExps.exprCompare Sort Prop.

Lemma expr_compare_eq_eval_compat (e1 e2: expr Q):
  Q_orderedExps.exprCompare e1 e2 = Eq -> (toRExp e1) = (toRExp e2).
Proof.
  intros Heq.
  functional induction (Q_orderedExps.exprCompare e1 e2); simpl in Heq;
    try congruence; try (simpl; f_equal; auto); try (now rewrite <- mTypeEq_compat_eq);
      try now apply Nat.compare_eq.
  - rewrite <- Qeq_alt in Heq.
    now apply Qeq_eqR.
  - apply Ndec.Pcompare_Peqb in e6.
    apply Pos.eqb_eq in e6; subst.
    apply N.compare_eq in Heq; subst; auto.
  - simpl in e3.
    apply andb_false_iff in e3.
    apply Ndec.Pcompare_Peqb in e6.
    apply Pos.eqb_eq in e6; subst.
    apply N.compare_eq in Heq; subst; auto.
    rewrite N.eqb_refl, Pos.eqb_refl in e3.
    destruct e3; congruence.
  - unfold unopEq in e5.
    destruct u1, u2; congruence.
(*  - simpl in e5.
    apply andb_false_iff in e5.
    apply Ndec.Pcompare_Peqb in e8.
    rewrite Pos.eqb_eq in e8; subst.
    apply N.compare_eq in Heq; subst.
    destruct e5; congruence.
  - simpl in e5.
    apply andb_false_iff in e5.
    apply Ndec.Pcompare_Peqb in e8.
    rewrite Pos.eqb_eq in e8.
    apply N.compare_eq in Heq; subst.
    rewrite N.eqb_refl, Pos.eqb_refl in *.
    destruct e5; congruence.
  - apply Pos.compare_eq in e7.
    apply N.compare_eq in Heq.
    now subst.
  - cbn in *.
    rewrite Pos.eqb_compare in e3.
    rewrite N.eqb_compare in e3.
    rewrite Heq, e7 in e3.
    discriminate.
  - cbn in *.
    rewrite Pos.eqb_compare in e3.
    rewrite N.eqb_compare in e3.
    rewrite Heq, e7 in e3.
    discriminate.*)
Qed.

Lemma Qcompare_Rcompare q1 q2:
  Qcompare q1 q2 = Rcompare (Q2R q1) (Q2R q2).
Proof.
  destruct (Qcompare q1 q2) eqn:q_check.
  - rewrite <- Qeq_alt in q_check.
    apply Qeq_eqR in q_check.
    rewrite q_check in *.
    rewrite R_orderedExps.V_orderedFacts.compare_refl in *; auto.
  - rewrite <- Qlt_alt in q_check.
    apply Qlt_Rlt in q_check.
    symmetry.
    rewrite R_orderedExps.V_orderedFacts.compare_lt_iff; auto.
  - rewrite <- Qgt_alt in q_check.
    symmetry.
    rewrite R_orderedExps.V_orderedFacts.compare_gt_iff.
    auto using Qlt_Rlt.
Qed.

Lemma QcompareExp_RcompareExp e1 e2:
  Q_orderedExps.exprCompare e1 e2 = R_orderedExps.exprCompare (toRExp e1) (toRExp e2).
Proof.
  functional induction (Q_orderedExps.exprCompare e1 e2); simpl in *; try auto; try congruence;
    try rewrite e3; try rewrite e4;
  try rewrite <- IHc, e6; try auto.
  - destruct (Qcompare v1 v2) eqn:q_comp; rewrite Qcompare_Rcompare in q_comp; auto.
  - rewrite e6; auto.
  - rewrite e6; auto.
  - rewrite e6; auto.
  - rewrite e5, IHc; auto.
  - rewrite e5, e6; auto.
  - rewrite e5, e6; auto.
(*  - rewrite <- IHc, <- IHc0, e4, e3; auto.
*)(*  - rewrite <- IHc, e3, <- IHc0, e4; auto.
  - rewrite <- IHc, e3, <- IHc0, e4; auto.
  - rewrite <- IHc, e3; auto.
  - rewrite <- IHc, e3; auto.
  - rewrite <- IHc, e5; auto.
  - rewrite e5, e8; auto.
  - rewrite e5, e8; auto.
  - rewrite e5, e8; auto.
  - rewrite <- IHc, e5; auto.
  - rewrite <- IHc, e5; auto.
  - rewrite <- IHc, e5; auto.
  - rewrite e7; auto.
  - rewrite e7; auto.
  - rewrite e7; auto.*)
    (*
  - rewrite <- IHc, <- IHc0, e3, e4; auto.
  - rewrite <- IHc, <- IHc0, e3, e4; auto.
  - rewrite <- IHc, <- IHc0, e3, e4; auto.
  - rewrite <- IHc, e3; auto.
  - rewrite <- IHc, e3; auto.
*)
Qed.

(* Lemma QcompareExp_toREvalcompare e1 e2: *)
(*   Q_orderedExps.exprCompare e1 e2 = R_orderedExps.exprCompare (toREval (toRExp e1)) (toREval (toRExp e2)). *)
(* Proof. *)
(*   functional induction (Q_orderedExps.exprCompare e1 e2); *)
(*     try auto; try congruence. *)
(*   - rewrite Qcompare_Rcompare; auto. *)
(*   - simpl in *; congruence. *)
(*   - simpl in *; congruence. *)
(*   -  *)

Lemma freeVars_eq_compat e1 e2:
  Q_orderedExps.eq e1 e2 ->
  NatSet.eq (freeVars e1) (freeVars e2).
Proof.
  intros Heq.
  unfold Q_orderedExps.eq in Heq.
  functional induction (Q_orderedExps.exprCompare e1 e2); try congruence.
  - apply Nat.compare_eq in Heq.
    now rewrite Heq.
  - now set_tac.
  - simpl.
    reflexivity.
  - set_tac.
  - specialize (IHc e6).
    specialize (IHc0 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    simpl.
    now rewrite IHc, IHc0.
  - specialize (IHc e6).
    specialize (IHc0 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    simpl.
    now rewrite IHc, IHc0.
  - specialize (IHc e6).
    specialize (IHc0 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    simpl.
    now rewrite IHc, IHc0.
  - specialize (IHc e6).
    specialize (IHc0 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    simpl.
    now rewrite IHc, IHc0.
    Admitted.
(*  - specialize (IHc e3).
    specialize (IHc0 e4).
    specialize (IHc1 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    apply NatSet.eq_leibniz in IHc1.
    simpl.
    now rewrite IHc, IHc0, IHc1.
  - simpl.
    now apply IHc.
  - simpl in e5.
    rewrite andb_false_iff in e5.
    destruct e5.
    + apply Ndec.Pcompare_Peqb in e8.
      congruence.
    + apply N.compare_eq in Heq; subst.
      rewrite N.eqb_refl in H; congruence.
  - specialize (IHc e5).
    specialize (IHc0 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    simpl.
    apply nat_compare_eq in e4.
    now rewrite IHc, IHc0, e4.
  - cbn in *.
    rewrite Pos.eqb_compare in e3.
    rewrite N.eqb_compare in e3.
    rewrite Heq, e7 in e3.
    discriminate.*)
    (*
  - specialize (IHc e3).
    specialize (IHc0 e4).
    specialize (IHc1 Heq).
    apply NatSet.eq_leibniz in IHc.
    apply NatSet.eq_leibniz in IHc0.
    apply NatSet.eq_leibniz in IHc1.
    simpl.
    now rewrite IHc, IHc0, IHc1.
*)
(*Qed.
*)
Lemma freeVars_toREval_toRExp_compat e:
  freeVars (toREval (toRExp e)) = freeVars e.
Proof.
  induction e; simpl; set_tac.
  - now rewrite IHe1, IHe2.
(*  - now rewrite IHe1, IHe2, IHe3.
  - now rewrite IHe1, IHe2.
*)  
  (* - now rewrite IHe1, IHe2, IHe3. *)
Qed.

Lemma freeVars_toRExp_compat e:
  freeVars (toRExp e) = freeVars e.
Proof.
  induction e; simpl; set_tac.
  - now rewrite IHe1, IHe2.
(*  - now rewrite IHe1, IHe2, IHe3.
  - now rewrite IHe1, IHe2.
*)  
  (* - now rewrite IHe1, IHe2, IHe3. *)
Qed.

Module SnapvMap := FMapAVL.Make(legacy_OrderedQExps).
Module SnapvMapFacts := OrdProperties (SnapvMap).

Definition analysisResult :Type := SnapvMap.t (intv * error).
Definition expressionsAffine: Type := SnapvMap.t (affine_form Q).

(**
  Later we will argue about program preconditions.
  Define a precondition to be a function mapping numbers (resp. variables) to intervals.
**)
Definition precondIntv : Type := SnapvMap.t intv.

Definition contained_Snapv_map V expmap1 expmap2 :=
  forall (e: expr Q) (v: V), SnapvMap.find e expmap1 = Some v -> SnapvMap.find e expmap2 = Some v.

Instance contained_Snapv_map_preorder (V: Type) : PreOrder (@contained_Snapv_map V).
Proof.
  constructor; unfold Reflexive, Transitive, contained_Snapv_map; eauto.
Qed.

Lemma contained_Snapv_map_extension V (expmap: SnapvMap.t V) e v:
  SnapvMap.find e expmap = None ->
  contained_Snapv_map expmap (SnapvMap.add e v expmap).
Proof.
  intros Hnone e' v' Hcont.
  rewrite <- Hcont.
  destruct (Q_orderedExps.exprCompare e e') eqn: Hcomp.
  - assert (SnapvMap.find e expmap = SnapvMap.find e' expmap) by (apply SnapvMapFacts.P.F.find_o; auto); congruence.
  - apply SnapvMapFacts.P.F.add_neq_o; congruence.
  - apply SnapvMapFacts.P.F.add_neq_o; congruence.
Qed.

Lemma contained_Snapv_map_add_compat V (expmap1 expmap2: SnapvMap.t V) e v:
  contained_Snapv_map expmap1 expmap2 ->
  contained_Snapv_map (SnapvMap.add e v expmap1) (SnapvMap.add e v expmap2).
Proof.
  unfold contained_Snapv_map.
  intros A e' v' B.
  destruct (Q_orderedExps.exprCompare e e') eqn: Hcomp.
  - rewrite SnapvMapFacts.P.F.add_eq_o in B; auto.
    rewrite SnapvMapFacts.P.F.add_eq_o; auto.
  - rewrite SnapvMapFacts.P.F.add_neq_o in B; try congruence.
    rewrite SnapvMapFacts.P.F.add_neq_o; try congruence.
    auto.
  - rewrite SnapvMapFacts.P.F.add_neq_o in B; try congruence.
    rewrite SnapvMapFacts.P.F.add_neq_o; try congruence.
    auto.
Qed.

Lemma contained_Snapv_map_none (V: Type) (e: expr Q) (expmap1: SnapvMap.t V) expmap2:
  contained_Snapv_map expmap1 expmap2 ->
  SnapvMap.find e expmap2 = None ->
  SnapvMap.find e expmap1 = None.
Proof.
  intros cont Hfound1.
  unfold contained_Snapv_map in cont.
  destruct (SnapvMap.find e expmap1) eqn: Heq; auto.
  apply cont in Heq.
  congruence.
Qed.

Lemma map_find_add e1 e2 m map1:
  SnapvMap.find e1 (SnapvMap.add e2 m map1) =
  match Q_orderedExps.compare e2 e1 with
  |Eq => Some m
  |_ => SnapvMap.find (elt:=mType) e1 map1
  end.
Proof.
  rewrite SnapvMapFacts.P.F.add_o.
  unfold SnapvMapFacts.P.F.eq_dec.
  unfold Q_orderedExps.compare.
  destruct (Q_orderedExps.exprCompare e2 e1) eqn:?; congruence.
Qed.

Lemma map_mem_add e1 e2 m map1:
  SnapvMap.mem e1 (SnapvMap.add e2 m map1) =
  match Q_orderedExps.compare e2 e1 with
  |Eq => true
  | _ => SnapvMap.mem (elt:=mType) e1 map1
  end.
Proof.
  rewrite SnapvMapFacts.P.F.mem_find_b.
  rewrite map_find_add.
  destruct (Q_orderedExps.compare e2 e1) eqn:?; try auto;
    rewrite SnapvMapFacts.P.F.mem_find_b; auto.
Qed.

Definition toRExpMap (tMap:SnapvMap.t mType) : expr R -> option mType :=
  let elements := SnapvMap.elements (elt:=mType) tMap in
  fun (e:expr R) =>
    olet p := findA
                (fun p => match R_orderedExps.compare e (toRExp p) with
                       | Eq => true |_ => false end)
                elements
      in
        Some p.

Definition toRTMap (Gamma:expr R -> option mType) :expr R -> option mType :=
  fun (e:expr R) =>
    match e with
    | Var _ _ =>
     match Gamma e with
     |Some m => Some REAL
     | _ => None
     end
    | _ => Some REAL
    end.

Definition updDefVars  (e:expr R) (m:mType) Gamma :=
  fun eNew =>
    match R_orderedExps.compare eNew e with
    |Eq => Some m
    |_ => Gamma eNew
    end.

Lemma findA_find A B (f:A -> bool) (l:list (A * B)) r:
  findA f l = Some r ->
  exists k,
  find (fun p => f (fst p)) l = Some (k,r) /\ f k = true.
Proof.
  induction l.
  - intros; simpl in *; congruence.
  - intros findA_top.
    simpl in *.
    destruct a; simpl in *.
    destruct (f a) eqn:?; try auto.
    exists a; split; congruence.
Qed.

Lemma find_swap A (f1:A -> bool) f2 l r:
  (forall k, f1 k = f2 k) ->
  find f1 l = Some r ->
  find f2 l = Some r.
Proof.
  induction l; intros f_eq find1; simpl in *; try congruence.
  destruct (f1 a) eqn:?.
  - rewrite <- f_eq; rewrite Heqb; congruence.
  - rewrite <- f_eq; rewrite Heqb.
    apply IHl; auto.
Qed.

Lemma findA_swap (A B:Type) (f1:A -> bool) f2 (l: list (A*B)) r:
  (forall k, f1 k = f2 k) ->
  findA f1 l = Some r ->
  findA f2 l = Some r.
Proof.
  induction l; intros f_eq find1; simpl in *; try congruence.
  destruct a.
  destruct (f1 a) eqn:?.
  - rewrite <- f_eq; rewrite Heqb0; auto.
  - rewrite <- f_eq; rewrite Heqb0.
    apply IHl; auto.
Qed.

Lemma findA_swap2 (A B:Type) (f1:A -> bool) f2 (l: list (A*B)):
  (forall k, f1 k = f2 k) ->
  findA f1 l = findA f2 l.
Proof.
  induction l; intros f_eq; simpl in *; try congruence.
  destruct a.
  destruct (f1 a) eqn:?.
  - rewrite <- f_eq; rewrite Heqb0; congruence.
  - rewrite <- f_eq; rewrite Heqb0.
    apply IHl; auto.
Qed.

Lemma toRExpMap_some tMap e e2 m:
  e2 = toRExp e ->
  SnapvMap.find e tMap = Some m ->
  toRExpMap tMap e2 = Some m.
Proof.
  intros ? find_Q; subst.
  rewrite  SnapvMapFacts.P.F.elements_o in find_Q.
  unfold toRExpMap.
  unfold optionBind.
  erewrite <- findA_swap2 with (f1 := SnapvMapFacts.P.F.eqb e).
  - rewrite find_Q; auto.
  - unfold R_orderedExps.compare.
    intros.
    rewrite <- QcompareExp_RcompareExp.
    unfold SnapvMapFacts.P.F.eqb, SnapvMapFacts.P.F.eq_dec.
    destruct (Q_orderedExps.exprCompare e k) eqn:q_comp; auto.
Qed.

Lemma toRExpMap_find_map tMap e m:
  toRExpMap tMap (toRExp e) = Some m ->
  SnapvMap.find e tMap = Some m.
Proof.
  intros RTMap_def.
  unfold toRExpMap, optionBind in *.
  Snapv_compute.
  inversion RTMap_def; subst.
  rewrite SnapvMapFacts.P.F.elements_o.
  erewrite <- findA_swap2 with
      (f1 := fun p => match R_orderedExps.compare (toRExp e) (toRExp p) with
             |Eq => true |_ => false end); try auto.
  intros. unfold R_orderedExps.compare; rewrite <- QcompareExp_RcompareExp.
  unfold SnapvMapFacts.P.F.eqb, SnapvMapFacts.P.F.eq_dec.
  destruct (Q_orderedExps.exprCompare e k) eqn:q_comp; auto.
Qed.

Lemma toRExpMap_some_cases tMap e1 e2 m1 m2:
  toRExpMap (SnapvMap.add e1 m1 tMap) (toRExp e2) = Some m2 ->
  (R_orderedExps.exprCompare (toRExp e1) (toRExp e2) = Eq /\ m1 = m2) \/ toRExpMap tMap (toRExp e2) = Some m2.
Proof.
  intros map_def.
  apply toRExpMap_find_map in map_def.
  rewrite SnapvMapFacts.P.F.add_o in map_def.
  destruct (SnapvMap.E.eq_dec e1 e2) eqn:?.
  - left. inversion map_def; split; try auto.
    rewrite <- QcompareExp_RcompareExp; auto.
  - right. eauto using toRExpMap_some.
Qed.

Lemma eqb_cmp_eq e1 e2:
  SnapvMapFacts.P.F.eqb e1 e2 = match Q_orderedExps.exprCompare e1 e2 with
                                 | Eq => true
                                 | _ => false end.
Proof.
  unfold SnapvMapFacts.P.F.eqb, SnapvMapFacts.P.F.eq_dec.
  destruct (Q_orderedExps.exprCompare e1 e2) eqn:q_comp; auto.
Qed.

Lemma Q_compare_eq_Rcompare_eq e1 e2:
  Q_orderedExps.exprCompare e1 e2 = Eq ->
  R_orderedExps.exprCompare (toREval (toRExp e1)) (toREval (toRExp e2)) = Eq.
Proof.
  functional induction (Q_orderedExps.exprCompare e1 e2);
    simpl in *; try congruence;
      intros;
      try eauto.
  - rewrite <- Qcompare_Rcompare; auto.
  - apply Pos.compare_eq in e6; subst.
    apply N.compare_eq in H; subst.
    rewrite Pos.eqb_refl, N.eqb_refl in e3; simpl in *; congruence.
  - rewrite IHc, e5; auto.
  - rewrite IHc; auto.
  - rewrite IHc, IHc0; auto.
  - rewrite IHc, IHc0; auto.
  - rewrite IHc, IHc0; auto.
  - rewrite IHc, IHc0; auto.
    Admitted.
(*  - apply Pos.compare_eq in e8; subst.
    apply N.compare_eq in H; subst.
    rewrite Pos.eqb_refl, N.eqb_refl in e5; simpl in *; congruence.
  - rewrite e4, IHc, IHc0; auto.
  - cbn in *.
    rewrite Pos.eqb_compare in e3.
    rewrite N.eqb_compare in e3.
    rewrite H, e7 in e3.
    discriminate.*)
  (* - rewrite IHc, IHc0; auto. *)
(*Qed.
*)
Lemma no_cycle_unop e:
  forall u, Q_orderedExps.exprCompare e (Unop u e) <> Eq.
  induction e; intros *;  cbn in *; try congruence.
  destruct (unopEq u u0) eqn:?; try auto.
  destruct (unopEq u Neg); congruence.
Qed.

(*Lemma no_cycle_cast e:
  forall m, Q_orderedExps.exprCompare e (Downcast m e) <> Eq.
  induction e; intros *;  cbn in *; try congruence.
  destruct (mTypeEq m m0) eqn:?; try auto.
  destruct m; destruct m0; type_conv; try congruence;
    cbn; hnf; intros; try congruence.
  destruct (w ?= w0)%positive eqn:?; try congruence.
  apply Pos.compare_eq in Heqc.
  apply N.compare_eq in H; subst; congruence.
Qed.*)

Lemma no_cycle_binop_left e1:
  forall b e2, Q_orderedExps.exprCompare e1 (Binop b e1 e2) <> Eq.
  induction e1; intros *;  cbn in *; try congruence.
  pose (bOp := b);
    destruct b; destruct b0;
      try (hnf; intros; congruence);
          destruct (Q_orderedExps.exprCompare e1_1 (Binop bOp e1_1 e1_2)) eqn:case_comp;
                   subst bOp; rewrite case_comp in *;
          congruence.
Qed.

Lemma no_cycle_binop_right e2:
  forall b e1, Q_orderedExps.exprCompare e2 (Binop b e1 e2) <> Eq.
  induction e2; intros *;  cbn in *; try congruence.
  pose (bOp := b);
    destruct b; destruct b0;
      try (hnf; intros; congruence);
      destruct (Q_orderedExps.exprCompare e2_1 e1) eqn:?; congruence.
Qed.

(*Lemma no_cycle_fma_left e1:
  forall e2 e3, Q_orderedExps.exprCompare e1 (Fma e1 e2 e3) <> Eq.
Proof.
  induction e1; intros *; cbn in *; try congruence;
    destruct (Q_orderedExps.exprCompare e1_1 (Fma e1_1 e1_2 e1_3)) eqn:?; congruence.
Qed.
*)
(*Lemma no_cycle_fma_center e2:
  forall e1 e3, Q_orderedExps.exprCompare e2 (Fma e1 e2 e3) <> Eq.
Proof.
  induction e2; intros *; cbn in *; try congruence.
  destruct (Q_orderedExps.exprCompare e2_1 e1) eqn:?; try congruence.
    destruct (Q_orderedExps.exprCompare e2_2 (Fma e2_1 e2_2 e2_3)) eqn:?; congruence.
Qed.
*)
(*Lemma no_cycle_fma_right e3:
  forall e1 e2, Q_orderedExps.exprCompare e3 (Fma e1 e2 e3) <> Eq.
Proof.
  induction e3; intros *; cbn in *; try congruence.
  destruct (Q_orderedExps.exprCompare e3_1 e1) eqn:?; try congruence.
  destruct (Q_orderedExps.exprCompare e3_2 e2) eqn:?; try congruence.
Qed.
*)
  
(*Lemma no_cycle_let_left e1:
  forall e2 x m, Q_orderedExps.exprCompare e1 (Let m x e1 e2) <> Eq.
Proof.
  induction e1; intros *; cbn in *; try congruence.
  destruct (mTypeEq m m0) eqn:?.
  + destruct (n ?= x)%nat eqn:?; try congruence.
    destruct (Q_orderedExps.exprCompare e1_1 (Let m n e1_1 e1_2)) eqn:?;
             try congruence.
  + destruct (n ?= x)%nat eqn:?; try congruence.
    destruct (morePrecise m m0) eqn:?; unfold morePrecise in *;
      destruct m; destruct m0; try congruence.
    * rewrite Pos.leb_compare in *.
      unfold mTypeEq in *.
      rewrite POrderedType.Positive_as_OT.compare_antisym in Heqb0.
      rewrite Pos.eqb_compare in *.
      destruct (w ?= w0)%positive eqn:?; simpl; try congruence.
      rewrite N.eqb_compare in *.
      destruct (f ?= f0)%N eqn:?; simpl in *; congruence.
    * rewrite Pos.leb_compare in *.
      unfold mTypeEq in *.
      rewrite POrderedType.Positive_as_OT.compare_antisym in Heqb0.
      rewrite Pos.eqb_compare in *.
      destruct (w ?= w0)%positive eqn:?; simpl; try congruence.
      rewrite N.eqb_compare in *.
      destruct (f ?= f0)%N eqn:?; simpl in *; congruence.
Qed.

Lemma no_cycle_let_right e2:
  forall e1 x m, Q_orderedExps.exprCompare e2 (Let m x e1 e2) <> Eq.
Proof.
  induction e2; intros *; cbn in *; try congruence.
  destruct (mTypeEq m m0) eqn:?.
  + destruct (n ?= x)%nat eqn:?; try congruence.
    destruct (Q_orderedExps.exprCompare e2_1 e1) eqn:?; try congruence.
  + destruct (n ?= x)%nat eqn:?; try congruence.
    destruct (morePrecise m m0) eqn:?; unfold morePrecise in *;
      destruct m; destruct m0; try congruence.
    * rewrite Pos.leb_compare in *.
      unfold mTypeEq in *.
      rewrite POrderedType.Positive_as_OT.compare_antisym in Heqb0.
      rewrite Pos.eqb_compare in *.
      destruct (w ?= w0)%positive eqn:?; simpl; try congruence.
      rewrite N.eqb_compare in *.
      destruct (f ?= f0)%N eqn:?; simpl in *; congruence.
    * rewrite Pos.leb_compare in *.
      unfold mTypeEq in *.
      rewrite POrderedType.Positive_as_OT.compare_antisym in Heqb0.
      rewrite Pos.eqb_compare in *.
      destruct (w ?= w0)%positive eqn:?; simpl; try congruence.
      rewrite N.eqb_compare in *.
      destruct (f ?= f0)%N eqn:?; simpl in *; congruence.
Qed.*)

(*
Lemma toRExpMap_toRTMap e Gamma m:
  toRExpMap Gamma (toRExp e) = Some m ->
  toRTMap Gamma (toREval (toRExp e)) = Some REAL.
Proof.
  intros map_def.
  unfold toRTMap.
  apply toRExpMap_find_map in map_def.
  Snapv_compute.
  rewrite SnapvMapFacts.P.F.elements_o in map_def.
  erewrite findA_swap2 with
      (f2 := SnapvMapFacts.P.F.eqb e) in Heqo; try congruence.
  intros. unfold R_orderedExps.compare.
  rewrite eqb_cmp_eq.
  clear map_def Heqo.
  destruct (Q_orderedExps.exprCompare e k) eqn:?.
  unfold SnapvMapFacts.P.F.eqb, SnapvMapFacts.P.F.eq_dec.
  rewrite <- QcompareExp_RcompareExp.
  destruct (Q_orderedExps.exprCompare e k) eqn:q_comp; auto.
*)

(**

to pairs of intervals on rationals and rational errors as the analysis result
**)
(* Definition analysisResult :Type := expr Q -> intv * error. *)

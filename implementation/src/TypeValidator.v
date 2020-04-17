(**
  Implementation of machine-precision as a datatype for mixed-precision computations

  @author: Raphael Monat
  @maintainer: Heiko Becker
 **)
From Coq
     Require Import Reals.Reals micromega.Psatz QArith.QArith QArith.Qreals
     MSets.MSets.
From Snapv
     Require Import Infra.RationalSimps Infra.RealRationalProps Infra.Ltacs
     ssaPrgs.
From Snapv
     Require Export Infra.ExpressionAbbrevs Infra.RealSimps Infra.NatSet
     Infra.MachineType Infra.Ltacs Infra.Results.
Require Import String.
(**
    Correctness predicate for type inference:
    For any subterm of the analyzed expression e, it must hold:
    If we have defined all the variables in e in an environment E and
    no division by zero occurs, evaluation does not crash because of the type
    assignment
**)

Fixpoint validTypes e (Gamma:SnapvMap.t mType): Prop :=
  exists mG,
    SnapvMap.find e Gamma = Some mG /\
    match e with
    | Var _ x => True
    | Const m v => m = mG
    | Unop u e1 =>
      validTypes e1 Gamma /\
      exists me, SnapvMap.find e1 Gamma = Some me /\ isCompat me mG = true
    | Binop b e1 e2 =>
      validTypes e1 Gamma /\
      validTypes e2 Gamma /\
      exists m1 m2, SnapvMap.find e1 Gamma = Some m1 /\
               SnapvMap.find e2 Gamma = Some m2 /\
               isJoin m1 m2 mG = true
    | Fma e1 e2 e3 =>
      validTypes e1 Gamma /\
      validTypes e2 Gamma /\
      validTypes e3 Gamma /\
      exists m1 m2 m3,
        SnapvMap.find e1 Gamma = Some m1 /\ SnapvMap.find e2 Gamma = Some m2 /\
        SnapvMap.find e3 Gamma = Some m3 /\
        isJoin3 m1 m2 m3 mG = true
    | Downcast m e1 =>
      validTypes e1 Gamma /\ m = mG /\
      exists m1,
        (SnapvMap.find e1 Gamma = Some m1 /\ isMorePrecise m1 mG = true)
    | Let m x e1 e2 =>
      validTypes e1 Gamma /\
      validTypes e2 Gamma /\
      exists me,
        SnapvMap.find e1 Gamma = Some m /\ SnapvMap.find (Var Q x) Gamma = Some m /\
        SnapvMap.find e2 Gamma = Some me /\ me = mG
     (*
    | Cond e1 e2 e3 =>
      validTypes e1 Gamma /\
      validTypes e2 Gamma /\
      validTypes e3 Gamma /\
      exists m1 m2 m3,
        SnapvMap.find e1 Gamma = Some m1 /\
        SnapvMap.find e2 Gamma = Some m2 /\
        SnapvMap.find e3 Gamma = Some m3 /\
        isJoin m2 m3 mG = true
      *)
  end /\
    (forall E Gamma2 DeltaMap v m,
        (forall e m, SnapvMap.find e Gamma = Some m ->
                SnapvMap.find e Gamma2 = Some m) ->
        eval_expr E (toRExpMap Gamma2) DeltaMap (toRExp e) v m ->
        m = mG).

Corollary validTypes_single e Gamma:
  validTypes e Gamma ->
  exists mG,
    SnapvMap.find e Gamma = Some mG /\
    forall E v m Gamma2 DeltaMap,
      (forall e m, SnapvMap.find e Gamma = Some m -> SnapvMap.find e Gamma2 = Some m) ->
      eval_expr E (toRExpMap Gamma2) DeltaMap (toRExp e) v m ->
      m = mG.
Proof.
  destruct e; intros * [? [defined_m [check_t valid_top]]]; simpl in *; eauto.
Qed.

Corollary validTypes_exec e Gamma m:
  validTypes e Gamma ->
  SnapvMap.find e Gamma = Some m ->
  forall E DeltaMap v mR,
    eval_expr E (toRExpMap Gamma) DeltaMap (toRExp e) v mR ->
    m = mR.
Proof.
  intros * valid_e find_e * eval_e.
  apply validTypes_single in valid_e.
  destruct valid_e as [? [find_e_new valid_exec]].
  erewrite valid_exec; eauto.
  congruence.
Qed.

Ltac validTypes_split :=
  match goal with
  | [ H: validTypes (Const ?m ?v) ?Gamma |- _] => idtac
  | [ H: validTypes (Var ?t ?x) ?Gamma |- _] => idtac
  | [ H: validTypes (Unop ?u ?e) ?Gamma |- _] =>
    let n := fresh "valid_arg" in
    assert (validTypes e Gamma)
      as n
        by (destruct H as [? [? [[? ?] ?]]]; eauto)
  | [ H: validTypes (Binop ?b ?e1 ?e2) ?Gamma |- _] =>
    let n1 := fresh "valid_arg" in
    let n2 := fresh "valid_arg" in
    assert (validTypes e1 Gamma)
      as n1
        by (destruct H as [? [? [[? [? ?]] ?]]]; auto);
    assert (validTypes e2 Gamma)
      as n2
        by (destruct H as [? [? [[? [? ?]] ?]]]; auto)
  | [ H: validTypes (Fma ?e1 ?e2 ?e3) ?Gamma |- _] =>
    let n1 := fresh "valid_arg" in
    let n2 := fresh "valid_arg" in
    let n3 := fresh "valid_arg" in
    assert (validTypes e1 Gamma)
      as n1
        by (destruct H as [? [? [[? [? [? ?]]] ?]]]; auto);
    assert (validTypes e2 Gamma)
      as n2
        by (destruct H as [? [? [[? [? [? ?]]] ?]]]; auto);
    assert (validTypes e3 Gamma)
      as n3
        by (destruct H as [? [? [[? [? [? ?]]] ?]]]; auto)
  | [ H: validTypes (Downcast ?m ?e) ?Gamma |- _] =>
    let n := fresh "valid_arg" in
    assert (validTypes e Gamma)
      as n
        by (destruct H as [? [? [[? ?] ?]]]; eauto)

  | [ H: validTypes (Let ?m ?x ?e1 ?e2) ?Gamma |- _] =>
    let n1 := fresh "valid_arg" in
    let n2 := fresh "valid_arg" in
    assert (validTypes e1 Gamma)
      as n1
        by (destruct H as [? [? [[? [? ?]] ?]]]; auto);
    assert (validTypes e2 Gamma)
      as n2
        by (destruct H as [? [? [[? [? ?]] ?]]]; auto)
  end.

Ltac validTypes_simp :=
  match goal with
  | [ H: validTypes ?e ?Gamma |- _ ] => validTypes_split; apply validTypes_single in H
  | _ => fail "No typing assumption found"
  end.

Open Scope string_scope.

Definition isMonotone mOldO mNew :=
  match mOldO with
  |None => true
  |Some mOld => mTypeEq mOld mNew
  end.

Definition addMono e m map :=
  match SnapvMap.find e map with
  |Some mOld => Fail (SnapvMap.t mType) "Nonmonotonic map update"
   (* if (mTypeEq m mOld)
   then Succes map
   else Fail _ "Nonmonotonic map update" *)
  | None =>
    Succes (SnapvMap.add e m map)
  end.

Fixpoint getValidMap (Gamma:SnapvMap.t mType) (e:expr Q)
         (akk:SnapvMap.t mType)
  : result (SnapvMap.t mType) :=
  if (SnapvMap.mem e akk)
  then Succes akk
  else
    let mOldO := SnapvMap.find e Gamma in
    match e with
    | Var _ v =>
      match mOldO with
      | Some m => Succes (SnapvMap.add e m akk)
      | None => Fail _ "Undefined variable"
      end
    | Const m n =>
      if (isMonotone mOldO m)
      then Succes (SnapvMap.add e m akk)
      else Fail _ "Wrong type annotation for Constant"
    | Unop u e1 =>
      rlet akk_new := getValidMap Gamma e1 akk in
      match SnapvMap.find e1 akk_new with
      | None => Fail _ "Cannot Typecheck unary operator"
      | Some m_e1 =>
        if (isFixedPointB m_e1)
        then
          match mOldO with
          |None => Fail _ "Undefined fixed-point type"
          |Some mFix =>
           if (isCompat m_e1 mFix)
           then addMono e mFix akk_new
           else Fail _ "Incompatible type assignment"
          end
        else
          if (isMonotone mOldO m_e1)
          then addMono e m_e1 akk_new
          else Fail _ "Wrong type annotation for unary constant"
      end
  | Binop b e1 e2 =>
    rlet akk1_map := getValidMap Gamma e1 akk  in
    rlet akk2_map := getValidMap Gamma e2 akk1_map in
    let m1 := SnapvMap.find e1 akk2_map in
    let m2 := SnapvMap.find e2 akk2_map in
    match m1, m2 with
    |Some t1, Some t2 =>
     if (isFixedPointB t1 && isFixedPointB t2)
     then
       match mOldO with
       | None => Fail _ "Undefined fixed-point type"
       | Some mj =>
         if (morePrecise t1 mj && morePrecise t2 mj)
         then addMono e mj akk2_map
         else Fail _ "Incorrect fixed-point type"
       end
     else
       match (join_fl t1 t2) with
       | None => Fail _ "Could not compute join for arguments"
       | Some m =>
         if (isMonotone mOldO m)
         then addMono e m akk2_map
         else Fail _ "Wrong type annotation for binary operator"
       end
    | _, _ => Fail _ "Could not compute type for arguments"
    end
  | Fma e1 e2 e3 =>
    rlet akk1_map := getValidMap Gamma e1 akk in
    rlet akk2_map := getValidMap Gamma e2 akk1_map in
    rlet akk3 := getValidMap Gamma e3 akk2_map in
    let m1 := SnapvMap.find e1 akk3 in
    let m2 := SnapvMap.find e2 akk3 in
    let m3 := SnapvMap.find e3 akk3 in
    match m1, m2, m3 with
    |Some t1, Some t2, Some t3 =>
     if (isFixedPointB t1 && isFixedPointB t2 && isFixedPointB t3)
     then
       match mOldO with
       | None => Fail _ "Undefined fixed-point type"
       | Some mj =>
         if (morePrecise t1 mj && morePrecise t2 mj && morePrecise t3 mj)
         then addMono e mj akk3
         else Fail _ "Incorrect fixed-point type"
       end
     else
       match (join_fl3 t1 t2 t3) with
       |Some m =>
        if (isMonotone mOldO m)
        then addMono e m akk3
        else Fail _ "Incorrect type assignment for FMA"
       | _ => Fail _ "Could not compute join for FMA"
       end
    | _, _, _ => Fail _ "Could not infer type for argument of FMA"
    end
  | Downcast m e1 =>
    rlet akk_new := getValidMap Gamma e1 akk in
    let m1 := SnapvMap.find e1 akk_new in
    match m1 with
    | None => Fail _ "Could not find cast argument type"
    | Some t1 =>
      if (isFixedPointB t1)
      then
        match mOldO with
        |None => Fail _ "Could not find fixed-point type for cast"
        |Some mFix => if (mTypeEq m mFix && morePrecise t1 mFix)
                     then addMono e mFix akk_new
                     else Fail _ "Incorrect fixed-point type"
        end
      else
        if (morePrecise t1 m && isMonotone mOldO m)
        then addMono e m akk_new
        else Fail _ "Cannot cast down to lower precision"
    end
  | Let m x e1 e2 =>
    rlet res1 := getValidMap Gamma e1 akk in
    match SnapvMap.find e1 res1 with
    | None => Fail _ "No type computed for argument"
    | Some m1 =>
      (* Let bound type and inferred type agree *)
      if (mTypeEq m m1)
      then
        (* Monotonic update *)
        rlet newMap := addMono (Var Q x) m res1 in
        (* recursive call *)
        rlet resMap := getValidMap Gamma e2 newMap in
        (* get type for continuation *)
        match SnapvMap.find e2 resMap with
        | None => Fail _ "Undefined type for let-continuation"
        | Some mLet =>
        if (isMonotone mOldO mLet)
        then
          if (isFixedPointB mLet)
          then
            match mOldO with
            | None => Fail _ "Undefined fixed-point type"
            | Some mj =>
              addMono e mj resMap
            end
          else
            addMono e mLet resMap
        else Fail _  "Non-monotonic type assignment for let-binding"
        end
      else
        Fail _ "Incorrect type for let-bound variable"
    end
      (*
  | Cond e1 e2 e3 =>
    rlet akk1_map := getValidMap Gamma e1 akk in
    rlet akk2_map := getValidMap Gamma e2 akk1_map in
    rlet akk3 := getValidMap Gamma e3 akk2_map in
    let m1 := SnapvMap.find e1 akk3 in
    let m2 := SnapvMap.find e2 akk3 in
    let m3 := SnapvMap.find e3 akk3 in
    match m1, m2, m3 with
    |Some t1, Some t2, Some t3 =>
     if (isFixedPointB t2 && isFixedPointB t3)
     then
       match mOldO with
       | None => Fail _ "Undefined fixed-point type"
       | Some mj =>
         if (morePrecise t2 mj && morePrecise t3 mj)
         then addMono e mj akk3
         else Fail _ "Incorrect fixed-point type"
       end
     else
       match (join_fl t2 t3) with
       |Some m =>
        if (isMonotone mOldO m)
        then addMono e m akk3
        else Fail _ "Incorrect type assignment for Cond"
       | _ => Fail _ "Could not compute join for Cond"
       end
    | _, _, _ => Fail _ "Could not infer type for argument of Cond"
    end
       *)
  end.

Lemma tMap_def:
  forall (e:expr Q) (m:mType) akk,
    SnapvMap.find e (SnapvMap.add e m akk) = Some m.
Proof.
  intros.
  rewrite  SnapvMapFacts.P.F.add_eq_o;
    auto using Q_orderedExps.exprCompare_refl.
Qed.

Lemma toRExpMap_def:
  forall e e' m akk,
    e' = toRExp e ->
    toRExpMap (SnapvMap.add e m akk) e' = Some m.
Proof.
  intros.
  subst; eapply toRExpMap_some;
  eauto using tMap_def.
Qed.

Ltac by_monotonicity find_akk mem_case:=
  rewrite map_find_add;
  match goal with
  | [ H: _ |- context [Q_orderedExps.compare ?e1 ?e2] ] =>
    destruct (Q_orderedExps.compare e1 e2) eqn:?; try eauto
  end;
  erewrite <- SnapvMapFacts.P.F.find_o in find_akk; try eauto;
  rewrite SnapvMapFacts.P.F.mem_find_b in mem_case;
  rewrite find_akk in *; congruence.

Ltac unfold_addMono :=
  unfold addMono in *;
  Snapv_compute;
  try
  match goal with
  | [ H: context [mTypeEq ?m1 ?m2] |- _] => destruct (mTypeEq m1 m2) eqn:?; type_conv; subst
  end;
  try congruence; inversion getMap_succeeds; subst.

Lemma mem_add_cases:
  forall e1 e2 (M:SnapvMap.t mType) (m:mType),
    SnapvMap.mem e1 (SnapvMap.add e2 m M) = true ->
    (Q_orderedExps.exprCompare e1 e2 = Eq) \/
    (Q_orderedExps.exprCompare e1 e2 <> Eq /\ SnapvMap.mem e1 M = true).
Proof.
  intros * mem_add. rewrite map_mem_add in mem_add.
  unfold Q_orderedExps.compare in *.
  destruct (Q_orderedExps.exprCompare e2 e1) eqn:?; [left | auto | right ].
  - inversion mem_add. now rewrite legacy_OrderedQExps.eq_sym.
  - split; try auto. rewrite Q_orderedExps.exprCompare_antisym in * |- .
    destruct (Q_orderedExps.exprCompare e1 e2) eqn:?; simpl in *; congruence.
Qed.

Lemma find_add_cases:
  forall e1 e2 (M:SnapvMap.t mType) (m:mType) r,
    SnapvMap.find e1 (SnapvMap.add e2 m M) = Some r ->
    (Q_orderedExps.exprCompare e1 e2 = Eq /\ m = r) \/
    (Q_orderedExps.exprCompare e1 e2 <> Eq /\ SnapvMap.find e1 M = Some r).
Proof.
  intros * find_add. rewrite map_find_add in find_add.
  unfold Q_orderedExps.compare in *.
  destruct (Q_orderedExps.exprCompare e2 e1) eqn:?; [left | auto | right ].
  - inversion find_add. now rewrite legacy_OrderedQExps.eq_sym.
  - split; try auto. rewrite Q_orderedExps.exprCompare_antisym in * |- .
    destruct (Q_orderedExps.exprCompare e1 e2) eqn:?; simpl in *; congruence.
Qed.

Lemma getValidMap_mono e:
  forall Gamma akk res,
    getValidMap Gamma e akk = Succes res ->
    forall e m, SnapvMap.find e akk = Some m ->
           SnapvMap.find e res = Some m.
Proof.
  pose (eT := e);
    induction e; intros * getMap_succeeds * find_akk;
      destruct (SnapvMap.mem eT akk) eqn:Hmem; subst;
        cbn in getMap_succeeds; subst eT;
          rewrite Hmem in *;
          try (inversion getMap_succeeds; subst; auto; fail "");
          Snapv_compute; try congruence.
  - inversion getMap_succeeds; subst.
    by_monotonicity find_akk Hmem.
  - unfold isMonotone in *.
    Snapv_compute.
    + destruct (mTypeEq m1 m) eqn:?; try congruence; type_conv; subst.
      inversion getMap_succeeds; subst.
      by_monotonicity find_akk Hmem.
    +  inversion getMap_succeeds; subst.
       by_monotonicity find_akk Hmem.
  - specialize (IHe Gamma akk t Heqr).
    destruct (isFixedPointB m0) eqn:?.
    + destruct (isCompat m0 m1) eqn:?; try congruence.
      unfold_addMono; try eauto using IHe.
      by_monotonicity find_akk Hmem.
    + destruct (mTypeEq m1 m0) eqn:?; try congruence.
      unfold_addMono; try eauto using IHe.
      by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0) eqn:?; try congruence.
    simpl in IHe. specialize (IHe Gamma akk t Heqr).
    unfold_addMono; try eauto using IHe.
    by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1) eqn:?;
             Snapv_compute; try congruence;
      [ destruct (morePrecise m0 m2 && morePrecise m1 m2) eqn:?; try congruence
      | destruct (mTypeEq m2 m3) eqn:?; try congruence ];
      unfold_addMono; try eauto; by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1) eqn:?;
             try congruence.
    destruct (morePrecise m0 m2 && morePrecise m1 m2) eqn:?; try congruence.
    unfold_addMono; try eauto.
    by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1) eqn:?;
             try congruence.
    unfold_addMono; try eauto.
    by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1) eqn:?;
             congruence.
  - destruct (isFixedPointB m0 && isFixedPointB m1 && isFixedPointB m2) eqn:?;
             try congruence;
      [ destruct (morePrecise m0 m3 && morePrecise m1 m3 && morePrecise m2 m3) eqn:?;
                 try congruence
      | destruct (mTypeEq m3 m4) eqn:?; try congruence];
    unfold_addMono; try eauto;
        by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1 && isFixedPointB m2) eqn:?;
             try congruence;
      destruct (morePrecise m0 m3 && morePrecise m1 m3 && morePrecise m2 m3) eqn:?;
                 try congruence;
      unfold_addMono; try eauto;
      by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1 && isFixedPointB m2) eqn:?;
             try congruence;
      unfold_addMono; try eauto;
      by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m0 && isFixedPointB m1 && isFixedPointB m2) eqn:?;
             congruence.
  - destruct (isFixedPointB m1) eqn:?;
             [ destruct (mTypeEq m m2 && morePrecise m1 m2) eqn:?; try congruence
             | destruct (morePrecise m1 m && mTypeEq m2 m) eqn:?; try congruence];
      unfold_addMono; try eauto;
        by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m1) eqn:?;
             [ | destruct (morePrecise m1 m && true) eqn:?; try congruence];
      unfold_addMono; try eauto;
        by_monotonicity find_akk Hmem.
  - destruct (mTypeEq m m1) eqn:?; try congruence. type_conv; subst.
    specialize (IHe1 _ _ _ Heqr).
    specialize (IHe2 _ _ _ Heqr1).
    rewrite SnapvMapFacts.P.F.mem_find_b in Hmem.
    destruct (isFixedPointB m2) eqn:?;
             unfold_addMono;
      inversion Heqr0; subst;
      rewrite map_find_add;
      destruct (Q_orderedExps.compare (Let m1 n e1 e2) e) eqn:?.
    + erewrite SnapvMapFacts.P.F.find_o in Heqo2; try eauto; congruence.
    + apply IHe2.
      rewrite map_find_add;
        destruct (Q_orderedExps.compare (Var Q n) e) eqn:?.
      * erewrite <- SnapvMapFacts.P.F.find_o in find_akk; eauto.
        specialize (IHe1 _ _ find_akk). congruence.
      * now apply IHe1.
      * now apply IHe1.
    + apply IHe2.
      rewrite map_find_add;
        destruct (Q_orderedExps.compare (Var Q n) e) eqn:?.
      * erewrite <- SnapvMapFacts.P.F.find_o in find_akk; eauto.
        specialize (IHe1 _ _ find_akk). congruence.
      * now apply IHe1.
      * now apply IHe1.
    + erewrite SnapvMapFacts.P.F.find_o in Heqo2; try eauto; congruence.
    + apply IHe2.
      rewrite map_find_add;
        destruct (Q_orderedExps.compare (Var Q n) e) eqn:?.
      * erewrite <- SnapvMapFacts.P.F.find_o in find_akk; eauto.
        specialize (IHe1 _ _ find_akk). congruence.
      * now apply IHe1.
      * now apply IHe1.
    + apply IHe2.
      rewrite map_find_add;
        destruct (Q_orderedExps.compare (Var Q n) e) eqn:?.
      * erewrite <- SnapvMapFacts.P.F.find_o in find_akk; eauto.
        specialize (IHe1 _ _ find_akk). congruence.
      * now apply IHe1.
      * now apply IHe1.
  - destruct (mTypeEq m m1) eqn:?; try congruence.
    destruct (isFixedPointB m2) eqn:?; try congruence.
    specialize (IHe1 _ _ _ Heqr);
      specialize (IHe2 _ _ _ Heqr1).
    unfold_addMono.
    rewrite SnapvMapFacts.P.F.mem_find_b in Hmem.
    rewrite map_find_add;
    destruct (Q_orderedExps.compare (Let m1 n e1 e2) e) eqn:?.
    + erewrite <- SnapvMapFacts.P.F.find_o in find_akk; try eauto.
      rewrite find_akk in *. congruence.
    + apply IHe2; eauto.
      inversion Heqr0; subst.
      rewrite map_find_add;
        destruct (Q_orderedExps.compare (Var Q n) e) eqn:?.
      * erewrite <- SnapvMapFacts.P.F.find_o in find_akk; eauto.
        specialize (IHe1 _ _ find_akk). congruence.
      * now eapply IHe1.
      * now apply IHe1.
    + apply IHe2.
      inversion Heqr0; subst.
      rewrite map_find_add;
        destruct (Q_orderedExps.compare (Var Q n) e) eqn:?.
      * erewrite <- SnapvMapFacts.P.F.find_o in find_akk; eauto.
        specialize (IHe1 _ _ find_akk). congruence.
      * now apply IHe1.
      * now apply IHe1.
  - destruct (mTypeEq m m1) eqn:?; congruence.
  - destruct (mTypeEq m m1) eqn:?; congruence.
  - destruct (mTypeEq m m1) eqn:?; congruence.
  - destruct (mTypeEq m m1) eqn:?; congruence.
  - destruct (mTypeEq m m1) eqn:?; congruence.
    (*
  - destruct (isFixedPointB m1 && isFixedPointB m2) eqn:?;
             try congruence;
      destruct (morePrecise m1 m3 && morePrecise m2 m3) eqn:?;
                 try congruence;
      unfold_addMono; try eauto;
      by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m1 && isFixedPointB m2) eqn:?;
             try congruence;
      destruct (morePrecise m1 m3 && morePrecise m2 m3) eqn:?;
                 try congruence;
      unfold_addMono; try eauto;
      by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m1 && isFixedPointB m2) eqn:?;
             try congruence;
      unfold_addMono; try eauto;
      by_monotonicity find_akk Hmem.
  - destruct (isFixedPointB m1 && isFixedPointB m2) eqn:?; congruence.
     *)
Qed.

Lemma validTypes_mono e:
  forall map1 map2,
  (forall e m, SnapvMap.find e map1 = Some m -> SnapvMap.find e map2 = Some m) ->
  validTypes e map1 ->
  validTypes e map2.
Proof.
  induction e; intros * maps_mono valid_m1; simpl in *;
    destruct valid_m1 as [t_m1 [find_map1 [check_top valid_rec]]];
    pose proof (maps_mono _ _ find_map1) as find_mono; eexists; split; try eauto.
  - repeat split; try eauto.
    destruct check_top as [valid_e1 check_top]; eapply IHe; eauto.
    destruct check_top as [? [? [? ?]]].
    eexists; split; eauto.
  - destruct check_top as [valid_e1 [valid_e2 validJoin]];
      repeat split; try eauto.
    destruct validJoin as [m1 [m2 [find_m1 [find_m2 join_true]]]].
    pose proof (maps_mono e1 m1 find_m1) as find_m1_map2;
      pose proof (maps_mono e2 m2 find_m2) as find_m2_map2.
    eauto.
  - destruct check_top as [valid_e1 [valid_e2  [valid_e3 validJoin]]];
      repeat split; try eauto.
    destruct validJoin as [m1 [m2 [m3 [find_m1 [find_m2 [find_m3 join_true]]]]]].
    pose proof (maps_mono e1 m1 find_m1) as find_m1_map2;
      pose proof (maps_mono e2 m2 find_m2) as find_m2_map2;
      pose proof (maps_mono e3 m3 find_m3) as find_m3_map2.
    repeat eexists; eauto.
  - destruct check_top as [valid_e1 [m_eq [m_e1 [find_e1 morePrecise_res]]]].
    repeat split; try eauto.
  - destruct check_top as [valid_e1 [valid_e2 validJoin]];
      repeat split; try eauto.
    destruct validJoin as [m2 [find_m1 [find_n [find_m2 join_true]]]].
    pose proof (maps_mono e1 m find_m1) as find_m_map2;
      pose proof (maps_mono (Var Q n) m find_n) as find_mx_map2;
      pose proof (maps_mono e2 m2 find_m2) as find_m2_map2.
    eauto.
    (*
  - destruct check_top as [valid_e1 [valid_e2  [valid_e3 validJoin]]];
      repeat split; try eauto.
    destruct validJoin as [m1 [m2 [m3 [find_m1 [find_m2 [find_m3 join_true]]]]]].
    pose proof (maps_mono e1 m1 find_m1) as find_m1_map2;
      pose proof (maps_mono e2 m2 find_m2) as find_m2_map2;
      pose proof (maps_mono e3 m3 find_m3) as find_m3_map2.
    repeat eexists; eauto.
*)
Qed.

Lemma validTypes_eq_compat e1:
  forall e2 Gamma,
    Q_orderedExps.compare e1 e2 = Eq ->
    validTypes e1 Gamma ->
    validTypes e2 Gamma.
Proof.
  induction e1; intros e2 Gamma eq_exp valid_e1;
    cbn in valid_e1;
  pose proof eq_exp as eq_clone; destruct e2; cbn in eq_exp; try congruence.
  - destruct valid_e1 as [mG [find_mG [_ valid_exec]]].
    cbn.
    exists mG. repeat split; try auto.
    + erewrite <- SnapvMapFacts.P.F.find_o; eauto.
    + intros. eapply valid_exec; eauto.
      pose proof (expr_compare_eq_eval_compat (Var Q n) (Var Q n0)) as exp_eq.
      simpl in *.
      rewrite <- exp_eq in H0; eauto.
  - destruct valid_e1 as [mG [find_mG [tEq valid_exec]]].
    subst; cbn.
    destruct (mTypeEq mG m0) eqn:?; try congruence; type_conv; subst.
    + exists m0; repeat split; try auto.
      * erewrite <- SnapvMapFacts.P.F.find_o; eauto; cbn.
      * intros.
        pose proof (expr_compare_eq_eval_compat (Const m0 v) (Const m0 v0)).
        simpl in *.
        rewrite <- H1 in H0; eauto.
    + destruct (morePrecise mG m0) eqn:?; destruct mG; destruct m0; try congruence.
      * destruct (w ?= w0)%positive eqn:?; try congruence.
        destruct (f ?= f0)%N eqn:?; try congruence.
        apply Pos.compare_eq in Heqc; subst.
        apply N.compare_eq in Heqc0; subst; congruence.
      * destruct (w ?= w0)%positive eqn:?; try congruence.
        destruct (f ?= f0)%N eqn:?; try congruence.
        apply Pos.compare_eq in Heqc; subst.
        apply N.compare_eq in Heqc0; subst; congruence.
  - destruct (unopEq u u0) eqn:?; [ | destruct (unopEq u Neg) eqn:?; congruence ].
    destruct valid_e1 as [mG [find_mG [[valid_e1 [? ?]] valid_exec]]].
    specialize (IHe1 _ _ eq_exp valid_e1).
    rewrite unopEq_compat_eq in Heqb; subst.
    erewrite SnapvMapFacts.P.F.find_o with (y:=Unop u0 e2) in find_mG; eauto.
    exists mG; repeat split; try auto.
    + destruct H. eexists; split; try eauto.
      erewrite <- SnapvMapFacts.P.F.find_o; eauto.
    + intros.
      pose proof (expr_compare_eq_eval_compat (Unop u0 e1) (Unop u0 e2)).
      simpl in *; rewrite <- H2 in H1; eauto.
  - destruct valid_e1 as [mG [find_mG [[valid_esub1 [valid_esub2 join_valid]] valid_exec]]].
    assert (b = b0) by (destruct b; destruct b0; cbn in *; congruence).
    subst.
    assert (Q_orderedExps.exprCompare e1_1 e2_1 = Eq)
      as eq_rec1
      by (destruct b0; try congruence;
          destruct (Q_orderedExps.exprCompare e1_1 e2_1) eqn:?; try congruence).
    rewrite eq_rec1 in *.
    assert (Q_orderedExps.exprCompare e1_2 e2_2 = Eq)
      as eq_rec2
        by (destruct b0; try congruence; auto).
    clear eq_exp.
    specialize (IHe1_1 _ _ eq_rec1 valid_esub1).
    specialize (IHe1_2 _ _ eq_rec2 valid_esub2).
    erewrite SnapvMapFacts.P.F.find_o in find_mG; try eauto.
    destruct join_valid as [? [? [find_e11 [find_e12 join_valid]]]].
    erewrite SnapvMapFacts.P.F.find_o in find_e11,find_e12; eauto.
    exists mG; repeat split; try eauto.
    intros.
    pose proof (expr_compare_eq_eval_compat (Binop b0 e1_1 e1_2) (Binop b0 e2_1 e2_2));
      simpl in *.
    rewrite <- H1 in H0; eauto.
  - assert (Q_orderedExps.exprCompare e1_1 e2_1 = Eq)
      as eq_rec1
        by (destruct (Q_orderedExps.exprCompare e1_1 e2_1) eqn:?; try congruence).
    rewrite eq_rec1 in *.
    assert (Q_orderedExps.exprCompare e1_2 e2_2 = Eq)
      as eq_rec2
        by (destruct (Q_orderedExps.exprCompare e1_2 e2_2) eqn:?; try congruence).
    rewrite eq_rec2 in *.
    assert (Q_orderedExps.exprCompare e1_3 e2_3 = Eq)
      as eq_rec3
        by (destruct (Q_orderedExps.exprCompare e1_3 e2_3) eqn:?; try congruence).
    clear eq_exp.
    destruct valid_e1 as
        [mG [find_mG [[valid_e1 [valid_e2 [valid_e3 validJoin]]] valid_exec]]].
    specialize (IHe1_1 _ _ eq_rec1 valid_e1).
    specialize (IHe1_2 _ _ eq_rec2 valid_e2).
    specialize (IHe1_3 _ _ eq_rec3 valid_e3).
    erewrite SnapvMapFacts.P.F.find_o in find_mG; try eauto.
    destruct validJoin as [? [? [? [find1 [find2 [find3 validJoin]]]]]].
    erewrite SnapvMapFacts.P.F.find_o in find1,find2, find3; eauto.
    exists mG; repeat split; try eauto.
    + repeat eexists; repeat split; eauto.
    + intros.
      pose proof (expr_compare_eq_eval_compat (Fma e1_1 e1_2 e1_3) (Fma e2_1 e2_2 e2_3)).
      simpl in *; rewrite <- H1 in H0; eauto.
  - destruct (mTypeEq m m0) eqn:?; type_conv; subst.
    + destruct valid_e1 as [mG [find_mG [[valid_e1 [t_eq upper_bound]] valid_exec]]].
      subst.
      specialize (IHe1 _ _ eq_exp valid_e1).
      erewrite SnapvMapFacts.P.F.find_o in find_mG; try eauto.
      destruct upper_bound as [? [find_e1 upperBound]].
      erewrite SnapvMapFacts.P.F.find_o in find_e1; try eauto.
      exists mG; repeat split; try eauto.
      intros.
      pose proof (expr_compare_eq_eval_compat (Downcast mG e1) (Downcast mG e2)).
      rewrite <- H1 in H0; eauto.
    + destruct (morePrecise m m0) eqn:?; destruct m; destruct m0; try congruence.
      * destruct (w ?= w0)%positive eqn:?; try congruence.
        destruct (f ?= f0)%N eqn:?; try congruence.
        apply Pos.compare_eq in Heqc; subst.
        apply N.compare_eq in Heqc0; subst; congruence.
      * destruct (w ?= w0)%positive eqn:?; try congruence.
        destruct (f ?= f0)%N eqn:?; try congruence.
        apply Pos.compare_eq in Heqc; subst.
        apply N.compare_eq in Heqc0; subst; congruence.
        (*
  - destruct (mTypeEq m m0) eqn:?; try congruence; type_conv; subst.
    + assert (Q_orderedExps.exprCompare e1_1 e2_1 = Eq)
        as eq_rec1
          by (destruct (Q_orderedExps.exprCompare e1_1 e2_1) eqn:?; try congruence).
    rewrite eq_rec1 in *.
    assert (Q_orderedExps.exprCompare e1_2 e2_2 = Eq)
      as eq_rec2
        by (destruct (Q_orderedExps.exprCompare e1_2 e2_2) eqn:?; try congruence).
    rewrite eq_rec2 in *.
    clear eq_exp.
    destruct valid_e1 as
        [mG [find_mG [[valid_e1 [valid_e2 [valid_e3 validJoin]]] valid_exec]]].
    specialize (IHe1_1 _ _ eq_rec1 valid_e1).
    specialize (IHe1_2 _ _ eq_rec2 valid_e2).
    erewrite SnapvMapFacts.P.F.find_o in find_mG; try eauto.
    destruct validJoin as [find1 [findn [find2 validJoin]]].
    erewrite SnapvMapFacts.P.F.find_o in find1, findn, find2; eauto.
    exists mG; repeat split; try eauto.
    * repeat eexists; repeat split; eauto.
    * intros.
      pose proof (expr_compare_eq_eval_compat (Let _ _ e1_1 e1_2) (Let _ _ e2_1 e2_2)).
      simpl in *; rewrite <- H1 in H0; eauto.
         *)
  - assert (m = m0) as types_eq.
    { simpl in eq_clone.
      destruct (mTypeEq m m0) eqn:?.
      - type_conv; auto.
      - destruct (n ?= n0)%nat eqn:?; try congruence.
        destruct m; destruct m0; simpl in *; try congruence.
        + destruct (w ?= w0)%positive eqn:?; try congruence.
          apply Pos.compare_eq in Heqc0; subst.
          apply N.compare_eq in eq_clone; subst; auto.
    }
    subst. rewrite mTypeEq_refl in *.
    assert (n = n0 /\ Q_orderedExps.exprCompare e1_1 e2_1 = Eq /\
            Q_orderedExps.exprCompare e1_2 e2_2 = Eq)%nat.
    { destruct (n ?= n0)%nat eqn:?; try congruence.
      apply Nat.compare_eq in Heqc; split; try auto.
      destruct (Q_orderedExps.exprCompare e1_1 e2_1) eqn:?; try congruence.
      split; auto. }
    destruct H as [? [eq_rec1 eq_rec2]].
    subst; cbn.
    destruct valid_e1 as
        [mG [find_mG [[valid_e1 [valid_e2 find_e1]] ?]]].
    exists mG. repeat split.
    + erewrite SnapvMapFacts.P.F.find_o in find_mG; try eauto.
    + eapply IHe1_1; auto.
    + eapply IHe1_2; auto.
    + destruct find_e1 as [? [? [? [? ?]]]].
      exists x. repeat split; try auto.
      * erewrite SnapvMapFacts.P.F.find_o in H0; try eauto.
      * erewrite SnapvMapFacts.P.F.find_o in H2; try eauto.
    + intros.
      eapply H; eauto.
      pose proof (expr_compare_eq_eval_compat (Let m0 n0 e1_1 e1_2) (Let m0 n0 e2_1 e2_2)).
      cbn in *.
      rewrite mTypeEq_refl in *. rewrite Nat.compare_refl in *.
      rewrite eq_rec1 in *. rewrite eq_rec2 in *.
      rewrite <- H2 in H1; eauto.
      (*
  - assert (Q_orderedExps.exprCompare e1_1 e2_1 = Eq)
      as eq_rec1
        by (destruct (Q_orderedExps.exprCompare e1_1 e2_1) eqn:?; try congruence).
    rewrite eq_rec1 in *.
    assert (Q_orderedExps.exprCompare e1_2 e2_2 = Eq)
      as eq_rec2
        by (destruct (Q_orderedExps.exprCompare e1_2 e2_2) eqn:?; try congruence).
    rewrite eq_rec2 in *.
    assert (Q_orderedExps.exprCompare e1_3 e2_3 = Eq)
      as eq_rec3
        by (destruct (Q_orderedExps.exprCompare e1_3 e2_3) eqn:?; try congruence).
    clear eq_exp.
    destruct valid_e1 as
        [mG [find_mG [[valid_e1 [valid_e2 [valid_e3 validJoin]]] valid_exec]]].
    specialize (IHe1_1 _ _ eq_rec1 valid_e1).
    specialize (IHe1_2 _ _ eq_rec2 valid_e2).
    specialize (IHe1_3 _ _ eq_rec3 valid_e3).
    erewrite SnapvMapFacts.P.F.find_o in find_mG; try eauto.
    destruct validJoin as [? [? [? [find1 [find2 [find3 validJoin]]]]]].
    erewrite SnapvMapFacts.P.F.find_o in find1,find2, find3; eauto.
    exists mG; repeat split; try eauto.
    + repeat eexists; repeat split; eauto.
    + intros.
      pose proof (expr_compare_eq_eval_compat (Cond e1_1 e1_2 e1_3) (Cond e2_1 e2_2 e2_3)).
      simpl in *; rewrite <- H1 in H0; eauto.
*)
Qed.

Lemma map_find_mono e1 e2 m1 m2 Gamma :
  SnapvMap.mem e2 Gamma = false ->
  SnapvMap.find (elt:=mType) e1 Gamma = Some m1 ->
  SnapvMap.find (elt:=mType) e1 (SnapvMap.add e2 m2 Gamma) = Some m1.
Proof.
  intros * no_mem find_Gamma.
  rewrite map_find_add.
  destruct (Q_orderedExps.compare e2 e1) eqn:?; try auto.
  rewrite SnapvMapFacts.P.F.mem_find_b in no_mem.
  erewrite <- SnapvMapFacts.P.F.find_o in find_Gamma; eauto.
  rewrite find_Gamma in no_mem; congruence.
Qed.

Corollary getValidMap_top_contained e:
  forall akk Gamma res,
    getValidMap Gamma e akk = Succes res ->
    SnapvMap.mem e res = true.
Proof.
  pose (eT := e);
    induction e; intros * validMap; cbn in validMap;
      destruct (SnapvMap.mem eT akk) eqn:case_akk;
      subst eT; rewrite case_akk in *;
        try (inversion validMap; subst; now auto);
        Snapv_compute;
        repeat (match goal with
                | [H : context [ if ?c then _ else _] |- _] =>
                  destruct c; try congruence; inversion H; subst end);
        unfold addMono in * |- ; Snapv_compute; inversion validMap; subst;
          try rewrite map_mem_add;
          unfold Q_orderedExps.compare; try rewrite Q_orderedExps.exprCompare_refl;
            auto.
Qed.

Theorem getValidMap_correct e:
  forall (Gamma akk:SnapvMap.t mType) res,
    (forall e,
        SnapvMap.mem e akk = true ->
        validTypes e akk) ->
    getValidMap Gamma e akk = Succes res ->
    forall e, SnapvMap.mem e res = true ->
    validTypes e res.
Proof.
  pose (eT := e);
    induction e ; intros Gamma akk res akk_sound validMap_succ;
    destruct (SnapvMap.mem eT akk) eqn:Hmem; subst;
      cbn in validMap_succ; subst eT;
        rewrite Hmem in *; try (inversion validMap_succ; subst; eapply akk_sound; now eauto).
  - Snapv_compute; simpl.
    inversion validMap_succ; subst.
    intros * mem_add.
    rewrite map_mem_add in mem_add.
    destruct (Q_orderedExps.compare (Var Q n) e) eqn:?;
             try (eapply validTypes_mono with (map1 := akk);
                  now eauto using map_find_mono).
    eapply validTypes_eq_compat; eauto.
    eexists; split; [eauto using tMap_def | split; try auto].
    intros * map_mono eval_var.
    inversion eval_var; subst.
    assert (SnapvMap.find (Var Q n) (SnapvMap.add (Var Q n) m akk) = Some m)
      by (eauto using tMap_def).
    pose proof (map_mono _ _ H) as find_Gamma2.
    assert (toRExpMap Gamma2 (Var R n)  = Some m).
    { eapply toRExpMap_some; eauto; simpl; auto. }
    congruence.
  - destruct (isMonotone (SnapvMap.find (elt:=mType) (Const m v) Gamma) m) eqn:?;
             [ | congruence].
    inversion validMap_succ; subst.
    intros * mem_add.
    rewrite map_mem_add in mem_add.
    destruct (Q_orderedExps.compare (Const m v) e) eqn:?;
             try (eapply validTypes_mono with (map1 := akk) ; now eauto using map_find_mono).
    eapply validTypes_eq_compat; eauto.
    eexists; split; [eauto using tMap_def | split; try auto].
    intros * map_mono eval_const; inversion eval_const; subst; auto.
  - destruct (getValidMap Gamma e akk) eqn:?; simpl in *; try congruence.
    destruct (SnapvMap.find (elt:=mType) e t) eqn:?; simpl in *;
             try congruence.
    intros * mem_add.
    assert (forall e, SnapvMap.mem e t = true -> validTypes e t) as valid_rec.
    { eapply IHe; eauto. }
    destruct (isFixedPointB m) eqn:?.
    + Snapv_compute.
      destruct (isCompat m m0) eqn:?; try congruence.
      unfold addMono in *; Snapv_compute.
      inversion validMap_succ; subst.
      assert (SnapvMap.mem (Unop u e) t = false)
             by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo1; eauto).
      rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Unop u e) e0) eqn:?;
             try (eapply validTypes_mono with (map1 := t);
                  now eauto using map_find_mono).
      eapply validTypes_eq_compat; eauto.
      exists m0; repeat split; eauto using tMap_def.
      * assert (SnapvMap.mem e t = true)
               by  (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo; eauto).
        eapply validTypes_mono with (map1:= t); eauto using map_find_mono.
      * exists m; split; try auto.
        eapply map_find_mono; try auto.
      * intros * map_mono eval_unop.
        assert (SnapvMap.find (elt:=mType) (Unop u e) (SnapvMap.add (Unop u e) m0 t) = Some m0)
          as find_unop_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_unop_t).
        assert (toRExpMap Gamma2 (toRExp (Unop u e)) = Some m0)
          by (eapply toRExpMap_some; eauto).
        inversion eval_unop; subst; simpl in *; congruence.
    + destruct (isMonotone (SnapvMap.find (elt:=mType) (Unop u e) Gamma) m) eqn:?;
               try congruence.
      unfold addMono in *; simpl in *.
      Snapv_compute.
      inversion validMap_succ; subst.
      assert (SnapvMap.mem (Unop u e) t = false)
             by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; eauto).
      rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Unop u e) e0) eqn:?;
             try (eapply validTypes_mono with (map1 := t);
                  now eauto using map_find_mono).
      eapply validTypes_eq_compat; eauto.
      exists m; repeat split; try eauto using tMap_def.
      * assert (SnapvMap.mem e t = true)
               by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo; auto).
        eapply (validTypes_mono _) with (map1:= t); eauto using map_find_mono.
      * exists m; split.
        { eapply map_find_mono; auto. }
        { unfold isCompat; destruct m; auto using morePrecise_refl. }
      * intros * map_mono eval_unop.
        assert (SnapvMap.find (elt:=mType) (Unop u e) (SnapvMap.add (Unop u e) m t) = Some m)
          by (eauto using tMap_def).
        pose proof (map_mono _ _ H0).
        assert (toRExpMap Gamma2 (toRExp (Unop u e)) = Some m)
          by (eapply toRExpMap_some; eauto).
        inversion eval_unop; subst; simpl in *; congruence.
  - destruct (getValidMap Gamma e1 akk) eqn:?; cbn in *; try congruence.
    destruct (getValidMap Gamma e2 t) eqn:?; cbn in *; try congruence.
    destruct (SnapvMap.find (elt:=mType) e1 t0) eqn:e1_find; try congruence.
    destruct (SnapvMap.find (elt:=mType) e2 t0) eqn:e2_find; try congruence.
    assert (forall e, SnapvMap.mem e t = true -> validTypes e t).
    { eapply IHe1; eauto. }
    assert (forall e, SnapvMap.mem e t0 = true -> validTypes e t0)
    as valid_akk_sub.
    { eapply IHe2; eauto. }
    assert (validTypes e1 t0).
    { assert (SnapvMap.mem e1 t0 = true)
        by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite e1_find; eauto).
      eauto. }
    assert (validTypes e2 t0).
    { assert (SnapvMap.mem e2 t0 = true)
          by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite e2_find; eauto).
         eauto. }
    destruct (isFixedPointB m && isFixedPointB m0) eqn:?.
    + Snapv_compute.
      destruct (morePrecise m m1 && morePrecise m0 m1) eqn:?; try congruence.
      andb_to_prop Heqb0.
      unfold addMono in *.
      Snapv_compute.
      inversion validMap_succ; subst.
      assert (SnapvMap.mem (Binop b e1 e2) t0 = false)
             by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; eauto).
      intros * mem_add;
        rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Binop b e1 e2) e) eqn:?;
               [ | eapply validTypes_mono with (map1 := t0);
                   now eauto using map_find_mono
                 | eapply validTypes_mono with (map1 := t0);
                   now eauto using map_find_mono ].
      apply validTypes_eq_compat with (e1:=Binop b e1 e2); auto.
       exists m1; repeat split; try auto using tMap_def.
      * eapply validTypes_mono with (map1:=t0); eauto using map_find_mono.
      * eapply validTypes_mono with (map1:=t0); eauto using map_find_mono.
      * exists m, m0. repeat split.
        { rewrite map_find_add.
          pose proof (no_cycle_binop_left e1 b e2).
          destruct (Q_orderedExps.compare (Binop b e1 e2) e1) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric.
          hnf in H4. specialize (H4 _ _ Heqc0).
          contradiction. }
        { rewrite map_find_add.
          pose proof (no_cycle_binop_right e2 b e1).
          destruct (Q_orderedExps.compare (Binop b e1 e2) e2) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric.
          hnf in H4. specialize (H4 _ _ Heqc0).
          contradiction. }
        { unfold isJoin; rewrite L,L0,R,R0; auto. }
      * intros * map_mono eval_binop.
        assert (SnapvMap.find (elt:=mType) (Binop b e1 e2)
                               (SnapvMap.add (Binop b e1 e2) m1 t0) = Some m1)
          as find_binop_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_binop_t).
        assert (toRExpMap Gamma2 (toRExp (Binop b e1 e2)) = Some m1)
          by (eapply toRExpMap_some; eauto).
        inversion eval_binop; subst; simpl in *; congruence.
  + destruct (join_fl m m0) eqn:?; try congruence.
    destruct (isMonotone (SnapvMap.find (elt:=mType) (Binop b e1 e2) Gamma) m1) eqn:?;
             try congruence.
    unfold addMono in *.
    Snapv_compute; try congruence.
    inversion validMap_succ; subst.
    assert (SnapvMap.mem (Binop b e1 e2) t0 = false)
      by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; eauto).
    intros * mem_add;
      rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Binop b e1 e2) e) eqn:?;
               [ | eapply validTypes_mono with (map1 := t0);
                   now eauto using map_find_mono
                 | eapply validTypes_mono with (map1 := t0);
                   now eauto using map_find_mono ].
      apply validTypes_eq_compat with (e1:=Binop b e1 e2); auto.
       exists m1; repeat split; try auto using tMap_def.
      * eapply validTypes_mono with (map1:=t0); eauto using map_find_mono.
      * eapply validTypes_mono with (map1:=t0); eauto using map_find_mono.
      * exists m, m0. repeat split.
        { rewrite map_find_add.
          pose proof (no_cycle_binop_left e1 b e2).
          destruct (Q_orderedExps.compare (Binop b e1 e2) e1) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric.
          hnf in H4. specialize (H4 _ _ Heqc0).
          contradiction. }
        { rewrite map_find_add.
          pose proof (no_cycle_binop_right e2 b e1).
          destruct (Q_orderedExps.compare (Binop b e1 e2) e2) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric.
          hnf in H4. specialize (H4 _ _ Heqc0).
          contradiction. }
        { unfold isJoin. rewrite Heqb0.  rewrite Heqo. apply mTypeEq_refl. }
      * intros * map_mono eval_binop.
        assert (SnapvMap.find (elt:=mType) (Binop b e1 e2)
                               (SnapvMap.add (Binop b e1 e2) m1 t0) = Some m1)
          as find_binop_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_binop_t).
        assert (toRExpMap Gamma2 (toRExp (Binop b e1 e2)) = Some m1)
          by (eapply toRExpMap_some; eauto).
        inversion eval_binop; subst; simpl in *; congruence.
  - destruct (getValidMap Gamma e1 akk) eqn:?; cbn in *; try congruence.
    destruct (getValidMap Gamma e2 t) eqn:?; cbn in *; try congruence.
    destruct (getValidMap Gamma e3 t0) eqn:?; cbn in *; try congruence.
    destruct (SnapvMap.find (elt:=mType) e1 t1) eqn:e1_find; try congruence.
    destruct (SnapvMap.find (elt:=mType) e2 t1) eqn:e2_find; try congruence.
    destruct (SnapvMap.find (elt:=mType) e3 t1) eqn:e3_find; try congruence.
    assert (forall e, SnapvMap.mem e t = true -> validTypes e t).
    { eapply IHe1; eauto. }
    assert (forall e, SnapvMap.mem e t0 = true -> validTypes e t0).
    { eapply IHe2; eauto. }
    assert (forall e, SnapvMap.mem e t1 = true -> validTypes e t1).
    { eapply IHe3; eauto. }
    assert (validTypes e1 t1).
    { assert (SnapvMap.mem e1 t1 = true)
        by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite e1_find; eauto).
      eauto. }
    assert (validTypes e2 t1).
    { assert (SnapvMap.mem e2 t1 = true)
          by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite e2_find; eauto).
         eauto. }
    assert (validTypes e3 t1).
    { assert (SnapvMap.mem e3 t1 = true)
          by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite e3_find; eauto).
         eauto. }
    destruct (isFixedPointB m && isFixedPointB m0 && isFixedPointB m1) eqn:?.
    + Snapv_compute.
      destruct (morePrecise m m2 && morePrecise m0 m2 && morePrecise m1 m2) eqn:?;
               try congruence.
      unfold addMono in *; Snapv_compute.
      inversion validMap_succ; subst.
      assert (SnapvMap.mem (Fma e1 e2 e3) t1 = false)
      by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; eauto).
      intros * mem_add;
        rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Fma e1 e2 e3) e) eqn:?;
               [ | eapply validTypes_mono with (map1 := t1); now eauto using map_find_mono
                 | eapply validTypes_mono with (map1 := t1); now eauto using map_find_mono].
      apply validTypes_eq_compat with (e1:=Fma e1 e2 e3); auto.
      exists m2; repeat split; try auto using tMap_def.
      * apply validTypes_mono with (map1:=t1); eauto using map_find_mono.
      * apply validTypes_mono with (map1:=t1); eauto using map_find_mono.
      * apply validTypes_mono with (map1:=t1); eauto using map_find_mono.
      * exists m, m0, m1. repeat split.
        { rewrite map_find_add.
          pose proof (no_cycle_fma_left e1 e2 e3).
          destruct (Q_orderedExps.compare (Fma e1 e2 e3) e1) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction. }
        { rewrite map_find_add.
          pose proof (no_cycle_fma_center e2 e1 e3).
          destruct (Q_orderedExps.compare (Fma e1 e2 e3) e2) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction. }
        { rewrite map_find_add.
          pose proof (no_cycle_fma_right e3 e1 e2).
          destruct (Q_orderedExps.compare (Fma e1 e2 e3) e3) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction. }
        { unfold isJoin3. rewrite L0, L1, R, R0, R1, R2. auto. }
      * intros * map_mono eval_fma.
        assert (SnapvMap.find (elt:=mType) (Fma e1 e2 e3)
                               (SnapvMap.add (Fma e1 e2 e3) m2 t1) = Some m2)
          as find_fma_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_fma_t).
        assert (toRExpMap Gamma2 (toRExp (Fma e1 e2 e3)) = Some m2)
          by (eapply toRExpMap_some; eauto).
        inversion eval_fma; subst; simpl in *; congruence.
    + destruct (join_fl3 m m0 m1) eqn:?; try congruence.
      destruct (isMonotone (SnapvMap.find (elt:=mType) (Fma e1 e2 e3) Gamma) m2) eqn:?;
               try congruence.
      unfold addMono in *; Snapv_compute.
      inversion validMap_succ.
      assert (SnapvMap.mem (Fma e1 e2 e3) t1 = false)
             by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; auto).
      intros * mem_add;
        rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Fma e1 e2 e3) e) eqn:?;
               [ | eapply validTypes_mono with (map1 := t1); now eauto using map_find_mono
                 | eapply validTypes_mono with (map1 := t1); now eauto using map_find_mono].
      apply validTypes_eq_compat with (e1:=Fma e1 e2 e3); auto.
      exists m2; repeat split; try auto using tMap_def.
      * apply validTypes_mono with (map1:=t1); eauto using map_find_mono.
      * apply validTypes_mono with (map1:=t1); eauto using map_find_mono.
      * apply validTypes_mono with (map1:=t1); eauto using map_find_mono.
      * exists m, m0, m1. repeat split.
        { rewrite map_find_add.
          pose proof (no_cycle_fma_left e1 e2 e3).
          destruct (Q_orderedExps.compare (Fma e1 e2 e3) e1) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction. }
        { rewrite map_find_add.
          pose proof (no_cycle_fma_center e2 e1 e3).
          destruct (Q_orderedExps.compare (Fma e1 e2 e3) e2) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction. }
        { rewrite map_find_add.
          pose proof (no_cycle_fma_right e3 e1 e2).
          destruct (Q_orderedExps.compare (Fma e1 e2 e3) e3) eqn:?; try congruence.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction. }
        { unfold isJoin3.
          unfold join_fl3 in *.
          rewrite Heqb. destruct (join_fl m0 m1) eqn:?; simpl in *; try congruence.
          rewrite Heqo. apply mTypeEq_refl. }
      * intros * map_mono eval_fma.
        assert (SnapvMap.find (elt:=mType) (Fma e1 e2 e3)
                               (SnapvMap.add (Fma e1 e2 e3) m2 t1) = Some m2)
          as find_fma_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_fma_t).
        assert (toRExpMap Gamma2 (toRExp (Fma e1 e2 e3)) = Some m2)
          by (eapply toRExpMap_some; eauto).
        inversion eval_fma; subst; simpl in *; congruence.
  - destruct (getValidMap Gamma e akk) eqn:?; cbn in validMap_succ; try congruence.
    assert (forall e, SnapvMap.mem e t = true -> validTypes e t).
    { eapply IHe; eauto. }
    destruct (SnapvMap.find e t) eqn:e_find; try congruence.
    assert (validTypes e t).
    { assert (SnapvMap.mem e t = true)
        by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite e_find; eauto).
      eauto. }
    destruct (isFixedPointB m0) eqn:?.
    + Snapv_compute.
      destruct (mTypeEq m m1 && morePrecise m0 m1) eqn:type_ok; try congruence;
        andb_to_prop type_ok; type_conv; subst.
      unfold addMono in *; Snapv_compute.
      assert (SnapvMap.mem (Downcast m1 e) t = false)
        by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; auto).
      inversion validMap_succ; subst.
      intros * mem_add. rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Downcast m1 e) e0) eqn:?;
               [ | eapply validTypes_mono with (map1:=t);
                   now eauto using map_find_mono
                 | eapply validTypes_mono with (map1:=t);
                 now eauto using map_find_mono].
      eapply validTypes_eq_compat; eauto.
      exists m1; repeat split; auto using tMap_def.
      * eapply validTypes_mono with (map1:=t); eauto using map_find_mono.
      * exists m0. rewrite map_find_add.
        pose proof (no_cycle_cast e m1).
        rewrite isMorePrecise_morePrecise.
        destruct (Q_orderedExps.compare (Downcast m1 e) e) eqn:?; split; try eauto.
          pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
          hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
          contradiction.
      * intros * map_mono eval_cast.
        assert (SnapvMap.find (elt:=mType) (Downcast m1 e)
                               (SnapvMap.add (Downcast m1 e) m1 t) = Some m1)
          as find_cast_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_cast_t).
        assert (toRExpMap Gamma2 (toRExp (Downcast m1 e)) = Some m1)
          by (eapply toRExpMap_some; eauto).
        inversion eval_cast; subst; simpl in *; congruence.
    + destruct (morePrecise m0 m &&
                            isMonotone (SnapvMap.find (Downcast m e) Gamma) m) eqn:?;
               try congruence.
      unfold addMono in *; Snapv_compute.
      assert (SnapvMap.mem (Downcast m e) t = false)
        by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo; auto).
      inversion validMap_succ; subst.
      intros * mem_add. rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Downcast m e) e0) eqn:?;
               [ | eapply validTypes_mono with (map1:=t);
                   now eauto using map_find_mono
                 | eapply validTypes_mono with (map1:=t);
                 now eauto using map_find_mono].
      eapply validTypes_eq_compat; eauto.
      exists m; repeat split; auto using tMap_def.
      * eapply validTypes_mono with (map1:=t); eauto using map_find_mono.
      * exists m0. rewrite map_find_add.
        pose proof (no_cycle_cast e m).
        rewrite isMorePrecise_morePrecise,L.
        destruct (Q_orderedExps.compare (Downcast m e) e) eqn:?; split; try eauto.
        pose proof SnapvMapFacts.P.F.KeySetoid_Symmetric as cmp_sym.
        hnf in cmp_sym. specialize (cmp_sym _ _ Heqc0).
        contradiction.
      * intros * map_mono eval_cast.
        assert (SnapvMap.find (elt:=mType) (Downcast m e)
                               (SnapvMap.add (Downcast m e) m t) = Some m)
          as find_cast_t
            by (eauto using tMap_def).
        pose proof (map_mono _ _ find_cast_t).
        assert (toRExpMap Gamma2 (toRExp (Downcast m e)) = Some m)
          by (eapply toRExpMap_some; eauto).
        inversion eval_cast; subst; simpl in *; congruence.
  - destruct (getValidMap Gamma e1 akk) eqn:?; simpl in validMap_succ;
      try congruence.
    destruct (SnapvMap.find e1 t) eqn:?; try congruence.
    destruct (mTypeEq m m0) eqn:?; try congruence.
    type_conv; subst.
    unfold addMono in validMap_succ.
    destruct (SnapvMap.find (Var Q n) t) eqn:?; simpl in *; try congruence.
    assert (SnapvMap.mem (Var Q n) t = false)
      by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; auto).
    destruct (getValidMap Gamma e2 (SnapvMap.add (Var Q n) m0 t)) eqn:?;
             simpl in *; try congruence.
    specialize (IHe1 _ _ _ akk_sound Heqr).
    specialize (IHe2 Gamma (SnapvMap.add (Var Q n) m0 t) t0).
    assert (forall e, SnapvMap.mem e t0 = true -> validTypes e t0).
    { apply IHe2; try auto.
      intros * mem_add.
      apply mem_add_cases in mem_add.
      destruct mem_add as [? | [? ?]].
      - eapply validTypes_eq_compat with (e1 := Var Q n); try eauto.
        + apply Q_orderedExps.eq_sym; auto.
        + simpl. exists m0; split.
          * rewrite map_find_add. unfold Q_orderedExps.compare.
            now rewrite SnapvMap.E.eq_refl.
          * split; [easy | ].
            intros * map_sound eval_var.
            inversion eval_var; subst.
            specialize (map_sound (Var Q n) m0).
            change (Var R n) with (toRExp (Var Q n)) in *.
            eapply toRExpMap_find_map in H2.
            rewrite map_sound in H2; try congruence.
            rewrite map_find_add. unfold Q_orderedExps.compare.
            now rewrite SnapvMap.E.eq_refl.
    - apply validTypes_mono with (map1 := t) ; eauto.
      intros * in_t.
      rewrite map_find_add.
      destruct (Q_orderedExps.compare (Var Q n) e0) eqn:?; try auto.
      rewrite SnapvMapFacts.P.F.mem_find_b in *.
      erewrite <- SnapvMapFacts.P.F.find_o in in_t; eauto.
      congruence. }
    destruct (SnapvMap.find e2 t0) eqn:?; simpl in *; try congruence.
    assert (validTypes e1 t0) as valid_e1_t0.
    { assert (SnapvMap.mem e1 t = true)
        by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo; eauto).
      assert (SnapvMap.mem e1 (SnapvMap.add (Var Q n) m0 t) = true).
      { rewrite map_mem_add. destruct (Q_orderedExps.compare (Var Q n) e1); auto. }
      pose proof (getValidMap_mono _ _ _ Heqr0).
      apply H0.
      rewrite SnapvMapFacts.P.F.mem_find_b in *.
      destruct (SnapvMap.find e1 (SnapvMap.add (Var Q n) m0 t)) eqn:?; try congruence.
      erewrite H3; eauto. }
    assert (validTypes e2 t0) as valid_e2_t0.
    { assert (SnapvMap.mem e2 t0 = true)
          by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo1; eauto).
         eauto. }
    assert (isMonotone (SnapvMap.find (Let m0 n e1 e2) Gamma) m = true) as isMono.
    { Snapv_compute; unfold isMonotone; try auto.
      - destruct (mTypeEq m1 m); congruence.
      - destruct (mTypeEq m1 m); congruence. }
    rewrite isMono in *.
    destruct (isFixedPointB m) eqn:?; simpl in *.
    + Snapv_compute. inversion validMap_succ; subst.
      intros. apply mem_add_cases in H1.
      destruct H1 as [? | [? ?]].
      * eapply validTypes_eq_compat with (e1 := (Let m0 n e1 e2)); try eauto.
        { apply Q_orderedExps.eq_sym; auto. }
        { simpl. exists m1; split.
          - rewrite map_find_add. unfold Q_orderedExps.compare.
            now rewrite SnapvMap.E.eq_refl.
          - repeat split.
            + eapply validTypes_mono with (map1 := t0); try auto.
              intros; eapply map_find_mono; auto.
              rewrite SnapvMapFacts.P.F.mem_find_b.
              rewrite Heqo3; auto.
            + eapply validTypes_mono with (map1 := t0).
              * intros; eapply map_find_mono; try auto.
                rewrite SnapvMapFacts.P.F.mem_find_b.
                rewrite Heqo3; auto.
              * apply H0.
                eapply getValidMap_top_contained; eauto.
            + exists m. repeat split; try auto.
              * assert (SnapvMap.find e1 (SnapvMap.add (Var Q n) m0 t) = Some m0).
                { rewrite map_find_add.
                  destruct (Q_orderedExps.compare (Var Q n) e1); auto. }
                eapply (getValidMap_mono _ _ _ Heqr0) in H2; eauto.
                rewrite map_find_add.
                rewrite Q_orderedExps.exprCompare_antisym.
                pose proof (no_cycle_let_left e1 e2 n m0).
                destruct (Q_orderedExps.exprCompare e1 (Let m0 n e1 e2)) eqn:?;
                         simpl in *; try congruence.
                contradiction.
              * assert (SnapvMap.find (Var Q n) (SnapvMap.add (Var Q n) m0 t) = Some m0).
                { rewrite map_find_add, Q_orderedExps.exprCompare_refl; auto. }
                eapply (getValidMap_mono _ _ _ Heqr0) in H2; eauto.
                rewrite map_find_add. cbn; auto.
              * rewrite map_find_add.
                pose proof (no_cycle_let_right e2 e1 n m0).
                rewrite Q_orderedExps.exprCompare_antisym.
                destruct (Q_orderedExps.exprCompare e2 (Let m0 n e1 e2)) eqn:?;
                         simpl in *; try congruence.
                contradiction.
              * unfold isMonotone in *. type_conv.
                unfold isCompat; destruct m; auto using morePrecise_refl.
            + intros * map_sound eval_let.
              inversion eval_let; subst.
              specialize (map_sound (Let m0 n e1 e2) m1).
              change (Let m0 n (toRExp e1) (toRExp e2))
                with (toRExp (Let m0 n e1 e2)) in *.
              eapply toRExpMap_find_map in H8.
              rewrite map_sound in H8; try congruence.
              rewrite map_find_add. unfold Q_orderedExps.compare.
              now rewrite SnapvMap.E.eq_refl. }
      * apply validTypes_mono with (map1 := t0) ; eauto.
         { intros * in_t.
           rewrite map_find_add.
           destruct (Q_orderedExps.compare (Let m0 n e1 e2) e0) eqn:?; try auto.
           - rewrite SnapvMapFacts.P.F.mem_find_b in *.
             erewrite <- SnapvMapFacts.P.F.find_o in in_t; eauto.
             congruence. }
    + intros. Snapv_compute. inversion validMap_succ; subst.
      apply mem_add_cases in H1.
      destruct H1 as [? | [? ?]].
      * eapply validTypes_eq_compat with (e1 := (Let m0 n e1 e2)); try eauto.
        { apply Q_orderedExps.eq_sym; auto. }
        { simpl. exists m; split.
          - rewrite map_find_add. unfold Q_orderedExps.compare.
            now rewrite SnapvMap.E.eq_refl.
          - repeat split.
            + eapply validTypes_mono with (map1 := t0); try auto.
              intros; eapply map_find_mono; auto.
              rewrite SnapvMapFacts.P.F.mem_find_b.
              rewrite Heqo2; auto.
            + eapply validTypes_mono with (map1 := t0).
              * intros; eapply map_find_mono; try auto.
                rewrite SnapvMapFacts.P.F.mem_find_b.
                rewrite Heqo2; auto.
              * apply H0.
                eapply getValidMap_top_contained; eauto.
            + exists m. repeat split; try auto.
              * assert (SnapvMap.find e1 (SnapvMap.add (Var Q n) m0 t) = Some m0).
                { rewrite map_find_add.
                  destruct (Q_orderedExps.compare (Var Q n) e1); auto. }
                eapply (getValidMap_mono _ _ _ Heqr0) in H2; eauto.
                rewrite map_find_add.
                rewrite Q_orderedExps.exprCompare_antisym.
                pose proof (no_cycle_let_left e1 e2 n m0).
                destruct (Q_orderedExps.exprCompare e1 (Let m0 n e1 e2)) eqn:?;
                         simpl in *; try congruence.
                contradiction.
              * assert (SnapvMap.find (Var Q n) (SnapvMap.add (Var Q n) m0 t) = Some m0).
                { rewrite map_find_add, Q_orderedExps.exprCompare_refl; auto. }
                eapply (getValidMap_mono _ _ _ Heqr0) in H2; eauto.
                rewrite map_find_add. cbn; auto.
              * rewrite map_find_add.
                pose proof (no_cycle_let_right e2 e1 n m0).
                rewrite Q_orderedExps.exprCompare_antisym.
                destruct (Q_orderedExps.exprCompare e2 (Let m0 n e1 e2)) eqn:?;
                         simpl in *; try congruence.
            + intros * map_sound eval_let.
              inversion eval_let; subst.
              specialize (map_sound (Let m0 n e1 e2) m).
              change (Let m0 n (toRExp e1) (toRExp e2))
                with (toRExp (Let m0 n e1 e2)) in *.
              eapply toRExpMap_find_map in H8.
              rewrite map_sound in H8; try congruence.
              rewrite map_find_add. unfold Q_orderedExps.compare.
              now rewrite SnapvMap.E.eq_refl. }
      * apply validTypes_mono with (map1 := t0) ; eauto.
         { intros * in_t.
           rewrite map_find_add.
           destruct (Q_orderedExps.compare (Let m0 n e1 e2) e0) eqn:?; try auto.
           - rewrite SnapvMapFacts.P.F.mem_find_b in *.
             erewrite <- SnapvMapFacts.P.F.find_o in in_t; eauto.
             congruence. }
Qed.

Corollary getValidMap_top_correct e:
  forall akk Gamma res,
    (forall e, SnapvMap.mem e akk = true ->
          validTypes e akk) ->
    getValidMap Gamma e akk = Succes res ->
    validTypes e res.
Proof.
  intros * akk_sound validMap.
  pose proof (getValidMap_correct _ _ _ akk_sound validMap) as all_sound.
  pose proof (getValidMap_top_contained _ _ _ validMap).
  eauto.
Qed.

(*
Lemma getValidMapCmd_mono f:
  forall Gamma akk res,
    getValidMapCmd Gamma f akk = Succes res ->
    forall e m, SnapvMap.find e akk = Some m ->
           SnapvMap.find e res = Some m.
Proof.
  induction f; intros * getMap_succeeds * mem_akk.
  - cbn in getMap_succeeds.
    destruct (getValidMap Gamma e akk) eqn:?; simpl in getMap_succeeds;
      try congruence.
    destruct (SnapvMap.find e t) eqn:?; try congruence.
    destruct (mTypeEq m m1) eqn:?; try congruence.
    unfold addMono in *; Snapv_compute.
    specialize (IHf _ _ _ getMap_succeeds).
    eapply IHf.
    rewrite map_find_add.
    destruct (Q_orderedExps.compare (Var Q n) e0) eqn:?;
             try eauto using getValidMap_mono.
    assert (SnapvMap.find (Var Q n) akk = Some m0)
      as in_akk
        by (erewrite SnapvMapFacts.P.F.find_o; eauto).
    eapply getValidMap_mono in in_akk; eauto.
    congruence.
  - simpl in *. eapply getValidMap_mono; eauto.
Qed.

Theorem getValidMapCmd_correct f:
  forall Gamma akk res,
    (forall e, SnapvMap.mem e akk = true ->
          validTypes e akk) ->
    getValidMapCmd Gamma f akk = Succes res ->
    validTypesCmd f res /\
    (forall e, SnapvMap.mem e res = true ->
          validTypes e res).
Proof.
  induction f; intros * akk_sound getMap_succeeds;
    cbn in * |-.
  - destruct (getValidMap Gamma e akk) eqn:?; simpl in getMap_succeeds;
      try congruence.
    destruct (SnapvMap.find e t) eqn:?; try congruence.
    destruct (mTypeEq m m0) eqn:?; try congruence.
    pose proof (getValidMap_correct _ _ _ akk_sound Heqr) as t_sound.
    unfold addMono in getMap_succeeds; Snapv_compute.
    assert (SnapvMap.mem (Var Q n) t = false)
      by (rewrite SnapvMapFacts.P.F.mem_find_b; rewrite Heqo0; auto).
    specialize (IHf Gamma (SnapvMap.add (Var Q n) m t) res).
    destruct IHf as [valid_f valid_res]; try auto.
    + intros * mem_add.
      rewrite map_mem_add in mem_add.
      destruct (Q_orderedExps.compare (Var Q n) e0) eqn:?;
               [ | eapply validTypes_mono with (map1:= t);
                   eauto using getValidMap_correct, map_find_mono
                 | eapply validTypes_mono with (map1:= t);
                   eauto using getValidMap_correct, map_find_mono].
      eapply validTypes_eq_compat; eauto.
      exists m; repeat split; try eauto using tMap_def.
      intros * map_mono eval_var.
      assert (SnapvMap.find (Var Q n) (SnapvMap.add (Var Q n) m t) = Some m)
        by (eauto using tMap_def).
      pose proof (map_mono _ _ H0) as find_Gamma2.
      assert (toRExpMap Gamma2 (Var R n)  = Some m).
      { eapply toRExpMap_some; eauto; simpl; auto. }
      inversion eval_var; subst; congruence.
    + split; try auto.
      unfold validTypesCmd; split.
      * exists m0. repeat split; auto.
        { eapply getValidMapCmd_mono; eauto.
          rewrite map_find_add.
          destruct (Q_orderedExps.compare (Var Q n) e) eqn:?; try auto.
          erewrite <- SnapvMapFacts.P.F.find_o in Heqo; eauto.
          congruence. }
        { eapply getValidMapCmd_mono; eauto.
          rewrite map_find_add.
          unfold Q_orderedExps.compare;
            rewrite Q_orderedExps.exprCompare_refl; auto. }
        { eapply validTypes_mono with (map1:=SnapvMap.add (Var Q n) m t).
          - eapply getValidMapCmd_mono; eauto.
          - eapply validTypes_mono with (map1:=t); eauto using map_find_mono.
            eapply getValidMap_top_correct with (akk:=akk); eauto. }
      *  eapply validTypesCmd_single in valid_f.
         simpl.
         destruct (valid_f)
           as [mT [find_mT valid_exec]].
         exists mT; split; try auto.
         intros * map_mono bstep_let.
         inversion bstep_let; subst.
         eapply valid_exec; eauto.
  - simpl.
    pose proof (getValidMap_correct _ _ _ akk_sound getMap_succeeds)
      as valid_exp_types.
    pose proof (getValidMap_top_correct _ _ _ akk_sound getMap_succeeds) as valid_top.
    repeat split; try auto.
    eapply validTypes_single in valid_top.
    destruct valid_top as [mT [find_mT valid_exec]].
    exists mT; split; try auto.
    intros * map_mono valid_bstep.
    inversion valid_bstep; subst.
    eapply valid_exec; eauto.
Qed.
*)

(**
   This file contains the coq implementation of the error bound validator as
   well as its soundness proof. The function validErrorbound is the Error bound
   validator from the certificate checking process. Under the assumption that a
   valid range arithmetic result has been computed, it can validate error bounds
   encoded in the analysis result. The validator is used in the file
   CertificateChecker.v to build the complete checker.
 **)
From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Recdef Reals.Reals.

From Flover
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis ErrorValidationAAutil
     ExpressionSemantics IntervalValidation TypeValidator RealRangeValidator ErrorBounds
     ErrorValidation AffineForm AffineArithQ AffineArith AffineValidation.

(** Error bound validator **)
Fixpoint validErrorboundAA (e:expr Q) (* analyzed expression *)
         (typeMap:FloverMap.t mType) (* derived types for e *)
         (A:analysisResult) (* encoded result of Flover *)
         (dVars:NatSet.t) (* let-bound variables encountered previously *)
         (currNoise: nat) (* current maximal noise term *)
         (errMap:FloverMap.t (affine_form Q)) (* previously seen affine polys *)
  : option (FloverMap.t (affine_form Q) * nat) :=
  (* case analysis for the expression *)
  if FloverMap.mem e errMap then
    (* We have already checked a subexpression *)
    Some (errMap, currNoise)
  else
    olet m := FloverMap.find e typeMap in
    olet dRes := FloverMap.find e A in
    let (intv, err) := dRes in
    (* Error bounds are intervals symmetric at 0 --> the bound must be positive here *)
    if negb (Qleb 0 err) then
      None
    else match e with
    | Var _ x =>
      if NatSet.mem x dVars then
        Some (errMap, currNoise) (* defined variable for a previously checked expression *)
      else
        (* Build an affine polynomial *)
        let errNew := computeErrorQ (maxAbs intv) m in
        let af := mkErrorPolyQ errNew currNoise in
        if Qleb errNew err then
          Some (FloverMap.add e af errMap, (currNoise+1)%nat)
        else
          None
    | Expressions.Const m v =>
        let errNew := computeErrorQ (maxAbs intv) m in
        let af := mkErrorPolyQ errNew currNoise in
        if Qleb errNew err then
          Some (FloverMap.add (elt:=affine_form Q) e af errMap, (currNoise+1)%nat)
        else
          None
    | Unop Neg e1 =>
        olet res := validErrorboundAA e1 typeMap A dVars currNoise errMap in
        let (newErrorMap, maxNoise) := res in
        olet afPolye1 := FloverMap.find e1 newErrorMap in
        let errPoly := AffineArithQ.negate_aff afPolye1 in
        match FloverMap.find e1 A with
        | Some (iv_e1, err1) =>
          if Qeq_bool err err1 then
            Some (FloverMap.add e errPoly newErrorMap, maxNoise)
          else
            None
        | None => None
        end
    | Unop Inv e1 => None
    | Binop b e1 e2 =>
        olet res1 := validErrorboundAA e1 typeMap A dVars currNoise errMap in
        let (newErrorMap1, maxNoise1) := res1 in
        olet res2 := validErrorboundAA e2 typeMap A dVars maxNoise1 newErrorMap1 in
        let (newErrorMap2, maxNoise2) := res2 in
        (* Error polynomial for e1 *)
        olet afPolye1 := FloverMap.find e1 newErrorMap2 in
        (* Error polynomial for e2 *)
        olet afPolye2 := FloverMap.find e2 newErrorMap2 in
        (* Analysis results for e1, e2 *)
        match FloverMap.find e1 A, FloverMap.find e2 A with
        | Some (ive1, err1), Some (ive2, err2) =>
            let errIve1 := widenIntv ive1 err1 in
            let errIve2 := widenIntv ive2 err2 in
            match b with
            | Plus =>
                let actualRange := (addIntv errIve1 errIve2) in
                let errNew := computeErrorQ (maxAbs actualRange) m in
                let errPoly := AffineArithQ.plus_aff
                                (AffineArithQ.plus_aff afPolye1 afPolye2)
                                (mkErrorPolyQ errNew maxNoise2) in
                let errVal := maxAbs (toIntv errPoly) in
                if Qleb errVal err then
                  Some (FloverMap.add e errPoly newErrorMap2, (maxNoise2 + 1)%nat)
                else
                  None
            | Sub =>
                let mAbs := (maxAbs (subtractIntv errIve1 errIve2)) in
                let errNew := computeErrorQ mAbs m in
                let errPoly := AffineArithQ.plus_aff
                                (AffineArithQ.subtract_aff afPolye1 afPolye2)
                                (mkErrorPolyQ errNew maxNoise2) in
                let errVal := maxAbs (toIntv errPoly) in
                if Qleb errVal err then
                  Some (FloverMap.add e errPoly newErrorMap2, (maxNoise2 + 1)%nat)
                else
                  None
            | Mult =>
                let aaRangee1 := fromIntv ive1 maxNoise2 in
                let aaRangee2 := fromIntv ive2 (maxNoise2 + 1) in
                (* Differs from intervals and daisy -- subtraction does not change the range *)
                (* but matters for concrete evaluations *)
                let propError := AffineArithQ.subtract_aff
                                   (AffineArithQ.plus_aff
                                      (AffineArithQ.mult_aff aaRangee1 afPolye2 (maxNoise2 + 2))
                                      (AffineArithQ.mult_aff aaRangee2 afPolye1 (maxNoise2 + 3)))
                                   (AffineArithQ.mult_aff afPolye1 afPolye2 (maxNoise2 + 4)) in
                let mAbs := (maxAbs (multIntv errIve1 errIve2)) in
                let errNew := computeErrorQ mAbs m in
                let errPoly := AffineArithQ.plus_aff propError
                                        (mkErrorPolyQ errNew (maxNoise2 + 5)) in
                let errVal := maxAbs (toIntv errPoly) in
                if Qleb errVal err then
                  Some (FloverMap.add e errPoly newErrorMap2, (maxNoise2 + 6)%nat)
                else
                  None
            | Div =>
                if ((Qleb (ivhi errIve2) 0) && (negb (Qeq_bool (ivhi errIve2) 0))) ||
                    ((Qleb 0 (ivlo errIve2)) && (negb (Qeq_bool (ivlo errIve2) 0))) then
                  let aaRangee1 := fromIntv ive1 maxNoise2 in
                  let aaRangeInve2 := fromIntv (invertIntv ive2) (maxNoise2 + 1) in
                  let minAbsIve2 := minAbs errIve2 in
                  let errMultiplier := fromIntv (invertIntv (multIntv ive2 errIve2))
                                                (maxNoise2 + 2) in
                  let invErrAf2 := AffineArithQ.mult_aff afPolye2 errMultiplier (maxNoise2 + 3) in
                  let propError := AffineArithQ.plus_aff
                                     (AffineArithQ.subtract_aff
                                        (AffineArithQ.mult_aff afPolye1 aaRangeInve2 (maxNoise2 + 4))
                                        (AffineArithQ.mult_aff aaRangee1 invErrAf2 (maxNoise2 + 5)))
                                     (AffineArithQ.mult_aff afPolye1 invErrAf2 (maxNoise2 + 6)) in
                  let mAbs := (maxAbs (divideIntv errIve1 errIve2)) in
                  let errNew := computeErrorQ mAbs m in
                  let errPoly := AffineArithQ.plus_aff propError
                                          (mkErrorPolyQ  errNew (maxNoise2 + 7)) in
                  let errVal := maxAbs (toIntv errPoly) in
                  if (Qleb errVal err) then
                    Some (FloverMap.add e errPoly newErrorMap2, (maxNoise2 + 8)%nat)
                  else
                    None
                else
                  None
            end
        | _, _ => None
        end
    | Fma e1 e2 e3 =>
        olet res1 := validErrorboundAA e1 typeMap A dVars currNoise errMap in
        let (newErrorMap1, maxNoise1) := res1 in
        olet res2 := validErrorboundAA e2 typeMap A dVars maxNoise1 newErrorMap1 in
        let (newErrorMap2, maxNoise2) := res2 in
        olet res3 := validErrorboundAA e3 typeMap A dVars maxNoise2 newErrorMap2 in
        let (newErrorMap3, maxNoise3) := res3 in
        (* Error polynomial for e1 *)
        olet afPolye1 := FloverMap.find e1 newErrorMap3 in
        (* Error polynomial for e2 *)
        olet afPolye2 := FloverMap.find e2 newErrorMap3 in
        (* Error polynomial for e2 *)
        olet afPolye3 := FloverMap.find e3 newErrorMap3 in
        match FloverMap.find e1 A, FloverMap.find e2 A, FloverMap.find e3 A with
        | Some (ive1, err1), Some (ive2, err2), Some (ive3, err3) =>
          let errIve1 := widenIntv ive1 err1 in
          let errIve2 := widenIntv ive2 err2 in
          let errIve3 := widenIntv ive3 err3 in
          let aaRangee1 := fromIntv ive1 maxNoise3 in
          let aaRangee2 := fromIntv ive2 (maxNoise3 + 1) in
          let propError := AffineArithQ.plus_aff
                             (AffineArithQ.subtract_aff
                                (AffineArithQ.plus_aff
                                   (AffineArithQ.mult_aff aaRangee1 afPolye2 (maxNoise3 + 2))
                                   (AffineArithQ.mult_aff aaRangee2 afPolye1 (maxNoise3 + 3)))
                                (AffineArithQ.mult_aff afPolye1 afPolye2 (maxNoise3 + 4)))
                             afPolye3 in
          let mAbs := (maxAbs (addIntv (multIntv errIve1 errIve2) errIve3)) in
          let errNew := computeErrorQ mAbs m in
          let errPoly := AffineArithQ.plus_aff propError (mkErrorPolyQ errNew (maxNoise3 + 5)) in
          let errVal := maxAbs (toIntv errPoly) in
          if Qleb errVal err then
            Some (FloverMap.add e errPoly newErrorMap3, (maxNoise3 + 6)%nat)
          else
            None
        | _, _, _ => None
        end
    | Downcast m e1 =>
        olet res1 := validErrorboundAA e1 typeMap A dVars currNoise errMap in
        let (newErrorMap1, maxNoise1) := res1 in
        (* Error polynomial for e1 *)
        olet afPolye1 := FloverMap.find e1 newErrorMap1 in
        olet aRes := FloverMap.find e1 A in
        let (ive1, err1) := aRes in
        let errIve1 := widenIntv ive1 err1 in
        let mAbs := maxAbs errIve1 in
        let newErr := computeErrorQ mAbs m in
        let errPoly := AffineArithQ.plus_aff afPolye1
                                (mkErrorPolyQ newErr maxNoise1) in
        let errVal := maxAbs (toIntv errPoly) in
        if Qleb errVal err then
          Some (FloverMap.add e errPoly newErrorMap1, (maxNoise1 + 1)%nat)
        else
          None
    | Let _ _ _ _ => None
    end.

(** Error bound command validator **)
(*
Fixpoint validErrorboundAACmd (f: cmd Q) (* analyzed cmd with let's *)
         (typeMap: FloverMap.t mType) (* derived types for e *)
         (A: analysisResult) (* encoded result of Flover *)
         (dVars: NatSet.t) (* let-bound variables encountered previously *)
         (currNoise: nat) (* current maximal noise term *)
         (errMap: FloverMap.t (affine_form Q)) (* previously seen affine polys *)
  : option (FloverMap.t (affine_form Q) * nat) :=
  match f with
  | Let m x e g =>
    olet res1 := validErrorboundAA e typeMap A dVars currNoise errMap in
    let (errMap1, maxNoise1) := res1 in
    olet afPolye := FloverMap.find e errMap1 in
    match FloverMap.find e A, FloverMap.find (Var Q x) A with
    | Some (iv_e, err_e), Some (iv_x, err_x) =>
      if Qeq_bool err_e err_x then
        match FloverMap.find (Var Q x) errMap1 with
        | Some _ => None
        | None => validErrorboundAACmd g typeMap A (NatSet.add x dVars) maxNoise1
                                      (FloverMap.add (Var Q x) afPolye errMap1)
        end
      else
          None
    | _,_ => None
    end
  | Ret e => validErrorboundAA e typeMap A dVars currNoise errMap
  end.
 *)

(* Notation for the universal case of the soundness statement, to help reason
   about memoization cases. This allows us to show several monotonicity lemmas
   that simplify the soundness proofs. This definition is just an extract from
   the full soundness statement, for elaboration on the used assumptions and the
   goal, find that statement below *)
Definition checked_error_expressions (e: expr Q) E1 E2 A Gamma DeltaMap
           noise_map noise expr_map :=
  forall v__R v__FP m__FP (iv__A: intv) (err__A: error),
  eval_expr E1 (toRTMap (toRExpMap Gamma)) (fun x m => Some 0%R) (toREval (toRExp e)) v__R REAL ->
  eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP ->
  FloverMap.find e A = Some (iv__A, err__A) ->
  exists af err__af,
    fresh noise (afQ2R af) /\
    (forall n, (n >= noise)%nat -> noise_map n = None) /\
    FloverMap.find e expr_map = Some af /\
    (0 <= err__af)%R /\
    toInterval (afQ2R af) = (-err__af, err__af)%R /\
    (err__af <= Q2R err__A)%R /\
    af_evals (afQ2R af) (v__R - v__FP)%R noise_map.

Lemma checked_error_expressions_extension e E1 E2 A Gamma DeltaMap
      noise_map1 noise_map2 noise1 noise2 expr_map1 expr_map2:
  contained_map noise_map1 noise_map2 ->
  (noise1 <= noise2)%nat ->
  contained_flover_map expr_map1 expr_map2 ->
  (forall n, (n >= noise2)%nat -> noise_map2 n = None) ->
  checked_error_expressions e E1 E2 A Gamma DeltaMap noise_map1 noise1 expr_map1 ->
  checked_error_expressions e E1 E2 A Gamma DeltaMap noise_map2 noise2 expr_map2.
Proof.
  intros cont contf Hnoise Hvalidmap checked1.
  unfold checked_error_expressions in checked1 |-*.
  intros.
  specialize (checked1 v__R v__FP m__FP iv__A err__A) as (af & err__af & checked1); auto.
  exists af, err__af.
  intuition; eauto using fresh_monotonic, af_evals_map_extension.
Qed.

Lemma checked_error_expressions_flover_map_add_compat e e' af E1 E2 A Gamma DeltaMap
      noise_map noise expr_map:
  Q_orderedExps.exprCompare e' e <> Eq ->
  checked_error_expressions e E1 E2 A Gamma DeltaMap noise_map noise expr_map ->
  checked_error_expressions e E1 E2 A Gamma DeltaMap noise_map noise
                            (FloverMap.add e' af expr_map).
Proof.
  intros Hneq checked1.
  unfold checked_error_expressions in checked1 |-*.
  intros.
  specialize (checked1 v__R v__FP m__FP iv__A err__A) as (af' & err__af' & checked1); auto.
  exists af', err__af'.
  intuition.
  rewrite FloverMapFacts.P.F.add_neq_o; auto.
Qed.

Definition dVars_contained  dVars (expr_map: FloverMap.t (affine_form Q)): Prop :=
  forall v, NatSet.In v dVars -> FloverMap.In (Var Q v) expr_map.

Lemma dVars_contained_extension dVars expr_map1 expr_map2:
  contained_flover_map expr_map1 expr_map2 ->
  dVars_contained dVars expr_map1 ->
  dVars_contained dVars expr_map2.
Proof.
  intros H Hdvars.
  unfold dVars_contained in Hdvars |-*.
  intros v Hvin.
  specialize (Hdvars v Hvin).
  eapply flover_map_in_extension; eauto.
Qed.

Fixpoint contained_subexpr (e: expr Q) (expr_map: FloverMap.t (affine_form Q)): Prop :=
  match e with
  | Var _ x => True
  | Expressions.Const m v => True
  | Unop u e' => contained_subexpr e' expr_map
  | Binop b e1 e2 => contained_subexpr e1 expr_map /\ contained_subexpr e2 expr_map
  | Fma e1 e2 e3 => contained_subexpr e1 expr_map /\ contained_subexpr e2 expr_map /\
                   contained_subexpr e3 expr_map
  | Downcast m e' => contained_subexpr e' expr_map
  | Let _ _ _ _ => False (* FIXME *)
  end /\ FloverMap.In e expr_map.

Lemma contained_subexpr_map_extension e expr_map1 expr_map2:
  contained_flover_map expr_map1 expr_map2 ->
  contained_subexpr e expr_map1 ->
  contained_subexpr e expr_map2.
Proof.
  intros Hcontf Hconte.
  induction e; cbn in *; intuition; eauto using flover_map_in_extension.
Qed.

Lemma contained_subexpr_add_compat e e' a expr_map:
  contained_subexpr e expr_map ->
  contained_subexpr e (FloverMap.add e' a expr_map).
Proof.
  intros Hcont.
  induction e; cbn in *; intuition; rewrite FloverMapFacts.P.F.add_in_iff; now right.
Qed.

Lemma contained_subexpr_eq_compat e e' expr_map:
  Q_orderedExps.exprCompare e e' = Eq ->
  contained_subexpr e expr_map ->
  contained_subexpr e' expr_map.
Proof.
  intros Hexpeq Hcont.
  functional induction (Q_orderedExps.exprCompare e e'); try congruence.
  - apply nat_compare_eq in Hexpeq.
    subst; auto.
  - cbn in Hcont |-*.
    split; auto.
    destruct Hcont as [_ Hcont].
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e3.
  - cbn in e3.
    apply Ndec.Pcompare_Peqb in e6.
    rewrite e6 in e3.
    rewrite andb_true_l in e3.
    apply Ndec.Ncompare_Neqb in Hexpeq.
    now rewrite Hexpeq in e3.
  - cbn in Hcont |-*.
    destruct Hcont as [Hsubcont Hcont].
    specialize (IHc Hexpeq Hsubcont).
    split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e5.
  - cbn in Hcont |-*.
    destruct Hcont as ((Hsubcont1 & Hsubcont2) & Hcont).
    specialize (IHc e6 Hsubcont1).
    specialize (IHc0 Hexpeq Hsubcont2).
    repeat split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e6.
  - cbn in Hcont |-*.
    destruct Hcont as ((Hsubcont1 & Hsubcont2) & Hcont).
    specialize (IHc e6 Hsubcont1).
    specialize (IHc0 Hexpeq Hsubcont2).
    repeat split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e6.
  - cbn in Hcont |-*.
    destruct Hcont as ((Hsubcont1 & Hsubcont2) & Hcont).
    specialize (IHc e6 Hsubcont1).
    specialize (IHc0 Hexpeq Hsubcont2).
    repeat split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e6.
  - cbn in Hcont |-*.
    destruct Hcont as ((Hsubcont1 & Hsubcont2) & Hcont).
    specialize (IHc e6 Hsubcont1).
    specialize (IHc0 Hexpeq Hsubcont2).
    repeat split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e6.
  - cbn in Hcont |-*.
    destruct Hcont as ((Hsubcont1 & Hsubcont2 & Hsubcont3) & Hcont).
    specialize (IHc e3 Hsubcont1).
    specialize (IHc0 e4 Hsubcont2).
    specialize (IHc1 Hexpeq Hsubcont3).
    repeat split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    rewrite e4.
    now rewrite e3.
  - cbn in Hcont |-*.
    destruct Hcont as [Hsubcont Hcont].
    specialize (IHc Hexpeq Hsubcont).
    split; auto.
    rewrite FloverMapFacts.P.F.In_iff in Hcont; eauto.
    cbn.
    now rewrite e5.
  - cbn in e5.
    apply Ndec.Pcompare_Peqb in e8.
    rewrite e8 in e5.
    rewrite andb_true_l in e5.
    apply Ndec.Ncompare_Neqb in Hexpeq.
    now rewrite Hexpeq in e5.
  - simpl in *. destruct Hcont; contradiction.
  - simpl in *. destruct Hcont; contradiction.
Qed.

Lemma validErrorboundAA_contained_subexpr e Gamma A dVars noise1 noise2 expr_map1 expr_map2:
  (forall e', FloverMap.In e' expr_map1 ->
         contained_subexpr e' expr_map1) ->
  (forall n, NatSet.In n dVars -> FloverMap.In (Var Q n) expr_map1) ->
  validErrorboundAA e Gamma A dVars noise1 expr_map1 = Some (expr_map2, noise2) ->
  contained_subexpr e expr_map2 /\
  contained_flover_map expr_map1 expr_map2 /\
  (forall e', ~ FloverMap.In e' expr_map1 -> FloverMap.In e' expr_map2 ->
   contained_subexpr e' expr_map2).
Proof.
  revert noise1 noise2 expr_map1 expr_map2.
  induction e; intros * Hchecked Hdvars Hvalidbounds; cbn in Hvalidbounds.
  - destruct (FloverMap.mem (Var Q n) expr_map1) eqn:Hmem.
    {
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    }
    Flover_compute.
    destruct negb; [congruence|].
    destruct NatSet.mem eqn:Hmemvar.
    + inversion Hvalidbounds; subst; clear Hvalidbounds.
      intuition.
    + destruct Qleb; [|congruence].
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      repeat split.
      * cbn.
        intuition.
        apply flover_map_in_add.
      * apply contained_flover_map_extension.
        now rewrite <- mem_false_find_none.
      * intros e' Hnin1 Hin.
        apply flover_map_el_eq_extension in Hin; auto.
        specialize Hin as [Heq Hexpreq].
        eapply contained_subexpr_eq_compat; eauto.
        cbn.
        intuition.
        apply flover_map_in_add.
  - destruct (FloverMap.mem (Expressions.Const m v) expr_map1) eqn:Hmem.
    {
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    }
    Flover_compute.
    destruct negb; [congruence|].
    destruct Qleb; [|congruence].
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    repeat split.
    + cbn.
      intuition.
      apply flover_map_in_add.
    + apply contained_flover_map_extension.
      now rewrite <- mem_false_find_none.
    + intros e' Hnin1 Hin.
      apply flover_map_el_eq_extension in Hin; auto.
      specialize Hin as [Heq Hexpreq].
      eapply contained_subexpr_eq_compat; eauto.
      cbn.
      intuition.
      apply flover_map_in_add.
  - destruct (FloverMap.mem (Unop u e) expr_map1) eqn:Hmem.
    {
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    }
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct p.
    destruct (negb (Qleb 0 e0)) eqn: H0err; [congruence|].
    destruct u; [|congruence].
    destruct (validErrorboundAA e Gamma A dVars noise1 expr_map1)
      as [(subexpr_map, subnoise)|] eqn: Hvalidsubexpr;
      simpl in Hvalidbounds; try congruence.
    destruct (FloverMap.find e subexpr_map) as [subaf|] eqn: Hsubaf;
      simpl in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e A) as [(subiv, suberr)|] eqn: Hsuba;
      simpl in Hvalidbounds; [|congruence].
    destruct (Qeq_bool e0 suberr) eqn: Heq__err; simpl in Hvalidbounds; [|congruence].
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    specialize IHe as (IHsubexpr & IHcont & IHechecked); eauto.
    split; [|split].
    + cbn.
      intuition; [|apply flover_map_in_add].
      now eapply contained_subexpr_add_compat.
    + etransitivity; try apply contained_flover_map_add_compat; eauto.
      apply contained_flover_map_extension.
      now rewrite <- mem_false_find_none.
    + intros e' Hnin1 Hin.
      destruct (flover_map_in_dec e' subexpr_map) as [Hsubin|Hsubnin];
        [apply contained_subexpr_add_compat; auto|].
      apply flover_map_el_eq_extension in Hin; auto.
      specialize Hin as [Heq Hexpreq].
      eapply contained_subexpr_eq_compat; eauto.
      cbn.
      intuition.
      * apply contained_subexpr_add_compat; auto.
      * apply flover_map_in_add.
  - destruct (FloverMap.mem (Binop b e1 e2) expr_map1) eqn:Hmem.
    {
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    }
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct p as (? & err__A).
    destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
    destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
      as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
      cbn in Hvalidbounds; try congruence.
    destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
      as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
      cbn in Hvalidbounds; try congruence.
    destruct (FloverMap.find e1 subexpr_map2) as [subaf1|] eqn: Hsubaf1;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e2 subexpr_map2) as [subaf2|] eqn: Hsubaf2;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e1 A); cbn in Hvalidbounds; [|congruence].
    destruct p as (iv__A1 & err__A1).
    destruct (FloverMap.find e2 A); cbn in Hvalidbounds; [|congruence].
    destruct p as (iv__A2 & err__A2).
    clear H0err.
    specialize IHe1 as (IHsubexpr1 & IHcont1 & IHchecked1); eauto.
    specialize (IHe2 subnoise1 subnoise2 subexpr_map1 subexpr_map2)
      as (IHsubexpr2 & IHcont2 & IHechecked2); eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply contained_subexpr_map_extension with (expr_map1 := expr_map1); eauto.
      - now apply IHchecked1.
    }
    {
      intros * ?.
      eapply flover_map_in_extension; try apply Hdvars; eauto.
    }
    rewrite mem_false_find_none in Hmem.
    destruct b.
    4: destruct (Qleb (snd iv__A2 + err__A2) 0 && negb (Qeq_bool (snd iv__A2 + err__A2) 0)
              || Qleb 0 (fst iv__A2 - err__A2) && negb (Qeq_bool (fst iv__A2 - err__A2) 0)); [|congruence].
    all: destruct Qleb; cbn in Hvalidbounds; [|congruence].
    all: inversion Hvalidbounds; subst; clear Hvalidbounds.
    + split; [|split].
      * cbn.
        intuition; eauto using flover_map_in_add, contained_subexpr_add_compat.
        apply contained_subexpr_add_compat.
        apply contained_subexpr_map_extension with (expr_map1 := subexpr_map1); auto.
      * epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcont2].
        assumption.
      * intros e' Hnin1 Hin.
        destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1];
          [apply contained_subexpr_add_compat; eapply contained_subexpr_map_extension; eauto|].
        destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2];
          [apply contained_subexpr_add_compat; auto|].
        apply flover_map_el_eq_extension in Hin; auto.
        specialize Hin as [Heq Hexpreq].
        eapply contained_subexpr_eq_compat; eauto.
        cbn.
        intuition; eauto using contained_subexpr_add_compat, flover_map_in_add.
        apply contained_subexpr_add_compat.
        eapply contained_subexpr_map_extension; eauto.
    + split; [|split].
      * cbn.
        intuition; eauto using flover_map_in_add, contained_subexpr_add_compat.
        apply contained_subexpr_add_compat.
        apply contained_subexpr_map_extension with (expr_map1 := subexpr_map1); auto.
      * epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcont2].
        assumption.
      * intros e' Hnin1 Hin.
        destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1];
          [apply contained_subexpr_add_compat; eapply contained_subexpr_map_extension; eauto|].
        destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2];
          [apply contained_subexpr_add_compat; auto|].
        apply flover_map_el_eq_extension in Hin; auto.
        specialize Hin as [Heq Hexpreq].
        eapply contained_subexpr_eq_compat; eauto.
        cbn.
        intuition; eauto using contained_subexpr_add_compat, flover_map_in_add.
        apply contained_subexpr_add_compat.
        eapply contained_subexpr_map_extension; eauto.
    + split; [|split].
      * cbn.
        intuition; eauto using flover_map_in_add, contained_subexpr_add_compat.
        apply contained_subexpr_add_compat.
        apply contained_subexpr_map_extension with (expr_map1 := subexpr_map1); auto.
      * epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcont2].
        assumption.
      * intros e' Hnin1 Hin.
        destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1];
          [apply contained_subexpr_add_compat; eapply contained_subexpr_map_extension; eauto|].
        destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2];
          [apply contained_subexpr_add_compat; auto|].
        apply flover_map_el_eq_extension in Hin; auto.
        specialize Hin as [Heq Hexpreq].
        eapply contained_subexpr_eq_compat; eauto.
        cbn.
        intuition; eauto using contained_subexpr_add_compat, flover_map_in_add.
        apply contained_subexpr_add_compat.
        eapply contained_subexpr_map_extension; eauto.
    + split; [|split].
      * cbn.
        intuition; eauto using flover_map_in_add, contained_subexpr_add_compat.
        apply contained_subexpr_add_compat.
        apply contained_subexpr_map_extension with (expr_map1 := subexpr_map1); auto.
      * epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcont2].
        assumption.
      * intros e' Hnin1 Hin.
        destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1];
          [apply contained_subexpr_add_compat; eapply contained_subexpr_map_extension; eauto|].
        destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2];
          [apply contained_subexpr_add_compat; auto|].
        apply flover_map_el_eq_extension in Hin; auto.
        specialize Hin as [Heq Hexpreq].
        eapply contained_subexpr_eq_compat; eauto.
        cbn.
        intuition; eauto using contained_subexpr_add_compat, flover_map_in_add.
        apply contained_subexpr_add_compat.
        eapply contained_subexpr_map_extension; eauto.
  - destruct (FloverMap.mem (Fma e1 e2 e3) expr_map1) eqn:Hmem.
    {
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    }
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct p as (? & err__A).
    destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
    destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
      as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
      cbn in Hvalidbounds; try congruence.
    destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
      as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
      cbn in Hvalidbounds; try congruence.
    destruct (validErrorboundAA e3 Gamma A dVars subnoise2 subexpr_map2)
      as [(subexpr_map3, subnoise3)|] eqn: Hvalidsubexpr3;
      cbn in Hvalidbounds; try congruence.
    destruct (FloverMap.find e1 subexpr_map3) as [subaf1|] eqn: Hsubaf1;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e2 subexpr_map3) as [subaf2|] eqn: Hsubaf2;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e3 subexpr_map3) as [subaf3|] eqn: Hsubaf3;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e1 A); cbn in Hvalidbounds; [|congruence].
    destruct p as (iv__A1 & err__A1).
    destruct (FloverMap.find e2 A); cbn in Hvalidbounds; [|congruence].
    destruct p as (iv__A2 & err__A2).
    destruct (FloverMap.find e3 A); cbn in Hvalidbounds; [|congruence].
    destruct p as (iv__A3 & err__A3).
    clear H0err.
    specialize IHe1 as (IHsubexpr1 & IHcont1 & IHchecked1); eauto.
    specialize (IHe2 subnoise1 subnoise2 subexpr_map1 subexpr_map2)
      as (IHsubexpr2 & IHcont2 & IHchecked2); eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply contained_subexpr_map_extension with (expr_map1 := expr_map1); eauto.
      - now apply IHchecked1.
    }
    {
      intros * ?.
      eapply flover_map_in_extension; try apply Hdvars; eauto.
    }
    specialize (IHe3 subnoise2 subnoise3 subexpr_map2 subexpr_map3)
      as (IHsubexpr3 & IHcont3 & IHechecked3); eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply contained_subexpr_map_extension with (expr_map1 := expr_map1); eauto.
        etransitivity; eauto.
      - destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1].
        + apply contained_subexpr_map_extension with (expr_map1 := subexpr_map1); auto.
        + now apply IHchecked2.
    }
    {
      intros * ?.
      eapply flover_map_in_extension; try apply Hdvars; eauto.
      etransitivity; eauto.
    }
    rewrite mem_false_find_none in Hmem.
    destruct Qleb; cbn in Hvalidbounds; [|congruence].
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    split; [|split].
    + cbn.
      intuition; eauto using flover_map_in_add, contained_subexpr_add_compat.
      * apply contained_subexpr_add_compat.
        apply contained_subexpr_map_extension with (expr_map1 := subexpr_map1); auto.
        etransitivity; eauto.
      * apply contained_subexpr_add_compat.
        apply contained_subexpr_map_extension with (expr_map1 := subexpr_map2); auto.
    + epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
      etransitivity; [exact G|].
      apply contained_flover_map_add_compat.
      etransitivity; [|exact IHcont3].
      etransitivity; [|exact IHcont2].
      assumption.
    + intros e' Hnin1 Hin.
      destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1];
        [apply contained_subexpr_add_compat; eapply contained_subexpr_map_extension; eauto;
         eapply contained_subexpr_map_extension; eauto|].
      destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2];
        [apply contained_subexpr_add_compat; auto; eapply contained_subexpr_map_extension; eauto|].
      destruct (flover_map_in_dec e' subexpr_map3) as [Hsubin3|Hsubnin3];
        [apply contained_subexpr_add_compat; auto|].
      apply flover_map_el_eq_extension in Hin; auto.
      specialize Hin as [Heq Hexpreq].
      eapply contained_subexpr_eq_compat; eauto.
      cbn.
      intuition; eauto using contained_subexpr_add_compat, flover_map_in_add.
      all: apply contained_subexpr_add_compat.
      all: eapply contained_subexpr_map_extension; eauto.
      eapply contained_subexpr_map_extension; eauto.
  - destruct (FloverMap.mem (Downcast m e) expr_map1) eqn:Hmem.
    {
      inversion Hvalidbounds; subst; clear Hvalidbounds.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    }
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct FloverMap.find; cbn in Hvalidbounds; [|congruence].
    destruct p.
    destruct (negb (Qleb 0 e0)) eqn: H0err; [congruence|].
    destruct (validErrorboundAA e Gamma A dVars noise1 expr_map1)
      as [(subexpr_map, subnoise)|] eqn: Hvalidsubexpr;
      cbn in Hvalidbounds; try congruence.
    destruct (FloverMap.find e subexpr_map) as [subaf|] eqn: Hsubaf;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e A) as [(subiv, suberr)|] eqn: Hsuba;
      cbn in Hvalidbounds; [|congruence].
    clear H0err.
    destruct Qleb; cbn in Hvalidbounds; [|congruence].
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    specialize IHe as (IHsubexpr & IHcont & IHechecked); eauto.
    split; [|split].
    + cbn.
      intuition; [|apply flover_map_in_add].
      now eapply contained_subexpr_add_compat.
    + etransitivity; try apply contained_flover_map_add_compat; eauto.
      apply contained_flover_map_extension.
      now rewrite <- mem_false_find_none.
    + intros e' Hnin1 Hin.
      destruct (flover_map_in_dec e' subexpr_map) as [Hsubin|Hsubnin];
        [apply contained_subexpr_add_compat; auto|].
      apply flover_map_el_eq_extension in Hin; auto.
      specialize Hin as [Heq Hexpreq].
      eapply contained_subexpr_eq_compat; eauto.
      cbn.
      intuition.
      * apply contained_subexpr_add_compat; auto.
      * apply flover_map_in_add.
  - destruct (FloverMap.mem (elt:=affine_form Q) (Let m n e1 e2) expr_map1) eqn:Hmem.
    + inversion Hvalidbounds; subst.
      apply FloverMap.mem_2 in Hmem.
      intuition.
    + Flover_compute. destruct (negb (Qleb 0 e)) eqn:?; congruence.
Qed.

(* The soundness statements starts off with assumption that the checking
   function succeeds and then also maintains several invariants. We require
   these invariants because of the checker function dependency on the current
   noise index and its memoization of the previosly computed polynomials. We
   explain these invariants in-line below. *)
Definition validErrorboundAA_sound_statement e E1 E2 A Gamma DeltaMap fVars dVars :=
  forall (expr_map1 expr_map2 : FloverMap.t (affine_form Q))
    (noise_map1 : nat -> option noise_type) (noise1 noise2 : nat) (v__R : R)
    (iv__A : intv) (err__A : error),
    (forall (v : R) (m' : mType),
        exists d : R, DeltaMap v m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) v__R REAL ->
    validRanges e A E1 (toRTMap (toRExpMap Gamma)) ->
    validErrorboundAA e Gamma A dVars noise1 expr_map1 = Some (expr_map2, noise2) ->
    (* WAS: usedVars *)
    NatSet.Subset (freeVars e -- dVars) fVars ->
    validTypes e Gamma ->
    FloverMap.find e A = Some (iv__A, err__A) ->
    (* Starting noise index is greater than 0 and the noise mapping doesn't
       map it and anything above to a noise value *)
    (0 < noise1)%nat ->
    (forall n0 : nat, (n0 >= noise1)%nat -> noise_map1 n0 = None) ->
    (* If a var is a dVar, we know it's in expr_map and invoke the corresponding
     preconditions (described below) *)
    dVars_contained dVars expr_map1 ->
    (* Precondition:
       Memoization for the existential case of the goal: if we checked the expression
       already, we know that there is an execution and certificate results for it *)
    (forall e' : FloverMap.key,
        FloverMap.In e' expr_map1 ->
        (* Assumption needed for Cmd_sound proof *)
        (* WAS: usedVars *)
        NatSet.Subset (freeVars e') (NatSet.union fVars dVars) /\
        (exists iv__A' err__A', FloverMap.find e' A = Some (iv__A', err__A')) /\
        exists (v__FP' : R) (m__FP' : mType),
          eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e') v__FP' m__FP') ->
    (* Precondition:
       Memoization for the universal case of the goal -- note that
       `checked_error_expressions` track only that case: if we checked
       the expression already, then, if we provide the execution in
       finite precision and the certificate results, we will know that
       the execution's error is bounded *)
    (forall e' : FloverMap.key,
        FloverMap.In e' expr_map1 ->
        checked_error_expressions e' E1 E2 A Gamma DeltaMap noise_map1 noise1 expr_map1) ->
    (* THE EXESTENTIAL CASE OF THE GOAL *)
    ((exists (v__FP : R) (m__FP : mType),
         eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP) /\
     (* Invariant of the existential case:
        our given expr_map1 is updated only with the expressions for which
        the existential part holds *)
     (forall e' : FloverMap.key,
         ~ FloverMap.In e' expr_map1 -> FloverMap.In e' expr_map2 ->
         (* WAS: usedVars *)
         NatSet.Subset (freeVars e') (NatSet.union fVars dVars) /\
         (exists iv__A' err__A', FloverMap.find e' A = Some (iv__A', err__A')) /\
         exists (v__FP' : R) (m__FP' : mType),
           eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e') v__FP' m__FP')) /\
    (* UNIVERSAL CASE OF THE GOAL *)
    (forall (v__FP : R) (m__FP : mType),
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP ->
        (* For the given evaluation we can find a polynomial and an
           error bound with a monotonic extension of noise_map1 to
           noise_map2 *)
        exists (af : affine_form Q) (err__af : R) (noise_map2 : noise_mapping),
          (* Invariant: the checker function only adds new polynomials
             to the expr_map, never removes something from it *)
          contained_flover_map expr_map1 expr_map2 /\
          (* Noise index invariants: the checker function returns new
             noise that is not used in already produced polynomials *)
          (noise1 <= noise2)%nat /\
          fresh noise2 (afQ2R af) /\
          (* Invariant: noise_map is incrementally updated *)
          contained_map noise_map1 noise_map2 /\
          (forall n0 : nat, (n0 >= noise2)%nat -> noise_map2 n0 = None) /\
          FloverMap.find (elt:=affine_form Q) e expr_map2 = Some af /\
          (* To show that the error is bounded by the polynomial, we say that
             the polynomial's range is bounded by err__af, which has a value
             less or equal to the certificate error, and that the polynomial
             captures any difference between real and finite-precision
             evaluations *)
          (0 <= err__af)%R /\
          toInterval (afQ2R af) = ((- err__af)%R, err__af) /\
          (err__af <= Q2R err__A)%R /\
          af_evals (afQ2R af) (v__R - v__FP) noise_map2 /\
          (* Invariant of the universal case:
             our given expr_map1 is updated only with the expressions for which
             the universal part (the conclusion directly above) holds *)
          (forall e' : FloverMap.key,
              ~ FloverMap.In e' expr_map1 -> FloverMap.In e' expr_map2 ->
              checked_error_expressions e' E1 E2 A Gamma DeltaMap noise_map2 noise2 expr_map2)).

Lemma validErrorboundAA_sound_var n E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement (Var Q n) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  unfold validErrorboundAA_sound_statement.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall;
  inversion Heval__R; subst.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Var Q n) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & Hcert' & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  destruct (Htypecheck) as (m & Hetype & _ & Hvalidexec).
  rewrite Hetype in Hvalidbounds; simpl in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  pose proof Hrange as Hrange'.
  destruct Hrange as [_ [tmpiv [tmperr [tmpvR [Hres__A' [Heval1' Hcontained]]]]]].
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  eapply meps_0_deterministic in Heval1'; try exact Heval__R.
  replace tmpvR with v__R in * by congruence; clear Heval1' tmpvR.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  cbn in Htypecheck.
  destruct (NatSet.mem n dVars) eqn: Hmem__n; cbn in Hvalidbounds.
  - inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply NatSetProps.FM.mem_2 in Hmem__n.
    specialize (Hdvars n Hmem__n).
    rewrite <- FloverMapFacts.P.F.not_mem_in_iff in Hmem.
    congruence.
  - destruct (Qleb (computeErrorQ (maxAbs iv__A) m) err__A) eqn: Herrle; cbn in Hvalidbounds; [|congruence].
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    rewrite mem_false_find_none in Hmem.
    apply not_in_not_mem in Hmem__n.
    assert (n ∈ fVars) as Hmem__n' by (set_tac; set_tac).
    assert (exists v, E2 n = Some v) as [v__fp Hv__fp]
        by (eapply approxEnv_gives_value; eauto; set_tac).
    split.
    + assert (exists (v__FP : R) (m__FP : mType),
                 eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Var Q n)) v__FP m__FP).
      {
        exists v__fp, m.
        constructor; auto.
        eapply toRExpMap_some with (e:=Var Q n); eauto.
      }
      split; auto.
      intros e' Hnin Hin.
      destruct (flover_map_el_eq_extension Hnin Hin) as [Heq Hexpeq].
      split; [|split; [|now rewrite Hexpeq]].
      * rewrite freeVars_eq_compat;
          try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
        simpl. set_tac. subst; auto.
      * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
    + intros v__FP m__FP Heval__FP.
      rewrite Qle_bool_iff in Herrle.
      apply Qle_Rle in Herrle.
      inversion Heval__FP; subst.
      eapply toRExpMap_some with (e:=Var Q n) in Hetype; eauto.
      cbn in Hetype.
      replace m with m__FP in * by congruence; clear H2.
      replace v__fp with v__FP in * by congruence; clear H3.
      assert (exists q, af_evals (afQ2R (mkErrorPolyQ (computeErrorQ (maxAbs iv__A) m__FP) noise1))
                            (v__R - v__FP)%R (updMap noise_map1 noise1 q)) as [q Hevals].
      {
        rewrite afQ2R_mkErrorPolyQ.
        rewrite computeErrorQ_computeErrorR.
        apply af_evals_mkErrorPolyR_updMap; auto using computeErrorR_pos.
        pose proof (approxEnv_fVar_bounded Henv H1 Hv__fp Hmem__n' Hetype) as H.
        eapply Rle_trans; try exact H.
        rewrite <- maxAbs_impl_RmaxAbs_iv.
        destruct iv__A as [liv__A hiv__A].
        apply computeErrorR_up.
        apply contained_leq_maxAbs.
        now cbn.
      }
      exists (mkErrorPolyQ (computeErrorQ (maxAbs iv__A) m__FP) noise1),
      (Q2R (computeErrorQ (maxAbs iv__A) m__FP)), (updMap noise_map1 noise1 q).
      rewrite computeErrorQ_computeErrorR in Herrle |-*.
      {
        repeat split; try auto.
        - now apply contained_flover_map_extension.
        - lia.
        - rewrite afQ2R_mkErrorPolyQ.
          apply mkErrorPolyR_fresh_compat; lia.
        - apply contained_map_extension; auto.
        - intros n' Hn'.
          unfold updMap.
          destruct (n' =? noise1) eqn: Hneq.
          + apply beq_nat_true in Hneq.
            lia.
          + apply Hnoise_map1.
            lia.
        - rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          apply Q_orderedExps.exprCompare_refl.
        - apply computeErrorR_pos.
        - rewrite afQ2R_mkErrorPolyQ.
          rewrite computeErrorQ_computeErrorR.
          rewrite toInterval_mkErrorPolyR; auto using computeErrorR_pos.
        - intros e' Hnin Hin.
          unfold checked_error_expressions.
          pose proof (flover_map_el_eq_extension Hnin Hin) as [Hexeq Hreq].
          rewrite Hreq.
          intros.
          exists (mkErrorPolyQ (computeErrorQ (maxAbs iv__A) m__FP) noise1),
          (Q2R (computeErrorQ (maxAbs iv__A) m__FP)).
          rewrite computeErrorQ_computeErrorR.
          {
            repeat split; try auto.
            - rewrite afQ2R_mkErrorPolyQ.
              apply mkErrorPolyR_fresh_compat; lia.
            - intros n' Hn'.
              unfold updMap.
              destruct (n' =? noise1) eqn: Hneq.
              + apply beq_nat_true in Hneq.
                lia.
              + apply Hnoise_map1.
                lia.
            - rewrite FloverMapFacts.P.F.add_eq_o; auto.
            - apply computeErrorR_pos.
            - rewrite afQ2R_mkErrorPolyQ.
              rewrite computeErrorQ_computeErrorR.
              rewrite toInterval_mkErrorPolyR; auto using computeErrorR_pos.
            - erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
              now match goal with
                  | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                         H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                  end.
            - erewrite meps_0_deterministic with (v1 := v__R0) (v2 := v__R); eauto.
              erewrite eval_expr_functional with (v1 := v__FP0) (v2 := v__FP); eauto.
              erewrite Gamma_det; eauto.
          }
      }
Qed.

Lemma validErrorboundAA_sound_const v m E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement (Expressions.Const m v) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  unfold validErrorboundAA_sound_statement.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall;
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Expressions.Const m v) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & Hcert' & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  destruct (Htypecheck) as (m__e & Hetype & _ & Hvalidexec).
  rewrite Hetype in Hvalidbounds; simpl in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (Qleb (computeErrorQ (maxAbs iv__A) m) err__A) eqn: Herrle; cbn in Hvalidbounds; [|congruence].
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  rewrite mem_false_find_none in Hmem.
  split.
  - assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap
                             (toRExp (Expressions.Const m v)) v__FP m__FP).
    {
      specialize (Hdeltamap (Q2R v) m)
        as (delta' & Hdelta & Hdelta').
      exists (perturb (Q2R v) m delta'), m.
      eapply Const_dist' with (delta := delta'); auto.
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_el_eq_extension Hnin Hin) as [Heq Hexpeq].
    split; [|split; [|now rewrite Hexpeq]].
      * rewrite freeVars_eq_compat;
          try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
        simpl. set_tac.
      * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  - rewrite Qle_bool_iff in Herrle.
    apply Qle_Rle in Herrle.
    intros * Heval__FP.
    inversion Heval__R; subst.
    inversion Heval__FP; subst.
    cbn in Htypecheck.
    cbn in Hrange.
    destruct Hrange as (_ & tmpiv & tmperr & tmpvR & Hres__A' & Heval1' & Hcontained).
    rewrite Hcert in Hres__A'.
    replace tmpiv with iv__A in * by congruence.
    replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
    pose proof Heval__R as Heval__R'.
    eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
    cbn in Heval__R'.
    replace tmpvR with (Q2R v) in * by congruence; clear Heval1' Heval__R' tmpvR.
    cbn in Heval__R, Heval__FP.
    assert (exists q, af_evals (afQ2R (mkErrorPolyQ (computeErrorQ (maxAbs iv__A) m__FP) noise1)) (Q2R v - perturb (Q2R v) m__FP delta0)%R (updMap noise_map1 noise1 q)) as [q Hevals].
    {
      rewrite afQ2R_mkErrorPolyQ.
      rewrite computeErrorQ_computeErrorR.
      apply af_evals_mkErrorPolyR_updMap; auto using computeErrorR_pos.
      rewrite <- maxAbs_impl_RmaxAbs_iv.
      destruct iv__A as [liv__A hiv__A].
      cbn in Hcontained |-*.
      pose proof (@const_abs_err_bounded (Q2R v) (Q2R v) (perturb (Q2R v) m__FP delta0)
                                         E1 E2 m__FP _ _ Heval__R Heval__FP) as H'.
      apply (Rle_trans _ _ _ H').
      apply computeErrorR_up.
      apply contained_leq_maxAbs.
      now cbn.
    }
    assert (forall n : nat, (n >= noise1 + 1)%nat -> updMap noise_map1 noise1 q n = None).
    {
      intros n' Hn'.
      unfold updMap.
      destruct (n' =? noise1) eqn: Hneq.
      * apply beq_nat_true in Hneq.
        lia.
      * apply Hnoise_map1.
        lia.
    }
    exists (mkErrorPolyQ (computeErrorQ (maxAbs iv__A) m__FP) noise1),
    (Q2R (computeErrorQ (maxAbs iv__A) m__FP)), (updMap noise_map1 noise1 q).
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    repeat split; auto.
    + now apply contained_flover_map_extension.
    + lia.
    + rewrite afQ2R_mkErrorPolyQ.
      apply mkErrorPolyR_fresh_compat; lia.
    + apply contained_map_extension; auto.
    + rewrite FloverMapFacts.P.F.add_eq_o; try auto.
      apply Q_orderedExps.exprCompare_refl.
    + apply computeErrorR_pos.
    + rewrite afQ2R_mkErrorPolyQ.
      rewrite computeErrorQ_computeErrorR.
      rewrite toInterval_mkErrorPolyR; auto using computeErrorR_pos.
    + intros e' Hnin Hin.
      unfold checked_error_expressions.
      pose proof (flover_map_el_eq_extension Hnin Hin) as [Hexeq Hreq].
      rewrite Hreq.
      intros.
      exists (mkErrorPolyQ (computeErrorQ (maxAbs iv__A) m__FP) noise1),
      (Q2R (computeErrorQ (maxAbs iv__A) m__FP)).
      rewrite computeErrorQ_computeErrorR.
      repeat split; try auto.
      * rewrite afQ2R_mkErrorPolyQ.
        apply mkErrorPolyR_fresh_compat; lia.
      * rewrite FloverMapFacts.P.F.add_eq_o; auto.
      * apply computeErrorR_pos.
      * rewrite afQ2R_mkErrorPolyQ.
        rewrite computeErrorQ_computeErrorR.
        rewrite toInterval_mkErrorPolyR; auto using computeErrorR_pos.
      * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
        now match goal with
            | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                   H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
            end.
      * erewrite meps_0_deterministic
          with (v1 := v__R) (v2 := (perturb (Q2R v) REAL delta)); eauto.
        erewrite eval_expr_functional
          with (v1 := v__FP) (v2 := (perturb (Q2R v) m__FP delta0)); eauto.
        erewrite Gamma_det; eauto.
Qed.

Lemma validErrorboundAA_sound_unop u e E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Unop u e) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe.
  unfold validErrorboundAA_sound_statement in IHe |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (elt:=affine_form Q) (Unop u e) expr_map1) eqn: Hmem;
    simpl in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  destruct Htypecheck as (m__e & Hetype & (Htypecheck__e & ?) & Hvalidexec).
  rewrite Hetype in Hvalidbounds; simpl in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; simpl in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct u; [|congruence].
  destruct (validErrorboundAA e Gamma A dVars noise1 expr_map1)
    as [(subexpr_map, subnoise)|] eqn: Hvalidsubexpr;
    simpl in Hvalidbounds; try congruence.
  destruct (FloverMap.find e subexpr_map) as [subaf|] eqn: Hsubaf;
    simpl in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e A) as [(subiv, suberr)|] eqn: Hsuba;
    simpl in Hvalidbounds; [|congruence].
  destruct (Qeq_bool err__A suberr) eqn: Heq__err; simpl in Hvalidbounds; [|congruence].
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  inversion Heval__R; subst.
  unfold isCompat in H2.
  destruct m; cbn in H2; try congruence; clear H2.
  pose proof H3 as H3det.
  specialize (IHe expr_map1 subexpr_map noise_map1 noise1 noise2 v1 subiv suberr).
  specialize IHe as (IHevex & IHevall); eauto;
    [destruct Hrange; auto|].
  split.
  - destruct IHevex as ((nF & m & IHeval) & IHcheckedex).
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Unop Neg e)) v__FP m__FP).
    {
      exists (evalUnop Neg nF); exists m__e.
      eapply Unop_neg'; eauto.
      { eapply toRExpMap_some with (e:=Unop Neg e); eauto. }
      { destruct H as [? [? ?]].
        assert (x = m).
        { eapply validTypes_exec; eauto. }
        subst; auto. }
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map) as [Hin1|Hnin1].
    + edestruct IHcheckedex as (? & ? & ?); eauto.
    + destruct (flover_map_el_eq_extension Hnin1 Hin) as [Heq Hexpeq]; auto.
      split; [|split; [|now rewrite Hexpeq]].
      * rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
          try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
        now apply subset_diff_to_subset_union.
      * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  - intros v__FP m__FP Heval__FPdet.
    inversion Heval__FPdet; subst.
    pose proof H5 as H5det.
    specialize (IHevall v0 m)
      as (ihaf & iherr__af & ihnoise_map & IHcontf & IHnoise & IHfresh & IHcontn & IHnoise_map &
          IHsub__A & IHerrpos & IHiv__err & IHerr & IHevals & IHchecked); auto.
    replace subaf with ihaf by congruence.
    apply Qeq_bool_eq in Heq__err.
    apply Qeq_eqR in Heq__err.
    rename v0 into nF.
    exists (AffineArithQ.negate_aff ihaf), iherr__af, ihnoise_map.
    repeat split; auto.
    + pose proof contained_flover_map_extension as H'.
      rewrite mem_false_find_none in Hmem.
      specialize (H' _ expr_map1 _ (AffineArithQ.negate_aff ihaf) Hmem).
      etransitivity; try eassumption.
      now apply contained_flover_map_add_compat.
    + rewrite afQ2R_negate_aff.
      unfold negate_aff.
      now apply mult_aff_const_fresh_compat.
    + rewrite FloverMapFacts.P.F.add_eq_o; try auto.
      apply Q_orderedExps.exprCompare_refl.
    + rewrite afQ2R_negate_aff.
      rewrite toInterval_negate_aff.
      rewrite IHiv__err.
      cbn.
      f_equal; lra.
    + now rewrite Heq__err.
    + rewrite Rsub_eq_Ropp_Rplus in IHevals.
      cbn.
      field_rewrite (- v1 - - nF = - (v1 - nF))%R.
      rewrite afQ2R_negate_aff.
      now apply negate_aff_sound.
    + intros e' Hnin Hin.
      {
        destruct (FloverMapFacts.O.MO.eq_dec (Unop Neg e) e') as [Heqexp|Heqexp].
        - unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          intros.
          exists (AffineArithQ.negate_aff ihaf), iherr__af.
          repeat split; try auto.
          + rewrite afQ2R_negate_aff.
            unfold negate_aff.
            now apply mult_aff_const_fresh_compat.
          + rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          + rewrite afQ2R_negate_aff.
            rewrite toInterval_negate_aff.
            rewrite IHiv__err.
            cbn.
            f_equal; lra.
          + erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            match goal with
            | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                   H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
            end.
            now rewrite Heq__err.
          + erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := (evalUnop Neg v1)); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := (evalUnop Neg nF)); eauto;
              [|erewrite Gamma_det; eauto].
            rewrite Rsub_eq_Ropp_Rplus in IHevals.
            cbn.
            field_rewrite (- v1 - - nF = - (v1 - nF))%R.
            rewrite afQ2R_negate_aff.
            now apply negate_aff_sound.
        - destruct (FloverMapFacts.P.F.In_dec subexpr_map e') as [Hsubin|Hsubnin].
          + apply checked_error_expressions_flover_map_add_compat; auto.
          + pose proof (flover_map_el_eq_extension Hsubnin Hin) as [Hexeq Hreq].
            congruence.
      }
Qed.

Lemma validErrorboundAA_sound_plus e1 e2 E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e1 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e2 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Binop Plus e1 e2) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe1 IHe2.
  unfold validErrorboundAA_sound_statement in IHe1, IHe2 |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall;
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Binop Plus e1 e2) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  cbn in Htypecheck.
  destruct (Htypecheck) as (m__e & find_t & (Htypecheck1 & Htypecheck2 & Hjoin) & valid_exec).
  rewrite find_t in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
    as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
    cbn in Hvalidbounds; try congruence.
  destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
    as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
    cbn in Hvalidbounds; try congruence.
  destruct (FloverMap.find e1 subexpr_map2) as [subaf1|] eqn: Hsubaf1;
    cbn in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e2 subexpr_map2) as [subaf2|] eqn: Hsubaf2;
    cbn in Hvalidbounds; [|congruence].
  cbn in Hrange.
  destruct Hrange as [[Hdivvalid Hsubranges] [tmpiv [tmperr [tmpvR [Hres__A' [Heval1' Hcontained]]]]]].
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  pose proof Heval__R as Heval__R'.
  eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
  replace tmpvR with v__R in * by congruence; clear Heval1' Heval__R' tmpvR.
  destruct Hsubranges as [Hrange1 Hrange2].
  pose proof (validRanges_single _ _ _ _ Hrange1)
    as [iv1 [err1 [vR1 [Hres__A1 [Heval1 Hcontained1]]]]].
  pose proof (validRanges_single _ _ _ _ Hrange2)
    as [iv2 [err2 [vR2 [Hres__A2 [Heval2 Hcontained2]]]]].
  rewrite Hres__A1, Hres__A2 in Hvalidbounds.
  specialize (IHe1 expr_map1 subexpr_map1 noise_map1 noise1 subnoise1 vR1 iv1 err1).
  specialize IHe1 as (((nF1 & m1 & IHevex1) & IHchecked1) & IHevall1); eauto;
    [clear - Hsubset; set_tac; set_tac|].
  destruct (Qleb (maxAbs (toIntv
                            (AffineArithQ.plus_aff (AffineArithQ.plus_aff subaf1 subaf2)
                                                   (mkErrorPolyQ
                                                      (computeErrorQ
                                                         (maxAbs (addIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__e)
                                                      subnoise2)))) err__A) eqn: Herrle; [|congruence].
  clear Hdivvalid.
  rewrite Qle_bool_iff in Herrle.
  apply Qle_Rle in Herrle.
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  split.
  * specialize (IHevall1 nF1 m1 IHevex1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1).
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     vR2 iv2 err2).
    specialize IHe2 as (((nF2 & m2 & IHevex2) & IHchecked2) & IHevall2);
      eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - specialize (Hcheckedex _ Hin1).
        intuition.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    destruct Hjoin as (m1' & m2' & Hgamma1 & Hgamma2 & join_exists).
    assert (m1' = m1) as Htmp.
    { eapply validTypes_exec with (e:=e1); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (m2' = m2) as Htmp.
    { eapply validTypes_exec with (e:=e2); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Binop Plus e1 e2)) v__FP m__FP) as H.
    {
      specialize (Hdeltamap (evalBinop Plus nF1 nF2) m__e)
        as (delta' & Hdelta & Hdelta').
      eexists; exists m__e.
      eapply Binop_dist' with (delta := delta'); eauto.
      - congruence.
      - eapply toRExpMap_some; eauto.
        auto.
    }
    pose proof H as H'.
    specialize H' as (? & ? & Heval).
    cbn in Heval.
    inversion Heval; subst.
    specialize (IHevall2 _ _ H10) as (? & ? & ? & ? & ?).
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map1) as [Hin1|Hnin1];
      [specialize (IHchecked1 e' Hnin Hin1); intuition|].
    destruct (flover_map_in_dec e' subexpr_map2) as [Hin2|Hnin2];
      [specialize (IHchecked2 e' Hnin1 Hin2); intuition|].
    destruct (flover_map_el_eq_extension Hnin2 Hin) as [Heq Hexpeq]; auto.
    split; [|split; [|now rewrite Hexpeq]].
    { rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
        try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
      now apply subset_diff_to_subset_union. }
    { erewrite FloverMapFacts.P.F.find_o in Hcert; eauto. }
  * intros * Heval__FPdet.
    inversion Heval__R; subst.
    rename v1 into v__R1; rename v2 into v__R2.
    apply Rabs_0_impl_eq in H5; replace delta with 0%R in *; clear delta H5.
    replace m0 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace m2 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace vR1 with v__R1 in * by (eapply meps_0_deterministic; eauto).
    replace vR2 with v__R2 in * by (eapply meps_0_deterministic; eauto).
    clear m0 m2 vR1 vR2.
    inversion Heval__FPdet; subst.
    rename v1 into v__FP1; rename v2 into v__FP2.
    rename delta into delta__FP.
    rename m0 into m__FP1.
    rename m2 into m__FP2.
    specialize (IHevall1 v__FP1 m__FP1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1);
      eauto.
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     v__R2 iv2 err2).
    edestruct IHe2 as (_ & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    specialize (IHevall2 v__FP2 m__FP2)
      as (ihaf2 & iherr__af2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 & IHcontn2 &
          IHnoise_map2 & IHsub__A2 & IHerrpos2 & IHiv__err2 & IH__err2 & IHevals2 & IHchecked2); auto.
    assert (FloverMap.find (elt:=affine_form Q) e1 subexpr_map2 = Some ihaf1) as tmp
        by now apply IHcontf2.
    replace subaf1 with ihaf1 in * by congruence.
    replace subaf2 with ihaf2 in * by congruence.
    clear tmp subaf1 subaf2.
    replace m__e with m__FP in * by (eapply toRExpMap_some in find_t; eauto); clear m__e.
    destruct (@addition_error_af_evals ihaf1 ihaf2 v__R1 v__R2 v__FP1 v__FP2
                                       iv1 iv2 err1 err2 iherr__af1 iherr__af2
                                       m__FP delta__FP subnoise2 ihnoise_map2)
      as (noise_map2 & ? & ? & ? & Hevalserrpoly); eauto using fresh_monotonic, af_evals_map_extension.
    exists (AffineArithQ.plus_aff (AffineArithQ.plus_aff ihaf1 ihaf2) (mkErrorPolyQ (computeErrorQ (maxAbs (addIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__FP) subnoise2)),
    (RmaxAbsFun (toInterval (plus_aff (plus_aff (afQ2R ihaf1) (afQ2R ihaf2)) (mkErrorPolyR (computeErrorR (Q2R (maxAbs (addIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP) subnoise2))))%R,
    noise_map2.
    rewrite <- maxAbs_impl_RmaxAbs_iv in Herrle.
    rewrite to_interval_to_intv_iv in Herrle.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_mkErrorPolyQ in Herrle |-*.
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    pose (err := computeErrorR (Q2R (maxAbs (addIntv (widenIntv iv1 err1)
                                                     (widenIntv iv2 err2)))) m__FP).
    fold err in Herrle |-*.
    clear H5 H11.
    {
      repeat split; auto.
      - rewrite mem_false_find_none in Hmem.
        epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcontf2].
        assumption.
      - lia.
      - eauto using contained_map_trans.
      - rewrite FloverMapFacts.P.F.add_eq_o; try auto.
        apply Q_orderedExps.exprCompare_refl.
      - unfold RmaxAbsFun.
        apply Rmax_case; apply Rabs_pos.
      - symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
        eapply plus_aff_to_interval_sym_compat with
            (v1 := radius (plus_aff (afQ2R ihaf1) (afQ2R ihaf2))) (v2 := err);
          try apply radius_nonneg; try apply computeErrorR_pos.
        + eapply plus_aff_to_interval_sym_compat with (v1 := iherr__af1) (v2 := iherr__af2); eauto.
        + rewrite toInterval_mkErrorPolyR; unfold err; auto using computeErrorR_pos.
      - intros e' Hnin Hin.
        destruct (q_expr_eq_dec (Binop Plus e1 e2) e') as [Heqexp|Heqexp].
        + unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          intros.
          exists (AffineArithQ.plus_aff (AffineArithQ.plus_aff ihaf1 ihaf2)
                                   (mkErrorPolyQ (computeErrorQ (maxAbs (addIntv
                                                                           (widenIntv iv1 err1)
                                                                           (widenIntv iv2 err2)))
                                                                m__FP) subnoise2)),
          (RmaxAbsFun (toInterval (plus_aff (plus_aff (afQ2R ihaf1) (afQ2R ihaf2))
                                            (mkErrorPolyR (computeErrorR
                                                             (Q2R (maxAbs (addIntv
                                                                             (widenIntv iv1 err1)
                                                                             (widenIntv iv2 err2))))
                                                             m__FP) subnoise2))))%R .
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_mkErrorPolyQ.
          rewrite computeErrorQ_computeErrorR.
          repeat split; try auto.
          * rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          * unfold RmaxAbsFun.
            apply Rmax_case; apply Rabs_pos.
          * symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
            eapply plus_aff_to_interval_sym_compat with
                (v1 := radius (plus_aff (afQ2R ihaf1) (afQ2R ihaf2))) (v2 := err);
              try apply radius_nonneg; try apply computeErrorR_pos.
            1: eapply plus_aff_to_interval_sym_compat with (v1 := iherr__af1) (v2 := iherr__af2); eauto.
            1: rewrite toInterval_mkErrorPolyR; unfold err; auto using computeErrorR_pos.
          * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            now match goal with
                | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                       H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                end.
          * erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := perturb (evalBinop Plus v__R1 v__R2) REAL 0); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := perturb (evalBinop Plus v__FP1 v__FP2) m__FP delta__FP); eauto.
            erewrite Gamma_det; eauto.
        + destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1].
          * apply checked_error_expressions_flover_map_add_compat; eauto.
            eapply checked_error_expressions_extension; try apply IHcheckedall1; eauto.
            2: lia.
            etransitivity; eauto.
          * {
              destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2].
              - apply checked_error_expressions_flover_map_add_compat; eauto.
                eapply checked_error_expressions_extension; try apply IHchecked2; eauto;
                  [lia|reflexivity].
              - pose proof (flover_map_el_eq_extension Hsubnin2 Hin) as [Hexeq Hreq].
                exfalso; apply Heqexp; auto.
            }
    }
Qed.

Lemma validErrorboundAA_sound_sub e1 e2 E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e1 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e2 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Binop Sub e1 e2) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe1 IHe2.
  unfold validErrorboundAA_sound_statement in IHe1, IHe2 |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Binop Sub e1 e2) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  cbn in Htypecheck.
  destruct (Htypecheck) as (m__e & find_t & (Htypecheck1 & Htypecheck2 & Hjoin) & valid_exec).
  rewrite find_t in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
    as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
    cbn in Hvalidbounds; try congruence.
  destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
    as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
    cbn in Hvalidbounds; try congruence.
  destruct (FloverMap.find e1 subexpr_map2) as [subaf1|] eqn: Hsubaf1;
    cbn in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e2 subexpr_map2) as [subaf2|] eqn: Hsubaf2;
    cbn in Hvalidbounds; [|congruence].
  cbn in Hrange.
  destruct Hrange as [[Hdivvalid Hsubranges] [tmpiv [tmperr [tmpvR [Hres__A' [Heval1' Hcontained]]]]]].
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  pose proof Heval__R as Heval__R'.
  eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
  replace tmpvR with v__R in * by congruence; clear Heval1' Heval__R' tmpvR.
  destruct Hsubranges as [Hrange1 Hrange2].
  pose proof (validRanges_single _ _ _ _ Hrange1)
    as [iv1 [err1 [vR1 [Hres__A1 [Heval1 Hcontained1]]]]].
  pose proof (validRanges_single _ _ _ _ Hrange2)
    as [iv2 [err2 [vR2 [Hres__A2 [Heval2 Hcontained2]]]]].
  rewrite Hres__A1, Hres__A2 in Hvalidbounds.
  specialize (IHe1 expr_map1 subexpr_map1 noise_map1 noise1 subnoise1 vR1 iv1 err1).
  specialize IHe1 as (((nF1 & m1 & IHevex1) & IHchecked1) & IHevall1); eauto;
    [clear - Hsubset; set_tac; set_tac|].
  destruct (Qleb (maxAbs (toIntv
                            (AffineArithQ.plus_aff (AffineArithQ.subtract_aff subaf1 subaf2)
                                                   (mkErrorPolyQ
                                                      (computeErrorQ
                                                         (maxAbs (subtractIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__e)
                                                      subnoise2)))) err__A) eqn: Herrle; [|congruence].
  clear Hdivvalid.
  rewrite Qle_bool_iff in Herrle.
  apply Qle_Rle in Herrle.
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  split.
  * specialize (IHevall1 nF1 m1 IHevex1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1).
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     vR2 iv2 err2).
    specialize IHe2 as (((nF2 & m2 & IHevex2) & IHchecked2) & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    destruct Hjoin as (m1' & m2' & Hgamma1 & Hgamma2 & join_exists).
    assert (m1' = m1) as Htmp.
    { eapply validTypes_exec with (e:=e1); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (m2' = m2) as Htmp.
    { eapply validTypes_exec with (e:=e2); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Binop Sub e1 e2)) v__FP m__FP).
    {
      specialize (Hdeltamap (evalBinop Sub nF1 nF2) m__e)
        as (delta' & Hdelta & Hdelta').
      eexists; exists m__e.
      eapply Binop_dist' with (delta := delta'); eauto.
      - congruence.
      - eapply toRExpMap_some; eauto.
        auto.
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map1) as [Hin1|Hnin1]; [apply IHchecked1; auto|].
    destruct (flover_map_in_dec e' subexpr_map2) as [Hin2|Hnin2]; [apply IHchecked2; auto|].
    destruct (flover_map_el_eq_extension Hnin2 Hin) as [Heq Hexpeq]; auto.
    split; [|split; [|now rewrite Hexpeq]].
    { rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
        try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
      now apply subset_diff_to_subset_union. }
    erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  * intros * Heval__FPdet.
    inversion Heval__R; subst.
    rename v1 into v__R1; rename v2 into v__R2.
    apply Rabs_0_impl_eq in H5; replace delta with 0%R in *; clear delta H5.
    replace m0 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace m2 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace vR1 with v__R1 in * by (eapply meps_0_deterministic; eauto).
    replace vR2 with v__R2 in * by (eapply meps_0_deterministic; eauto).
    clear m0 m2 vR1 vR2.
    inversion Heval__FPdet; subst.
    rename v1 into v__FP1; rename v2 into v__FP2.
    rename delta into delta__FP.
    rename m0 into m__FP1.
    rename m2 into m__FP2.
    specialize (IHevall1 v__FP1 m__FP1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1);
      eauto.
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     v__R2 iv2 err2).
    edestruct IHe2 as (_ & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    specialize (IHevall2 v__FP2 m__FP2)
      as (ihaf2 & iherr__af2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 & IHcontn2 &
          IHnoise_map2 & IHsub__A2 & IHerrpos2 & IHiv__err2 & IH__err2 & IHevals2 & IHchecked2); auto.
    assert (FloverMap.find (elt:=affine_form Q) e1 subexpr_map2 = Some ihaf1) as tmp
        by now apply IHcontf2.
    replace subaf1 with ihaf1 in * by congruence.
    replace subaf2 with ihaf2 in * by congruence.
    clear tmp subaf1 subaf2.
    replace m__e with m__FP in * by (eapply toRExpMap_some in find_t; eauto); clear m__e.
    destruct (@subtraction_error_af_evals ihaf1 ihaf2 v__R1 v__R2 v__FP1 v__FP2
                                          iv1 iv2 err1 err2 iherr__af1 iherr__af2
                                          m__FP delta__FP subnoise2 ihnoise_map2)
      as (noise_map2 & ? & ? & ? & Hevalserrpoly);
      eauto using fresh_monotonic, af_evals_map_extension.
    exists (AffineArithQ.plus_aff (AffineArithQ.subtract_aff ihaf1 ihaf2) (mkErrorPolyQ (computeErrorQ (maxAbs (subtractIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__FP) subnoise2)),
    (RmaxAbsFun (toInterval (plus_aff (subtract_aff (afQ2R ihaf1) (afQ2R ihaf2)) (mkErrorPolyR (computeErrorR (Q2R (maxAbs (subtractIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP) subnoise2))))%R,
    noise_map2.
    rewrite <- maxAbs_impl_RmaxAbs_iv in Herrle.
    rewrite to_interval_to_intv_iv in Herrle.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_subtract_aff in Herrle |-*.
    rewrite afQ2R_mkErrorPolyQ in Herrle |-*.
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    pose (err := computeErrorR (Q2R (maxAbs (subtractIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP).
    fold err in Herrle |-*.
    clear H5 H11.
    {
      repeat split; auto.
      - rewrite mem_false_find_none in Hmem.
        epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcontf2].
        assumption.
      - lia.
      - eauto using contained_map_trans.
      - rewrite FloverMapFacts.P.F.add_eq_o; try auto.
        apply Q_orderedExps.exprCompare_refl.
      - unfold RmaxAbsFun.
        apply Rmax_case; apply Rabs_pos.
      - symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
        eauto
          using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
        toInterval_mkErrorPolyR, computeErrorR_pos.
      - intros e' Hnin Hin.
        destruct (q_expr_eq_dec (Binop Sub e1 e2) e') as [Heqexp|Heqexp].
        + unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          intros.
          exists (AffineArithQ.plus_aff (AffineArithQ.subtract_aff ihaf1 ihaf2) (mkErrorPolyQ (computeErrorQ (maxAbs (subtractIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__FP) subnoise2)),
          (RmaxAbsFun (toInterval (plus_aff (subtract_aff (afQ2R ihaf1) (afQ2R ihaf2)) (mkErrorPolyR (computeErrorR (Q2R (maxAbs (subtractIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP) subnoise2))))%R.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_subtract_aff.
          rewrite afQ2R_mkErrorPolyQ.
          rewrite computeErrorQ_computeErrorR.
          repeat split; try auto.
          * rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          * unfold RmaxAbsFun.
            apply Rmax_case; apply Rabs_pos.
          * symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
            eauto
              using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
            toInterval_mkErrorPolyR, computeErrorR_pos.
          * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            now match goal with
                | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                       H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                end.
          * erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := perturb (evalBinop Sub v__R1 v__R2) REAL 0); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := perturb (evalBinop Sub v__FP1 v__FP2) m__FP delta__FP); eauto.
            erewrite Gamma_det; eauto.
        + destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1].
          * apply checked_error_expressions_flover_map_add_compat; eauto.
            eapply checked_error_expressions_extension; try apply IHcheckedall1; eauto.
            2: lia.
            etransitivity; eauto.
          * {
              destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2].
              - apply checked_error_expressions_flover_map_add_compat; eauto.
                eapply checked_error_expressions_extension; try apply IHchecked2; eauto;
                  [lia|reflexivity].
              - pose proof (flover_map_el_eq_extension Hsubnin2 Hin) as [Hexeq Hreq].
                exfalso; apply Heqexp; auto.
            }
    }
Qed.

Lemma validErrorboundAA_sound_mult e1 e2 E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e1 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e2 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Binop Mult e1 e2) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe1 IHe2.
  unfold validErrorboundAA_sound_statement in IHe1, IHe2 |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Binop Mult e1 e2) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  cbn in Htypecheck.
  destruct (Htypecheck) as (m__e & find_t & (Htypecheck1 & Htypecheck2 & Hjoin) & valid_exec).
  rewrite find_t in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
    as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
    cbn in Hvalidbounds; try congruence.
  destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
    as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
    cbn in Hvalidbounds; try congruence.
  destruct (FloverMap.find e1 subexpr_map2) as [subaf1|] eqn: Hsubaf1;
    cbn in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e2 subexpr_map2) as [subaf2|] eqn: Hsubaf2;
    cbn in Hvalidbounds; [|congruence].
  cbn in Hrange.
  destruct Hrange as [[Hdivvalid Hsubranges] [tmpiv [tmperr [tmpvR [Hres__A' [Heval1' Hcontained]]]]]].
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  pose proof Heval__R as Heval__R'.
  eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
  replace tmpvR with v__R in * by congruence; clear Heval1' Heval__R' tmpvR.
  destruct Hsubranges as [Hrange1 Hrange2].
  pose proof (validRanges_single _ _ _ _ Hrange1)
    as [iv1 [err1 [vR1 [Hres__A1 [Heval1 Hcontained1]]]]].
  pose proof (validRanges_single _ _ _ _ Hrange2)
    as [iv2 [err2 [vR2 [Hres__A2 [Heval2 Hcontained2]]]]].
  rewrite Hres__A1, Hres__A2 in Hvalidbounds.
  specialize (IHe1 expr_map1 subexpr_map1 noise_map1 noise1 subnoise1 vR1 iv1 err1).
  specialize IHe1 as (((nF1 & m1 & IHevex1) & IHchecked1) & IHevall1); eauto;
    [clear - Hsubset; set_tac; set_tac|].
  destruct (Qleb (maxAbs (toIntv
                            (AffineArithQ.plus_aff
                               (AffineArithQ.subtract_aff
                                  (AffineArithQ.plus_aff
                                     (AffineArithQ.mult_aff (fromIntv iv1 subnoise2) subaf2
                                                            (subnoise2 + 2))
                                     (AffineArithQ.mult_aff (fromIntv iv2 (subnoise2 + 1))
                                                            subaf1 (subnoise2 + 3)))
                                  (AffineArithQ.mult_aff subaf1 subaf2 (subnoise2 + 4)))
                               (mkErrorPolyQ
                                  (computeErrorQ
                                     (maxAbs
                                        (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))
                                     m__e) (subnoise2 + 5))))) err__A) eqn: Herrle; [|congruence].
  clear Hdivvalid.
  rewrite Qle_bool_iff in Herrle.
  apply Qle_Rle in Herrle.
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  split.
  * specialize (IHevall1 nF1 m1 IHevex1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1).
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     vR2 iv2 err2).
    specialize IHe2 as (((nF2 & m2 & IHevex2) & IHchecked2) & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    destruct Hjoin as (m1' & m2' & Hgamma1 & Hgamma2 & join_exists).
    assert (m1' = m1) as Htmp.
    { eapply validTypes_exec with (e:=e1); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (m2' = m2) as Htmp.
    { eapply validTypes_exec with (e:=e2); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Binop Mult e1 e2)) v__FP m__FP).
    {
      specialize (Hdeltamap (evalBinop Mult nF1 nF2) m__e)
        as (delta' & Hdelta & Hdelta').
      eexists; exists m__e.
      eapply Binop_dist' with (delta := delta'); eauto.
      - congruence.
      - eapply toRExpMap_some; eauto.
        auto.
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map1) as [Hin1|Hnin1]; [apply IHchecked1; auto|].
    destruct (flover_map_in_dec e' subexpr_map2) as [Hin2|Hnin2]; [apply IHchecked2; auto|].
    destruct (flover_map_el_eq_extension Hnin2 Hin) as [Heq Hexpeq]; auto.
    split; [|split; [|now rewrite Hexpeq]].
    1: rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
      try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
    1: now apply subset_diff_to_subset_union.
    erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  * intros * Heval__FPdet.
    inversion Heval__R; subst.
    rename v1 into v__R1; rename v2 into v__R2.
    apply Rabs_0_impl_eq in H5; replace delta with 0%R in *; clear delta H5.
    replace m0 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace m2 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace vR1 with v__R1 in * by (eapply meps_0_deterministic; eauto).
    replace vR2 with v__R2 in * by (eapply meps_0_deterministic; eauto).
    clear m0 m2 vR1 vR2.
    inversion Heval__FPdet; subst.
    rename v1 into v__FP1; rename v2 into v__FP2.
    rename delta into delta__FP.
    rename m0 into m__FP1.
    rename m2 into m__FP2.
    specialize (IHevall1 v__FP1 m__FP1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1);
      eauto.
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     v__R2 iv2 err2).
    edestruct IHe2 as (_ & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    specialize (IHevall2 v__FP2 m__FP2)
      as (ihaf2 & iherr__af2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 & IHcontn2 &
          IHnoise_map2 & IHsub__A2 & IHerrpos2 & IHiv__err2 & IH__err2 & IHevals2 & IHchecked2); auto.
    assert (FloverMap.find (elt:=affine_form Q) e1 subexpr_map2 = Some ihaf1) as tmp
        by now apply IHcontf2.
    replace subaf1 with ihaf1 in * by congruence.
    replace subaf2 with ihaf2 in * by congruence.
    clear tmp subaf1 subaf2.
    replace m__e with m__FP in * by (eapply toRExpMap_some in find_t; eauto); clear m__e.
    destruct (@multiplication_error_af_evals ihaf1 ihaf2 v__R1 v__R2 v__FP1 v__FP2
                                             iv1 iv2 err1 err2 iherr__af1 iherr__af2
                                             m__FP delta__FP subnoise2 ihnoise_map2)
      as (noise_map' & ? & ? & ? & Hevalserrpoly);
      eauto using fresh_monotonic, af_evals_map_extension.
    exists (AffineArithQ.plus_aff
         (AffineArithQ.subtract_aff
            (AffineArithQ.plus_aff
               (AffineArithQ.mult_aff (fromIntv iv1 subnoise2) ihaf2 (subnoise2 + 2))
               (AffineArithQ.mult_aff (fromIntv iv2 (subnoise2 + 1)) ihaf1 (subnoise2 + 3)))
            (AffineArithQ.mult_aff ihaf1 ihaf2 (subnoise2 + 4)))
         (mkErrorPolyQ
            (computeErrorQ (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))
                           m__FP) (subnoise2 + 5))),
    (RmaxAbsFun (toInterval (plus_aff
                               (subtract_aff
                                  (plus_aff
                                     (mult_aff (afQ2R (fromIntv iv1 subnoise2)) (afQ2R ihaf2) (subnoise2 + 2))
                                     (mult_aff (afQ2R (fromIntv iv2 (subnoise2 + 1))) (afQ2R ihaf1) (subnoise2 + 3)))
                                  (mult_aff (afQ2R ihaf1) (afQ2R ihaf2) (subnoise2 + 4)))
                               (mkErrorPolyR
                                  (computeErrorR (Q2R (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))))
                                                 m__FP) (subnoise2 + 5)))))%R,
    noise_map'.
    rewrite <- maxAbs_impl_RmaxAbs_iv in Herrle.
    rewrite to_interval_to_intv_iv in Herrle.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_subtract_aff in Herrle |-*.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mkErrorPolyQ in Herrle |-*.
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    pose (err := computeErrorR (Q2R (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP).
    fold err in Herrle |-*.
    clear H5 H11.
    {
      repeat split; auto.
      - rewrite mem_false_find_none in Hmem.
        epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcontf2].
        assumption.
      - lia.
      - eauto using contained_map_trans.
      - rewrite FloverMapFacts.P.F.add_eq_o; try auto.
        apply Q_orderedExps.exprCompare_refl.
      - unfold RmaxAbsFun.
        apply Rmax_case; apply Rabs_pos.
      - symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
        eauto 8
              using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
        mult_aff_to_interval_sym_compat, mult_aff_to_interval_sym_compat_r,
        toInterval_mkErrorPolyR, computeErrorR_pos, RmaxAbsFun_iv, radius_nonneg.
      - intros e' Hnin Hin.
        destruct (q_expr_eq_dec (Binop Mult e1 e2) e') as [Heqexp|Heqexp].
        + unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          intros.
          exists (AffineArithQ.plus_aff
               (AffineArithQ.subtract_aff
                  (AffineArithQ.plus_aff
                     (AffineArithQ.mult_aff (fromIntv iv1 subnoise2) ihaf2 (subnoise2 + 2))
                     (AffineArithQ.mult_aff (fromIntv iv2 (subnoise2 + 1)) ihaf1 (subnoise2 + 3)))
                  (AffineArithQ.mult_aff ihaf1 ihaf2 (subnoise2 + 4)))
               (mkErrorPolyQ
                  (computeErrorQ (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))
                                 m__FP) (subnoise2 + 5))),
          (RmaxAbsFun (toInterval (plus_aff
                                     (subtract_aff
                                        (plus_aff
                                           (mult_aff (afQ2R (fromIntv iv1 subnoise2)) (afQ2R ihaf2) (subnoise2 + 2))
                                           (mult_aff (afQ2R (fromIntv iv2 (subnoise2 + 1))) (afQ2R ihaf1) (subnoise2 + 3)))
                                        (mult_aff (afQ2R ihaf1) (afQ2R ihaf2) (subnoise2 + 4)))
                                     (mkErrorPolyR
                                        (computeErrorR (Q2R (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))))
                                                       m__FP) (subnoise2 + 5)))))%R.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_subtract_aff.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mkErrorPolyQ.
          rewrite computeErrorQ_computeErrorR.
          repeat split; try auto.
          * rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          * unfold RmaxAbsFun.
            apply Rmax_case; apply Rabs_pos.
          * symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
            eauto 8
                  using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
            mult_aff_to_interval_sym_compat, mult_aff_to_interval_sym_compat_r,
            toInterval_mkErrorPolyR, computeErrorR_pos, RmaxAbsFun_iv, radius_nonneg.
          * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            now match goal with
                | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                       H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                end.
          * erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := perturb (evalBinop Mult v__R1 v__R2) REAL 0); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := perturb (evalBinop Mult v__FP1 v__FP2) m__FP delta__FP); eauto.
            erewrite Gamma_det; eauto.
        + destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1].
          * apply checked_error_expressions_flover_map_add_compat; eauto.
            eapply checked_error_expressions_extension; try apply IHcheckedall1; eauto.
            2: lia.
            etransitivity; eauto.
          * {
              destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2].
              - apply checked_error_expressions_flover_map_add_compat; eauto.
                eapply checked_error_expressions_extension; try apply IHchecked2; eauto;
                  [lia|reflexivity].
              - pose proof (flover_map_el_eq_extension Hsubnin2 Hin) as [Hexeq Hreq].
                exfalso; apply Heqexp; auto.
            }
    }
Qed.

Lemma validErrorboundAA_sound_div e1 e2 E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e1 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e2 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Binop Div e1 e2) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe1 IHe2.
  unfold validErrorboundAA_sound_statement in IHe1, IHe2 |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Binop Div e1 e2) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  cbn in Htypecheck.
  destruct (Htypecheck) as (m__e & find_t & (Htypecheck1 & Htypecheck2 & Hjoin) & valid_exec).
  rewrite find_t in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
    as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
    cbn in Hvalidbounds; try congruence.
  destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
    as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
    cbn in Hvalidbounds; try congruence.
  destruct (FloverMap.find e1 subexpr_map2) as [subaf1|] eqn: Hsubaf1;
    cbn in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e2 subexpr_map2) as [subaf2|] eqn: Hsubaf2;
    cbn in Hvalidbounds; [|congruence].
  cbn in Hrange.
  destruct Hrange as [[Hdivvalid Hsubranges] [tmpiv [tmperr [tmpvR [Hres__A' [Heval1' Hcontained]]]]]].
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  pose proof Heval__R as Heval__R'.
  eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
  replace tmpvR with v__R in * by congruence; clear Heval1' Heval__R' tmpvR.
  destruct Hsubranges as [Hrange1 Hrange2].
  pose proof (validRanges_single _ _ _ _ Hrange1)
    as [iv1 [err1 [vR1 [Hres__A1 [Heval1 Hcontained1]]]]].
  pose proof (validRanges_single _ _ _ _ Hrange2)
    as [iv2 [err2 [vR2 [Hres__A2 [Heval2 Hcontained2]]]]].
  rewrite Hres__A1, Hres__A2 in Hvalidbounds.
  specialize (IHe1 expr_map1 subexpr_map1 noise_map1 noise1 subnoise1 vR1 iv1 err1).
  specialize IHe1 as (((nF1 & m1 & IHevex1) & IHchecked1) & IHevall1); eauto;
    [clear - Hsubset; set_tac; set_tac|].
  destruct (Qleb (snd iv2 + err2) 0 && negb (Qeq_bool (snd iv2 + err2) 0)
            || Qleb 0 (fst iv2 - err2) && negb (Qeq_bool (fst iv2 - err2) 0)) eqn: Hnonzero;
    [|congruence].
  rewrite orb_true_iff in Hnonzero.
  rewrite andb_true_iff in Hnonzero.
  rewrite andb_true_iff in Hnonzero.
  rewrite Qle_bool_iff in Hnonzero.
  rewrite Qle_bool_iff in Hnonzero.
  rewrite negb_true_iff in Hnonzero.
  rewrite negb_true_iff in Hnonzero.
  destruct (Qleb
              (maxAbs
                 (toIntv
                    (AffineArithQ.plus_aff
                       (AffineArithQ.plus_aff
                          (AffineArithQ.subtract_aff
                             (AffineArithQ.mult_aff subaf1
                                                    (fromIntv (invertIntv iv2) (subnoise2 + 1))
                                                    (subnoise2 + 4))
                             (AffineArithQ.mult_aff (fromIntv iv1 subnoise2)
                                                    (AffineArithQ.mult_aff subaf2
                                                                           (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                                                     (subnoise2 + 2)) (subnoise2 + 3))
                                                    (subnoise2 + 5)))
                          (AffineArithQ.mult_aff subaf1
                                                 (AffineArithQ.mult_aff subaf2
                                                                        (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                                                  (subnoise2 + 2)) (subnoise2 + 3))
                                                 (subnoise2 + 6)))
                       (mkErrorPolyQ
                          (computeErrorQ
                             (maxAbs (divideIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))
                             m__e) (subnoise2 + 7))))) err__A) eqn: Herrle; [|congruence].
  clear Hdivvalid.
  rewrite Qle_bool_iff in Herrle.
  apply Qle_Rle in Herrle.
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  split.
  * specialize (IHevall1 nF1 m1 IHevex1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1).
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     vR2 iv2 err2).
    specialize IHe2 as (((nF2 & m2 & IHevex2) & IHchecked2) & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    destruct Hjoin as (m1' & m2' & Hgamma1 & Hgamma2 & join_exists).
    assert (m1' = m1) as Htmp.
    { eapply validTypes_exec with (e:=e1); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (m2' = m2) as Htmp.
    { eapply validTypes_exec with (e:=e2); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Binop Div e1 e2)) v__FP m__FP).
    {
      specialize (Hdeltamap (evalBinop Div nF1 nF2) m__e)
        as (delta' & Hdelta & Hdelta').
      eexists; exists m__e.
      eapply Binop_dist' with (delta := delta'); eauto.
      - intros _.
        specialize (IHevall2 nF2 m2)
          as (ihaf2 & iherr2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 &
              IHcontn2 & IHnoise_map2 & IHfind2 & IHerr2 & IHiv2 & IHbound2 & IHevals2 &
              IHcheckedall2); auto.
        eapply contained' in Hcontained2; eauto.
        clear - Hnonzero Hcontained2.
        destruct Hnonzero as [H'|H']; destruct H' as [Hle Heq]; apply Qeq_bool_neq in Heq;
          apply Qle_Rle in Hle; intros Hz; apply Heq; apply eqR_Qeq.
        + rewrite Q2R_plus in Hle |-*.
          lra.
        + rewrite Q2R_minus in Hle |-*.
          lra.
      - eapply toRExpMap_some; eauto.
        auto.
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map1) as [Hin1|Hnin1]; [apply IHchecked1; auto|].
    destruct (flover_map_in_dec e' subexpr_map2) as [Hin2|Hnin2]; [apply IHchecked2; auto|].
    destruct (flover_map_el_eq_extension Hnin2 Hin) as [Heq Hexpeq]; auto.
    split; [|split; [|now rewrite Hexpeq]].
    1: rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
      try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
    1: now apply subset_diff_to_subset_union.
    erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  * intros * Heval__FPdet.
    inversion Heval__R; subst.
    rename v1 into v__R1; rename v2 into v__R2.
    apply Rabs_0_impl_eq in H5; replace delta with 0%R in *; clear delta H5.
    replace m0 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace m2 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace vR1 with v__R1 in * by (eapply meps_0_deterministic; eauto).
    replace vR2 with v__R2 in * by (eapply meps_0_deterministic; eauto).
    clear m0 m2 vR1 vR2.
    inversion Heval__FPdet; subst.
    rename v1 into v__FP1; rename v2 into v__FP2.
    rename delta into delta__FP.
    rename m0 into m__FP1.
    rename m2 into m__FP2.
    specialize (IHevall1 v__FP1 m__FP1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1);
      eauto.
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     v__R2 iv2 err2).
    edestruct IHe2 as (_ & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    specialize (IHevall2 v__FP2 m__FP2)
      as (ihaf2 & iherr__af2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 & IHcontn2 &
          IHnoise_map2 & IHsub__A2 & IHerrpos2 & IHiv__err2 & IH__err2 & IHevals2 & IHchecked2); auto.
    assert (FloverMap.find (elt:=affine_form Q) e1 subexpr_map2 = Some ihaf1) as tmp
        by now apply IHcontf2.
    replace subaf1 with ihaf1 in * by congruence.
    replace subaf2 with ihaf2 in * by congruence.
    clear tmp subaf1 subaf2.
    replace m__e with m__FP in * by (eapply toRExpMap_some in find_t; eauto); clear m__e.
    destruct (@division_error_af_evals ihaf1 ihaf2 v__R1 v__R2 v__FP1 v__FP2
                                       iv1 iv2 err1 err2 iherr__af1 iherr__af2
                                       m__FP delta__FP subnoise2 ihnoise_map2)
      as (noise_map' & ? & ? & ? & Hevalserrpoly);
      eauto using fresh_monotonic, af_evals_map_extension, Rle_trans.
    exists (AffineArithQ.plus_aff
         (AffineArithQ.plus_aff
            (AffineArithQ.subtract_aff
               (AffineArithQ.mult_aff ihaf1 (fromIntv (invertIntv iv2) (subnoise2 + 1))
                                      (subnoise2 + 4))
               (AffineArithQ.mult_aff (fromIntv iv1 subnoise2)
                                      (AffineArithQ.mult_aff ihaf2
                                                             (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2))) (subnoise2 + 2))
                                                             (subnoise2 + 3)) (subnoise2 + 5)))
            (AffineArithQ.mult_aff ihaf1
                                   (AffineArithQ.mult_aff ihaf2
                                                          (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2))) (subnoise2 + 2))
                                                          (subnoise2 + 3)) (subnoise2 + 6)))
         (mkErrorPolyQ
            (computeErrorQ (maxAbs (divideIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__FP)
            (subnoise2 + 7))),
    (RmaxAbsFun (toInterval
                   (plus_aff
                      (plus_aff
                         (subtract_aff
                            (mult_aff (afQ2R ihaf1) (afQ2R (fromIntv (invertIntv iv2) (subnoise2 + 1)))
                                      (subnoise2 + 4))
                            (mult_aff (afQ2R (fromIntv iv1 subnoise2))
                                      (mult_aff (afQ2R ihaf2)
                                                (afQ2R (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                                 (subnoise2 + 2)))
                                                (subnoise2 + 3)) (subnoise2 + 5)))
                         (mult_aff (afQ2R ihaf1)
                                   (mult_aff (afQ2R ihaf2)
                                             (afQ2R (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                              (subnoise2 + 2)))
                                             (subnoise2 + 3)) (subnoise2 + 6)))
                      (mkErrorPolyR
                         (computeErrorR (Q2R (maxAbs (divideIntv (widenIntv iv1 err1) (widenIntv iv2 err2))))
                                        m__FP)
                         (subnoise2 + 7))))),
    noise_map'.
    rewrite <- maxAbs_impl_RmaxAbs_iv in Herrle.
    rewrite to_interval_to_intv_iv in Herrle.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_subtract_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mkErrorPolyQ in Herrle |-*.
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    pose (err := computeErrorR (Q2R (maxAbs (divideIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP).
    fold err in Herrle |-*.
    clear H5 H11.
    {
      repeat split; auto.
      - rewrite mem_false_find_none in Hmem.
        epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcontf2].
        assumption.
      - lia.
      - eauto using contained_map_trans.
      - rewrite FloverMapFacts.P.F.add_eq_o; try auto.
        apply Q_orderedExps.exprCompare_refl.
      - unfold RmaxAbsFun.
        apply Rmax_case; apply Rabs_pos.
      - symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
        eauto 9
              using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
        mult_aff_to_interval_sym_compat, mult_aff_to_interval_sym_compat_l,
        mult_aff_to_interval_sym_compat_r, toInterval_mkErrorPolyR, computeErrorR_pos,
        RmaxAbsFun_iv, radius_nonneg.
      - intros e' Hnin Hin.
        destruct (q_expr_eq_dec (Binop Div e1 e2) e') as [Heqexp|Heqexp].
        + unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          exists (AffineArithQ.plus_aff
               (AffineArithQ.plus_aff
                  (AffineArithQ.subtract_aff
                     (AffineArithQ.mult_aff ihaf1 (fromIntv (invertIntv iv2) (subnoise2 + 1))
                                            (subnoise2 + 4))
                     (AffineArithQ.mult_aff (fromIntv iv1 subnoise2)
                                            (AffineArithQ.mult_aff ihaf2
                                                                   (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2))) (subnoise2 + 2))
                                                                   (subnoise2 + 3)) (subnoise2 + 5)))
                  (AffineArithQ.mult_aff ihaf1
                                         (AffineArithQ.mult_aff ihaf2
                                                                (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2))) (subnoise2 + 2))
                                                                (subnoise2 + 3)) (subnoise2 + 6)))
               (mkErrorPolyQ
                  (computeErrorQ (maxAbs (divideIntv (widenIntv iv1 err1) (widenIntv iv2 err2))) m__FP)
                  (subnoise2 + 7))),
          (RmaxAbsFun (toInterval
                         (plus_aff
                            (plus_aff
                               (subtract_aff
                                  (mult_aff (afQ2R ihaf1) (afQ2R (fromIntv (invertIntv iv2) (subnoise2 + 1)))
                                            (subnoise2 + 4))
                                  (mult_aff (afQ2R (fromIntv iv1 subnoise2))
                                            (mult_aff (afQ2R ihaf2)
                                                      (afQ2R (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                                       (subnoise2 + 2)))
                                                      (subnoise2 + 3)) (subnoise2 + 5)))
                               (mult_aff (afQ2R ihaf1)
                                         (mult_aff (afQ2R ihaf2)
                                                   (afQ2R (fromIntv (invertIntv (multIntv iv2 (widenIntv iv2 err2)))
                                                                    (subnoise2 + 2)))
                                                   (subnoise2 + 3)) (subnoise2 + 6)))
                            (mkErrorPolyR
                               (computeErrorR (Q2R (maxAbs (divideIntv (widenIntv iv1 err1) (widenIntv iv2 err2))))
                                              m__FP)
                               (subnoise2 + 7))))).
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_subtract_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mkErrorPolyQ.
          intros.
          rewrite computeErrorQ_computeErrorR.
          repeat split; try auto.
          * rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          * unfold RmaxAbsFun.
            apply Rmax_case; apply Rabs_pos.
          * symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
            eauto 9
                  using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
            mult_aff_to_interval_sym_compat, mult_aff_to_interval_sym_compat_l,
            mult_aff_to_interval_sym_compat_r, toInterval_mkErrorPolyR, computeErrorR_pos,
            RmaxAbsFun_iv, radius_nonneg.
          * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            now match goal with
                | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                       H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                end.
          * erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := perturb (evalBinop Div v__R1 v__R2) REAL 0); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := perturb (evalBinop Div v__FP1 v__FP2) m__FP delta__FP); eauto.
            erewrite Gamma_det; eauto.
        + destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1].
          * apply checked_error_expressions_flover_map_add_compat; eauto.
            eapply checked_error_expressions_extension; try apply IHcheckedall1; eauto.
            2: lia.
            etransitivity; eauto.
          * {
              destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2].
              - apply checked_error_expressions_flover_map_add_compat; eauto.
                eapply checked_error_expressions_extension; try apply IHchecked2; eauto;
                  [lia|reflexivity].
              - pose proof (flover_map_el_eq_extension Hsubnin2 Hin) as [Hexeq Hreq].
                exfalso; apply Heqexp; auto.
            }
    }
Qed.

Lemma validErrorboundAA_sound_binop b e1 e2 E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e1 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e2 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Binop b e1 e2) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  destruct b; auto using validErrorboundAA_sound_plus, validErrorboundAA_sound_sub,
              validErrorboundAA_sound_mult, validErrorboundAA_sound_div.
Qed.

Lemma validErrorboundAA_sound_fma e1 e2 e3 E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e1 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e2 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement e3 E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Fma e1 e2 e3) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe1 IHe2 IHe3.
  unfold validErrorboundAA_sound_statement in IHe1, IHe2, IHe3 |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Fma e1 e2 e3) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  cbn in Htypecheck.
  destruct (Htypecheck) as (m__e & find_t & (Htypecheck1 & Htypecheck2 & Htypecheck3 & Hjoin)
                            & valid_exec).
  rewrite find_t in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (validErrorboundAA e1 Gamma A dVars noise1 expr_map1)
    as [(subexpr_map1, subnoise1)|] eqn: Hvalidsubexpr1;
    cbn in Hvalidbounds; try congruence.
  destruct (validErrorboundAA e2 Gamma A dVars subnoise1 subexpr_map1)
    as [(subexpr_map2, subnoise2)|] eqn: Hvalidsubexpr2;
    cbn in Hvalidbounds; try congruence.
  destruct (validErrorboundAA e3 Gamma A dVars subnoise2 subexpr_map2)
    as [(subexpr_map3, subnoise3)|] eqn: Hvalidsubexpr3;
    cbn in Hvalidbounds; try congruence.
  destruct (FloverMap.find e1 subexpr_map3) as [subaf1|] eqn: Hsubaf1;
    cbn in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e2 subexpr_map3) as [subaf2|] eqn: Hsubaf2;
    cbn in Hvalidbounds; [|congruence].
  destruct (FloverMap.find e3 subexpr_map3) as [subaf3|] eqn: Hsubaf3;
    cbn in Hvalidbounds; [|congruence].
  cbn in Hrange.
  destruct Hrange as (Hsubranges & tmpiv & tmperr & tmpvR & Hres__A' & Heval1' & Hcontained).
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  pose proof Heval__R as Heval__R'.
  eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
  cbn in Heval__R'.
  replace tmpvR with v__R in * by congruence; clear Heval1' Heval__R' tmpvR.
  destruct Hsubranges as (Hrange1 & Hrange2 & Hrange3).
  pose proof (validRanges_single _ _ _ _ Hrange1)
    as (iv1 & err1 & vR1 & Hres__A1 & Heval1 & Hcontained1).
  pose proof (validRanges_single _ _ _ _ Hrange2)
    as (iv2 & err2 & vR2 & Hres__A2 & Heval2 & Hcontained2).
  pose proof (validRanges_single _ _ _ _ Hrange3)
    as (iv3 & err3 & vR3 & Hres__A3 & Heval3 & Hcontained3).
  rewrite Hres__A1, Hres__A2, Hres__A3 in Hvalidbounds.
  destruct (Qleb (maxAbs (toIntv
                            (AffineArithQ.plus_aff
                               (AffineArithQ.plus_aff
                                  (AffineArithQ.subtract_aff
                                     (AffineArithQ.plus_aff
                                        (AffineArithQ.mult_aff (fromIntv iv1 subnoise3) subaf2
                                                               (subnoise3 + 2))
                                        (AffineArithQ.mult_aff (fromIntv iv2 (subnoise3 + 1))
                                                               subaf1 (subnoise3 + 3)))
                                     (AffineArithQ.mult_aff subaf1 subaf2 (subnoise3 + 4)))
                                  subaf3)
                               (mkErrorPolyQ
                                  (computeErrorQ
                                     (maxAbs
                                        (addIntv
                                           (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))
                                           (widenIntv iv3 err3)))
                                     m__e) (subnoise3 + 5))))) err__A) eqn: Herrle; [|congruence].
  rewrite Qle_bool_iff in Herrle.
  apply Qle_Rle in Herrle.
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  specialize (IHe1 expr_map1 subexpr_map1 noise_map1 noise1 subnoise1 vR1 iv1 err1).
  specialize IHe1 as (((nF1 & m1 & IHevex1) & IHchecked1) & IHevall1); eauto;
    [clear - Hsubset; set_tac; set_tac|].
  split.
  + specialize (IHevall1 nF1 m1 IHevex1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1).
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     vR2 iv2 err2).
    specialize IHe2 as (((nF2 & m2 & IHevex2) & IHchecked2) & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    specialize (IHevall2 nF2 m2 IHevex2)
      as (ihaf2 & iherr__af2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 & IHcontn2 &
          IHnoise_map2 & IHsub__A2 & IHerrpos2 & IHiv__err2 & IH__err2 & IHevals2 & IHcheckedall2).
    specialize (IHe3 subexpr_map2 subexpr_map3 ihnoise_map2 subnoise2 subnoise3
                     vR3 iv3 err3).
    specialize IHe3 as (((nF3 & m3 & IHevex3) & IHchecked3) & IHevall3); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto;
      eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - destruct (flover_map_in_dec e' subexpr_map1).
        + eapply IHchecked1; eauto.
        + eapply IHchecked2; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto;
          etransitivity; eauto.
      - destruct (flover_map_in_dec e' subexpr_map1) as [Hin2|Hnin2].
        + eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
        + eapply checked_error_expressions_extension; try apply IHcheckedall2; auto; reflexivity.
    }
    destruct Hjoin as (m1' & m2' & m3' & Hgamma1 & Hgamma2 & Hgamma3 & join_exists).
    assert (m1' = m1) as Htmp.
    { eapply validTypes_exec with (e:=e1); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (m2' = m2) as Htmp.
    { eapply validTypes_exec with (e:=e2); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (m3' = m3) as Htmp.
    { eapply validTypes_exec with (e:=e3); eauto; eapply eval_det_eval_nondet; eauto. }
    rewrite Htmp in *; clear Htmp.
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Fma e1 e2 e3)) v__FP m__FP).
    {
      specialize (Hdeltamap (evalFma nF1 nF2 nF3) m__e)
        as (delta' & Hdelta & Hdelta').
      eexists; exists m__e.
      eapply Fma_dist' with (delta:= delta'); eauto.
      eapply toRExpMap_some; eauto.
      auto.
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map1) as [Hin1|Hnin1]; [apply IHchecked1; auto|].
    destruct (flover_map_in_dec e' subexpr_map2) as [Hin2|Hnin2]; [apply IHchecked2; auto|].
    destruct (flover_map_in_dec e' subexpr_map3) as [Hin3|Hnin3]; [apply IHchecked3; auto|].
    destruct (flover_map_el_eq_extension Hnin3 Hin) as [Heq Hexpeq]; auto.
    split; [|split; [|now rewrite Hexpeq]].
    1: rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
      try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
    1: now apply subset_diff_to_subset_union.
    erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  + intros * Heval__FPdet.
    inversion Heval__R; subst.
    rename v1 into v__R1; rename v2 into v__R2; rename v3 into v__R3.
    apply Rabs_0_impl_eq in H5; replace delta with 0%R in *; clear delta H5.
    replace m0 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace m2 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace m3 with REAL in * by (symmetry; eapply toRTMap_eval_REAL; eauto).
    replace vR1 with v__R1 in * by (eapply meps_0_deterministic; eauto).
    replace vR2 with v__R2 in * by (eapply meps_0_deterministic; eauto).
    replace vR3 with v__R3 in * by (eapply meps_0_deterministic; eauto).
    clear m0 m2 m3 vR1 vR2 vR3.
    inversion Heval__FPdet; subst.
    rename v1 into v__FP1; rename v2 into v__FP2; rename v3 into v__FP3.
    rename delta into delta__FP.
    rename m0 into m__FP1.
    rename m2 into m__FP2.
    rename m3 into m__FP3.
    specialize (IHevall1 v__FP1 m__FP1)
      as (ihaf1 & iherr__af1 & ihnoise_map1 & IHcontf1 & IHnoise1 & IHfresh1 & IHcontn1 &
          IHnoise_map1 & IHsub__A1 & IHerrpos1 & IHiv__err1 & IH__err1 & IHevals1 & IHcheckedall1);
      eauto.
    specialize (IHe2 subexpr_map1 subexpr_map2 ihnoise_map1 subnoise1 subnoise2
                     v__R2 iv2 err2).
    edestruct IHe2 as (((nF2 & m2 & IHevex2) & IHchecked2) & IHevall2); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eapply dVars_contained_extension; eauto.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - eapply IHchecked1; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto.
      - eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
    }
    specialize (IHevall2 v__FP2 m__FP2)
      as (ihaf2 & iherr__af2 & ihnoise_map2 & IHcontf2 & IHnoise2 & IHfresh2 & IHcontn2 &
          IHnoise_map2 & IHsub__A2 & IHerrpos2 & IHiv__err2 & IH__err2 & IHevals2 & IHcheckedall2); auto.
    specialize (IHe3 subexpr_map2 subexpr_map3 ihnoise_map2 subnoise2 subnoise3
                     v__R3 iv3 err3).
    edestruct IHe3 as (((nF3 & m3 & IHevex3) & IHchecked3) & IHevall3); eauto.
    1: clear - Hsubset; set_tac; set_tac.
    1: lia.
    1: eauto using dVars_contained_extension.
    {
      intros e' Hin.
      destruct (flover_map_in_dec e' expr_map1).
      - eapply Hcheckedex; eauto.
      - destruct (flover_map_in_dec e' subexpr_map1).
        + eapply IHchecked1; eauto.
        + eapply IHchecked2; eauto.
    }
    {
      intros.
      destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
      - eapply checked_error_expressions_extension; try apply Hcheckedall; auto;
          etransitivity; eauto.
      - destruct (flover_map_in_dec e' subexpr_map1) as [Hin2|Hnin2].
        + eapply checked_error_expressions_extension; try apply IHcheckedall1; auto; reflexivity.
        + eapply checked_error_expressions_extension; try apply IHcheckedall2; auto; reflexivity.
    }
    specialize (IHevall3 v__FP3 m__FP3)
      as (ihaf3 & iherr__af3 & ihnoise_map3 & IHcontf3 & IHnoise3 & IHfresh3 & IHcontn3 &
          IHnoise_map3 & IHsub__A3 & IHerrpos3 & IHiv__err3 & IH__err3 & IHevals3 & IHcheckedall3); auto.
    assert (FloverMap.find (elt:=affine_form Q) e1 subexpr_map3 = Some ihaf1) as tmp
        by now (apply IHcontf3; apply IHcontf2).
    assert (FloverMap.find (elt:=affine_form Q) e2 subexpr_map3 = Some ihaf2) as tmp'
        by now apply IHcontf3.
    replace subaf1 with ihaf1 in * by congruence.
    replace subaf2 with ihaf2 in * by congruence.
    replace subaf3 with ihaf3 in * by congruence.
    clear tmp tmp' subaf1 subaf2 subaf3.
    replace m__e with m__FP in * by (eapply toRExpMap_some in find_t; eauto); clear m__e.
    destruct (@fma_error_af_evals ihaf1 ihaf2 ihaf3 v__R1 v__R2 v__R3 v__FP1 v__FP2 v__FP3
                                  iv1 iv2 iv3 err1 err2 err3 iherr__af1 iherr__af2 iherr__af3
                                  m__FP delta__FP subnoise3 ihnoise_map3)
      as (noise_map' & ? & ? & ? & Hevalserrpoly);
      eauto using fresh_monotonic, af_evals_map_extension.
    exists (AffineArithQ.plus_aff
         (AffineArithQ.plus_aff
            (AffineArithQ.subtract_aff
               (AffineArithQ.plus_aff
                  (AffineArithQ.mult_aff (fromIntv iv1 subnoise3) ihaf2 (subnoise3 + 2))
                  (AffineArithQ.mult_aff (fromIntv iv2 (subnoise3 + 1)) ihaf1
                                         (subnoise3 + 3))) (AffineArithQ.mult_aff ihaf1 ihaf2 (subnoise3 + 4)))
            ihaf3)
         (mkErrorPolyQ
            (computeErrorQ
               (maxAbs
                  (addIntv (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))
                           (widenIntv iv3 err3))) m__FP)
            (subnoise3 + 5))),
    (RmaxAbsFun (toInterval (plus_aff
                               (plus_aff (subtract_aff
                                            (plus_aff
                                               (mult_aff (afQ2R (fromIntv iv1 subnoise3)) (afQ2R ihaf2) (subnoise3 + 2))
                                               (mult_aff (afQ2R (fromIntv iv2 (subnoise3 + 1))) (afQ2R ihaf1)
                                                         (subnoise3 + 3))) (mult_aff (afQ2R ihaf1) (afQ2R ihaf2) (subnoise3 + 4)))
                                         (afQ2R ihaf3))
                               (mkErrorPolyR
                                  (computeErrorR
                                     (Q2R (maxAbs
                                             (addIntv (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))
                                                      (widenIntv iv3 err3)))) m__FP)
                                  (subnoise3 + 5)))))%R,
    noise_map'.
    rewrite <- maxAbs_impl_RmaxAbs_iv in Herrle.
    rewrite to_interval_to_intv_iv in Herrle.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_subtract_aff in Herrle |-*.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mult_aff in Herrle |-*.
    rewrite afQ2R_mkErrorPolyQ in Herrle |-*.
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    pose (err := computeErrorR (Q2R (maxAbs (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2)))) m__FP).
    fold err in Herrle |-*.
    clear H5 H11.
    {
      repeat split; auto.
      - rewrite mem_false_find_none in Hmem.
        epose proof (contained_flover_map_extension _ _ _ Hmem) as G.
        etransitivity; [exact G|].
        apply contained_flover_map_add_compat.
        etransitivity; [|exact IHcontf3].
        etransitivity; [|exact IHcontf2].
        assumption.
      - lia.
      - eauto using contained_map_trans.
      - rewrite FloverMapFacts.P.F.add_eq_o; try auto.
        apply Q_orderedExps.exprCompare_refl.
      - unfold RmaxAbsFun.
        apply Rmax_case; apply Rabs_pos.
      - symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
        eauto 9
              using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
        mult_aff_to_interval_sym_compat, mult_aff_to_interval_sym_compat_r,
        toInterval_mkErrorPolyR, computeErrorR_pos, RmaxAbsFun_iv, radius_nonneg.
      - intros e' Hnin Hin.
        destruct (q_expr_eq_dec (Fma e1 e2 e3) e') as [Heqexp|Heqexp].
        + unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          intros.
          exists (AffineArithQ.plus_aff
               (AffineArithQ.plus_aff (AffineArithQ.subtract_aff
                                         (AffineArithQ.plus_aff
                                            (AffineArithQ.mult_aff (fromIntv iv1 subnoise3) ihaf2 (subnoise3 + 2))
                                            (AffineArithQ.mult_aff (fromIntv iv2 (subnoise3 + 1)) ihaf1
                                                                   (subnoise3 + 3))) (AffineArithQ.mult_aff ihaf1 ihaf2 (subnoise3 + 4)))
               ihaf3)
               (mkErrorPolyQ
                  (computeErrorQ
                     (maxAbs
                        (addIntv (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))
                                 (widenIntv iv3 err3))) m__FP)
                  (subnoise3 + 5))),
          (RmaxAbsFun (toInterval (plus_aff
                                     (plus_aff (subtract_aff
                                                  (plus_aff
                                                     (mult_aff (afQ2R (fromIntv iv1 subnoise3)) (afQ2R ihaf2) (subnoise3 + 2))
                                                     (mult_aff (afQ2R (fromIntv iv2 (subnoise3 + 1))) (afQ2R ihaf1)
                                                               (subnoise3 + 3))) (mult_aff (afQ2R ihaf1) (afQ2R ihaf2) (subnoise3 + 4)))
                                     (afQ2R ihaf3))
                                     (mkErrorPolyR
                                        (computeErrorR
                                           (Q2R (maxAbs
                                                   (addIntv (multIntv (widenIntv iv1 err1) (widenIntv iv2 err2))
                                                            (widenIntv iv3 err3)))) m__FP)
                                        (subnoise3 + 5)))))%R.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_subtract_aff.
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mult_aff.
          rewrite afQ2R_mkErrorPolyQ.
          rewrite computeErrorQ_computeErrorR.
          repeat split; try auto.
          * rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          * unfold RmaxAbsFun.
            apply Rmax_case; apply Rabs_pos.
          * symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
            eauto 9
                  using plus_aff_to_interval_sym_compat, subtract_aff_to_interval_sym_compat,
            mult_aff_to_interval_sym_compat, mult_aff_to_interval_sym_compat_r,
            toInterval_mkErrorPolyR, computeErrorR_pos, RmaxAbsFun_iv, radius_nonneg.
          * erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            now match goal with
                | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                       H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                end.
          * erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := perturb (evalFma v__R1 v__R2 v__R3) REAL 0); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := perturb (evalFma v__FP1 v__FP2 v__FP3) m__FP delta__FP); eauto.
            erewrite Gamma_det; eauto.
        + destruct (flover_map_in_dec e' subexpr_map1) as [Hsubin1|Hsubnin1].
          * apply checked_error_expressions_flover_map_add_compat; eauto.
            eapply checked_error_expressions_extension; try apply IHcheckedall1;
              eauto; [|lia|]; etransitivity; eauto; etransitivity; eauto.
          * {
              destruct (flover_map_in_dec e' subexpr_map2) as [Hsubin2|Hsubnin2].
              - apply checked_error_expressions_flover_map_add_compat; eauto.
                eapply checked_error_expressions_extension; try apply IHcheckedall2; eauto;
                  [etransitivity; eauto|lia].
              - destruct (flover_map_in_dec e' subexpr_map3) as [Hsubin3|Hsubnin3].
                + apply checked_error_expressions_flover_map_add_compat; eauto.
                  eapply checked_error_expressions_extension; try apply IHcheckedall3; eauto;
                    [lia|reflexivity].
                + pose proof (flover_map_el_eq_extension Hsubnin3 Hin) as [Hexeq Hreq].
                  exfalso; apply Heqexp; auto.
            }
    }
Qed.

Lemma validErrorboundAA_sound_downcast m e E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e E1 E2 A Gamma DeltaMap fVars dVars ->
  validErrorboundAA_sound_statement (Downcast m e) E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  intros IHe.
  unfold validErrorboundAA_sound_statement in IHe |-*.
  intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds
                     Hsubset Htypecheck Hcert Hnoise1 Hnoise_map1 Hdvars
                     Hcheckedex Hcheckedall.
  cbn in Hvalidbounds.
  destruct (FloverMap.mem (Downcast m e) expr_map1) eqn: Hmem; cbn in Hvalidbounds.
  {
    symmetry in Hvalidbounds.
    inversion Hvalidbounds; subst; clear Hvalidbounds.
    apply FloverMap.mem_2 in Hmem.
    specialize (Hcheckedall _ Hmem).
    specialize (Hcheckedex _ Hmem) as (Hvars & ? & Hcheckedex).
    repeat split.
    1-4: congruence.
    intros v__FP m__FP Heval__FP.
    unfold checked_error_expressions in Hcheckedall.
    specialize (Hcheckedall v__R v__FP m__FP iv__A err__A) as (af & err__af & Hcheckedall); auto.
    exists af, err__af, noise_map1.
    intuition.
  }
  destruct Htypecheck as (m__e & Hetype & (Htypecheck__e & (Hm & ?)) & Hvalidexec).
  subst.
  rewrite Hetype in Hvalidbounds; cbn in Hvalidbounds.
  rewrite Hcert in Hvalidbounds; cbn in Hvalidbounds.
  destruct (negb (Qleb 0 err__A)) eqn: H0err; [congruence|].
  destruct (validErrorboundAA e Gamma A dVars noise1 expr_map1)
    as [(subexpr_map, subnoise)|] eqn: Hvalidsubexpr;
    cbn in Hvalidbounds; try congruence.
  destruct (FloverMap.find e subexpr_map) as [subaf|] eqn: Hsubaf;
    cbn in Hvalidbounds; [|congruence].
  destruct Hrange as (Hsubrange & tmpiv & tmperr & tmpvR & Hres__A' & Heval1' & Hcontained).
  rewrite Hcert in Hres__A'.
  replace tmpiv with iv__A in * by congruence.
  replace tmperr with err__A in * by congruence; clear Hres__A' tmperr tmpiv.
  pose proof Heval__R as Heval__R'.
  eapply meps_0_deterministic in Heval__R'; try exact Heval1'.
  replace tmpvR with v__R in * by congruence; clear Heval1' Heval__R' tmpvR.
  pose proof (validRanges_single _ _ _ _ Hsubrange)
    as (subiv & suberr & subv__R & Hsubres__A & Hsubeval & Hsubcontained).
  rewrite Hsubres__A in Hvalidbounds; cbn in Hvalidbounds.
  destruct (Qleb (maxAbs (toIntv (AffineArithQ.plus_aff subaf
                                                        (mkErrorPolyQ (computeErrorQ
                                                                         (maxAbs (widenIntv subiv
                                                                                            suberr))
                                                                         m__e)
                                                                      subnoise)))) err__A) eqn: Herrle;
    [|congruence].
  inversion Hvalidbounds; subst; clear Hvalidbounds.
  split.
  + inversion Heval__R; subst.
    destruct m1; cbn in H4; try congruence; clear H4.
    specialize (IHe expr_map1 subexpr_map noise_map1 noise1 subnoise v1 subiv suberr).
    edestruct IHe as (((nF & m & IHevex) & IHchecked) & IHevall); eauto.
    assert (exists (v__FP : R) (m__FP : mType),
               eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp (Downcast m__e e)) v__FP m__FP).
    {
      specialize (Hdeltamap nF m__e)
        as (delta' & Hdelta & Hdelta').
      exists (perturb nF m__e delta'), m__e.
      eapply Downcast_dist' with (delta := delta'); eauto.
      { destruct H as [? [? ?]].
        assert (x = m).
        { eapply validTypes_exec; eauto. }
        subst; auto. }
      { eapply toRExpMap_some with (e:=Downcast m__e e); eauto. }
    }
    split; auto.
    intros e' Hnin Hin.
    destruct (flover_map_in_dec e' subexpr_map) as [Hin1|Hnin1]; [apply IHchecked; auto|].
    destruct (flover_map_el_eq_extension Hnin1 Hin) as [Heq Hexpeq]; auto.
    split; [|split; [|now rewrite Hexpeq]].
    1: rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
      try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
    1: now apply subset_diff_to_subset_union.
    erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
  + intros * Heval__FPdet.
    inversion Heval__R; subst.
    destruct m1; cbn in H4; try congruence; clear H4.
    inversion Heval__FPdet; subst.
    specialize (IHe expr_map1 subexpr_map noise_map1 noise1 subnoise
                    v1 subiv suberr).
    edestruct IHe as (_ & IHevall); eauto.
    specialize (IHevall v0 m1)
      as (ihaf & iherr__af & ihnoise_map & IHcontf & IHnoise & IHfresh & IHcontn &
          IHnoise_map & IHsub__A & IHerrpos & IHiv__err & IHerr & IHevals & IHchecked);
      eauto.
    replace subaf with ihaf in * by congruence; clear subaf.
    rewrite Qle_bool_iff in Herrle.
    apply Qle_Rle in Herrle.
    rename v0 into nF.
    replace subv__R with v1 in * by (eapply meps_0_deterministic; eauto).
    clear subv__R.
    pose proof (@plus_error_aff_af_evals (afQ2R ihaf) v1 nF (widenIntv subiv suberr) m__FP delta0
                                         subnoise ihnoise_map) as (noise_map2 & ? & ? & ? & Hevals);
      eauto.
    1: reflexivity.
    1: destruct subiv; cbn in *; try rewrite Q2R_minus, Q2R_plus; eapply contained'; eauto.
    exists (AffineArithQ.plus_aff ihaf
                             (mkErrorPolyQ (computeErrorQ (maxAbs (widenIntv subiv
                                                                             suberr)) m__FP)
                                           subnoise)),
    (RmaxAbsFun (toInterval (plus_aff (afQ2R ihaf)
                                      (mkErrorPolyR (computeErrorR (Q2R (maxAbs (widenIntv subiv
                                                                                           suberr))) m__FP)
                                                    subnoise)))),
    noise_map2.
    rewrite <- maxAbs_impl_RmaxAbs_iv in Herrle.
    rewrite to_interval_to_intv_iv in Herrle.
    rewrite afQ2R_plus_aff in Herrle |-*.
    rewrite afQ2R_mkErrorPolyQ in Herrle |-*.
    rewrite computeErrorQ_computeErrorR in Herrle |-*.
    repeat split; auto.
    * rewrite mem_false_find_none in Hmem.
      pose proof contained_flover_map_extension as H'.
      specialize (H' _ expr_map1 _ (AffineArithQ.plus_aff ihaf
                                                          (mkErrorPolyQ (computeErrorQ
                                                                           (maxAbs (widenIntv subiv
                                                                                              suberr))
                                                                           m__FP) subnoise)) Hmem).
      etransitivity; try eassumption.
      apply contained_flover_map_add_compat.
      assumption.
    * lia.
    * eauto using contained_map_trans.
    * rewrite FloverMapFacts.P.F.add_eq_o; try auto.
      apply Q_orderedExps.exprCompare_refl.
    * unfold RmaxAbsFun.
      apply Rmax_case; apply Rabs_pos.
    * symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
      eauto 9
            using plus_aff_to_interval_sym_compat,
      toInterval_mkErrorPolyR, computeErrorR_pos, RmaxAbsFun_iv, radius_nonneg.
    * intros e' Hnin Hin.
      {
        destruct (FloverMapFacts.O.MO.eq_dec (Downcast m__FP e) e') as [Heqexp|Heqexp].
        - unfold checked_error_expressions.
          pose proof (expr_compare_eq_eval_compat _ _ Heqexp) as Hreq.
          rewrite <- Hreq.
          intros.
          exists (AffineArithQ.plus_aff ihaf
                                   (mkErrorPolyQ (computeErrorQ (maxAbs (widenIntv subiv
                                                                                   suberr)) m__FP)
                                                 subnoise)),
          (RmaxAbsFun (toInterval (plus_aff (afQ2R ihaf)
                                            (mkErrorPolyR (computeErrorR
                                                             (Q2R (maxAbs (widenIntv subiv
                                                                                     suberr))) m__FP)
                                                          subnoise)))).
          rewrite afQ2R_plus_aff.
          rewrite afQ2R_mkErrorPolyQ.
          rewrite computeErrorQ_computeErrorR.
          repeat split; try auto.
          + rewrite FloverMapFacts.P.F.add_eq_o; try auto.
          + unfold RmaxAbsFun.
            apply Rmax_case; apply Rabs_pos.
          + symmetry; erewrite RmaxAbsFun_iv; auto; try apply radius_nonneg.
            eauto 3
                  using plus_aff_to_interval_sym_compat,
            toInterval_mkErrorPolyR, computeErrorR_pos, RmaxAbsFun_iv, radius_nonneg.
          + erewrite FloverMapFacts.P.F.find_o in Hcert; eauto.
            now match goal with
                | [H1: FloverMap.find e' A = Some (iv__A0, err__A0),
                       H2: FloverMap.find e' A = Some (iv__A, err__A) |- _] => rewrite H1 in H2; inversion H2
                end.
          + erewrite meps_0_deterministic
              with (v1 := v__R) (v2 := perturb v1 REAL delta); eauto.
            erewrite eval_expr_functional
              with (v1 := v__FP) (v2 := perturb nF m__FP delta0); eauto.
            erewrite Gamma_det; eauto.
        - destruct (FloverMapFacts.P.F.In_dec subexpr_map e') as [Hsubin|Hsubnin].
          + apply checked_error_expressions_flover_map_add_compat; auto;
              eapply checked_error_expressions_extension; try apply IHchecked; eauto;
                [lia|reflexivity].
          + pose proof (flover_map_el_eq_extension Hsubnin Hin) as [Hexeq Hreq].
            congruence.
      }
Qed.

Theorem validErrorboundAA_sound (e: expr Q) E1 E2 A Gamma DeltaMap fVars dVars:
  validErrorboundAA_sound_statement e E1 E2 A Gamma DeltaMap fVars dVars.
Proof.
  induction e.
  - apply validErrorboundAA_sound_var; auto.
  - apply validErrorboundAA_sound_const; auto.
  - apply validErrorboundAA_sound_unop; auto.
  - apply validErrorboundAA_sound_binop; auto.
  - apply validErrorboundAA_sound_fma; auto.
  - apply validErrorboundAA_sound_downcast; auto.
  - admit.
Abort.

Corollary validErrorbound_sound_validErrorBounds e E1 E2 A Gamma DeltaMap expr_map noise noise_map:
  (forall e' : FloverMap.key,
      FloverMap.In e' expr_map ->
      (exists (v__FP' : R) (m__FP' : mType),
          eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e') v__FP' m__FP') /\
      checked_error_expressions e' E1 E2 A Gamma DeltaMap noise_map noise expr_map) ->
  contained_subexpr e expr_map ->
  validErrorBoundsRec e E1 E2 A Gamma DeltaMap.
Proof.
  induction e; intros Hchecked Hsubexpr.
  - split; [trivial|].
    intros * Heval__R Hcert.
    specialize Hsubexpr as (_ & Hsubexpr).
    specialize Hchecked as (Hex & Hall); eauto.
    intuition.
    specialize Hall as (? & ? & ?); eauto.
    intuition.
    eapply Rle_trans; eauto.
    match goal with
    | H: af_evals _ _ _ |- _ => apply to_interval_containment in H; rename H into Hiv
    end.
    match goal with
    | H: toInterval _ = _ |- _ => rewrite H in Hiv
    end.
    cbn in Hiv.
    now rewrite Rabs_Rle_condition.
  - split; [trivial|].
    intros * Heval__R Hcert.
    specialize Hsubexpr as (_ & Hsubexpr).
    specialize Hchecked as (Hex & Hall); eauto.
    intuition.
    specialize Hall as (? & ? & ?); eauto.
    intuition.
    eapply Rle_trans; eauto.
    match goal with
    | H: af_evals _ _ _ |- _ => apply to_interval_containment in H; rename H into Hiv
    end.
    match goal with
    | H: toInterval _ = _ |- _ => rewrite H in Hiv
    end.
    cbn in Hiv.
    now rewrite Rabs_Rle_condition.
  - cbn.
    specialize (IHe Hchecked).
    specialize Hsubexpr as (Hsubexpr & Hin).
    unfold validErrorBounds in IHe.
    split.
    { admit. (* FIXME! Invariant from checker *) }
    intros * Heval__R Hcert.
    specialize Hchecked as (Hex & Hall); eauto.
    intuition.
    specialize Hall as (? & ? & ?); eauto.
    intuition.
    eapply Rle_trans; eauto.
    match goal with
    | H: af_evals _ _ _ |- _ => apply to_interval_containment in H; rename H into Hiv
    end.
    match goal with
    | H: toInterval _ = _ |- _ => rewrite H in Hiv
    end.
    cbn in Hiv.
    now rewrite Rabs_Rle_condition.
  - cbn.
    specialize (IHe1 Hchecked).
    specialize (IHe2 Hchecked).
    specialize Hsubexpr as ((Hsubexpr1 & Hsubexpr2) & Hin).
    unfold validErrorBounds in IHe1, IHe2.
    split; [repeat split; try auto | ].
    { admit. }
    intros * Heval__R Hcert.
    specialize Hchecked as (Hex & Hall); eauto.
    intuition.
    specialize Hall as (? & ? & ?); eauto.
    intuition.
    eapply Rle_trans; eauto.
    match goal with
    | H: af_evals _ _ _ |- _ => apply to_interval_containment in H; rename H into Hiv
    end.
    match goal with
    | H: toInterval _ = _ |- _ => rewrite H in Hiv
    end.
    cbn in Hiv.
    now rewrite Rabs_Rle_condition.
  - cbn.
    specialize (IHe1 Hchecked).
    specialize (IHe2 Hchecked).
    specialize (IHe3 Hchecked).
    specialize Hsubexpr as ((Hsubexpr1 & Hsubexpr2 & Hsubexpr3) & Hin).
    unfold validErrorBounds in IHe1, IHe2, IHe3.
    split; auto.
    intros * Heval__R Hcert.
    specialize Hchecked as (Hex & Hall); eauto.
    intuition.
    specialize Hall as (? & ? & ?); eauto.
    intuition.
    eapply Rle_trans; eauto.
    match goal with
    | H: af_evals _ _ _ |- _ => apply to_interval_containment in H; rename H into Hiv
    end.
    match goal with
    | H: toInterval _ = _ |- _ => rewrite H in Hiv
    end.
    cbn in Hiv.
    now rewrite Rabs_Rle_condition.
  - cbn.
    specialize (IHe Hchecked).
    specialize Hsubexpr as (Hsubexpr & Hin).
    unfold validErrorBounds in IHe.
    split; auto.
    intros * Heval__R Hcert.
    specialize Hchecked as (Hex & Hall); eauto.
    intuition.
    specialize Hall as (? & ? & ?); eauto.
    intuition.
    eapply Rle_trans; eauto.
    match goal with
    | H: af_evals _ _ _ |- _ => apply to_interval_containment in H; rename H into Hiv
    end.
    match goal with
    | H: toInterval _ = _ |- _ => rewrite H in Hiv
    end.
    cbn in Hiv.
    now rewrite Rabs_Rle_condition.
  - admit.
Abort.

(*
Definition checked_error_commands c E1 E2 A Gamma DeltaMap noise_map noise expr_map :=
  match c with
  | Let m x e k =>
    checked_error_expressions e E1 E2 A Gamma DeltaMap noise_map noise expr_map
  | Ret e => checked_error_expressions e E1 E2 A Gamma DeltaMap noise_map noise expr_map
  end /\
  (forall v__R v__FP m__FP iv__A err__A,
      bstep (toREvalCmd (toRCmd c)) E1 (toRTMap (toRExpMap Gamma)) DeltaMapR v__R REAL ->
      bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP ->
      FloverMap.find (getRetExp c) A = Some (iv__A, err__A) ->
      exists (af : affine_form Q) (err__af : R) (noise_map2 : noise_mapping),
        fresh noise (afQ2R af) /\
        (forall n0 : nat, (n0 >= noise)%nat -> noise_map n0 = None) /\
        FloverMap.find (getRetExp c) expr_map = Some af /\
        (0 <= err__af)%R /\
        toInterval (afQ2R af) = ((- err__af)%R, err__af) /\
        (err__af <= Q2R err__A)%R /\
        af_evals (afQ2R af) (v__R - v__FP) noise_map2).

Fixpoint contained_command_subexpr (c: cmd Q) (expr_map: FloverMap.t (affine_form Q)): Prop :=
  match c with
  | Let m x e c => contained_subexpr e expr_map /\ contained_command_subexpr c expr_map
  | Ret e => contained_subexpr e expr_map
  end.

Lemma contained_command_subexpr_map_extension c expr_map1 expr_map2:
  contained_flover_map expr_map1 expr_map2 ->
  contained_command_subexpr c expr_map1 ->
  contained_command_subexpr c expr_map2.
Proof.
  intros Hcontf Hconte.
  induction c; cbn in *; intuition; eapply contained_subexpr_map_extension; eauto.
Qed.

Lemma contained_command_subexpr_add_compat c e' a expr_map:
  contained_command_subexpr c expr_map ->
  contained_command_subexpr c (FloverMap.add e' a expr_map).
Proof.
  intros Hcont.
  now induction c; cbn in *; intuition; apply contained_subexpr_add_compat.
Qed.

Lemma contained_command_subexpr_get_retexp_in c expr_map:
  contained_command_subexpr c expr_map ->
  FloverMap.In (getRetExp c) expr_map.
Proof.
  intros; induction c; cbn in *; intuition.
  induction e; cbn in *; intuition.
Qed.

Lemma validErrorBoundAACmd_contained_command_subexpr c Gamma A fVars dVars outVars
      noise1 expr_map1 noise2 expr_map2:
  (forall e', FloverMap.In e' expr_map1 ->
         contained_subexpr e' expr_map1) ->
  (forall n, NatSet.In n dVars -> FloverMap.In (Var Q n) expr_map1) ->
  ssa c (NatSet.union fVars dVars) outVars ->
  NatSet.Subset (Commands.freeVars c -- dVars) fVars ->
  validErrorboundAACmd c Gamma A dVars noise1 expr_map1 = Some (expr_map2, noise2) ->
  contained_flover_map expr_map1 expr_map2 /\
  contained_command_subexpr c expr_map2.
Proof.
  revert dVars expr_map1 expr_map2 noise1 noise2.
  induction c; intros * Hsubexpr Hdvars Hssa Hsubset Hvalid; cbn in *.
  - destruct (validErrorboundAA e Gamma A dVars noise1 expr_map1) eqn: Hvalid__e;
      cbn in Hvalid; [|congruence].
    destruct p as (expr_map', noise').
    destruct (FloverMap.find e expr_map') eqn: Hein; cbn in Hvalid; [|congruence].
    destruct (FloverMap.find e A) eqn: Hecert; cbn in Hvalid; [|congruence].
    destruct p as (?, ?).
    destruct (FloverMap.find (Var Q n) A) eqn: Hvarcert; cbn in Hvalid; [|congruence].
    destruct p as (?, ?).
    destruct (Qeq_bool e0 e1) eqn: Heq; cbn in Hvalid; [|congruence].
    destruct (FloverMap.find (Var Q n) expr_map') eqn: Hvarin; cbn in Hvalid; [congruence|].
    pose proof (validErrorboundAA_contained_subexpr _ _ _ _ Hsubexpr Hdvars Hvalid__e) as Hcont.
    specialize Hcont as (Hcont__e & Hcontf' & Hconte').
    inversion Hssa; subst.
    assert (contained_flover_map (FloverMap.add (Var Q n) a expr_map') expr_map2 /\
            contained_command_subexpr c expr_map2) as (H1 & H2).
    {
      eapply IHc with (dVars := NatSet.add n dVars); eauto.
      - intros.
        destruct (q_expr_eq_dec (Var Q n) e').
        + eapply contained_subexpr_eq_compat; eauto.
          cbn.
          split; auto.
          apply flover_map_in_add.
        + rewrite FloverMapFacts.P.F.add_neq_in_iff in H; auto.
          destruct (flover_map_in_dec e' expr_map1).
          * eapply contained_subexpr_map_extension; eauto.
            etransitivity; try apply Hcontf'; eauto.
            now apply contained_flover_map_extension.
          * apply contained_subexpr_add_compat; auto.
      - intros n__e Hn__e.
        set_tac.
        destruct Hn__e.
        + subst.
          apply flover_map_in_add.
        + specialize H as (_ & ?).
          eapply flover_map_in_extension; eauto.
          etransitivity; try apply Hcontf'; eauto.
          now apply contained_flover_map_extension.
      - assert (NatSet.Equal (NatSet.add n (NatSet.union fVars dVars))
                             (NatSet.union fVars (NatSet.add n dVars))) as Hseteq.
        {
          hnf. intros ?; split; intros in_set; set_tac.
          - destruct in_set as [ ? | [? ?]]; try auto; set_tac.
            destruct H0; auto.
          - destruct in_set as [? | ?]; try auto; set_tac.
            destruct H as [? | [? ?]]; auto.
        }
        eapply ssa_equal_set; symmetry in Hseteq.
        exact Hseteq.
        assumption.
      - hnf. intros ? a_freeVar.
        rewrite NatSet.diff_spec in a_freeVar.
        destruct a_freeVar as [a_freeVar a_no_dVar].
        apply Hsubset.
        simpl.
        rewrite NatSet.diff_spec, NatSet.remove_spec, NatSet.union_spec.
        repeat split; try auto.
        { hnf; intros; subst.
          apply a_no_dVar.
          rewrite NatSet.add_spec; auto. }
        { hnf; intros a_dVar.
          apply a_no_dVar.
          rewrite NatSet.add_spec; auto. }
    }
    split; [|split]; auto.
    + etransitivity; eauto.
      etransitivity; eauto.
      apply contained_flover_map_extension; auto.
    + eapply contained_subexpr_map_extension; eauto.
      eapply contained_subexpr_map_extension; eauto.
      apply contained_flover_map_extension; auto.
  - pose proof (validErrorboundAA_contained_subexpr _ _ _ _ Hsubexpr Hdvars Hvalid) as Hcont.
    intuition.
Qed.

Lemma validErrorboundAA_some_cert e Gamma A dVars noise expr_map p:
  (forall e', FloverMap.In e' expr_map -> exists iv__A err__A, FloverMap.find e' A = Some (iv__A, err__A)) ->
  validErrorboundAA e Gamma A dVars noise expr_map = Some p ->
  exists iv__A err__A, FloverMap.find e A = Some (iv__A, err__A).
Proof.
  destruct e; cbn; intros Hchecked Hvalid; destruct FloverMap.mem eqn: Hmem;
    try (eapply Hchecked; rewrite <- FloverMapFacts.P.F.mem_in_iff in Hmem; eauto);
    move Hchecked at bottom; destruct FloverMap.find; cbn in Hvalid; try congruence;
      destruct FloverMap.find eqn: Hfind; cbn in Hvalid; try congruence; destruct p0; eauto.
Qed.

Theorem validErrorboundAACmd_sound c:
  forall E1 E2 A Gamma DeltaMap fVars dVars outVars
    (expr_map1 expr_map2 : FloverMap.t (affine_form Q))
    (noise_map1 : nat -> option noise_type) (noise1 noise2 : nat) (v__R : R),
    (forall (v : R) (m' : mType),
        exists d : R, DeltaMap v m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    bstep (toREvalCmd (toRCmd c)) E1 (toRTMap (toRExpMap Gamma)) DeltaMapR v__R REAL ->
    validRangesCmd c A E1 (toRTMap (toRExpMap Gamma)) ->
    validErrorboundAACmd c Gamma A dVars noise1 expr_map1 = Some (expr_map2, noise2) ->
    ssa c (NatSet.union fVars dVars) outVars ->
    NatSet.Subset (Commands.freeVars c -- dVars) fVars ->
    validTypesCmd c Gamma ->
    (0 < noise1)%nat ->
    (forall n0 : nat, (n0 >= noise1)%nat -> noise_map1 n0 = None) ->
    dVars_contained dVars expr_map1 ->
    (forall e',
        FloverMap.In  e' expr_map1 -> contained_subexpr e' expr_map1) ->
    (forall e' : FloverMap.key,
        FloverMap.In (elt:=affine_form Q) e' expr_map1 ->
        NatSet.Subset (usedVars e') (NatSet.union fVars dVars) /\
        (exists iv__A' err__A', FloverMap.find e' A = Some (iv__A', err__A')) /\
        exists (v__FP' : R) (m__FP' : mType),
          eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e') v__FP' m__FP') ->
    (forall e' : FloverMap.key,
        FloverMap.In (elt:=affine_form Q) e' expr_map1 ->
        checked_error_expressions e' E1 E2 A Gamma DeltaMap noise_map1 noise1 expr_map1) ->
    ((exists (v__FP : R) (m__FP : mType),
         bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP) /\
     (forall e' : FloverMap.key,
         ~ FloverMap.In (elt:=affine_form Q) e' expr_map1 ->
         FloverMap.In (elt:=affine_form Q) e' expr_map2 ->
         (exists dVars, NatSet.Subset (usedVars e') (NatSet.union fVars dVars)) /\
         (exists iv__A' err__A', FloverMap.find e' A = Some (iv__A', err__A')) /\
         exists E2 (v__FP' : R) (m__FP' : mType),
           eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e') v__FP' m__FP')) /\
    (forall (v__FP : R) (m__FP : mType) (iv__A : intv) (err__A : error),
        bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP ->
        FloverMap.find (getRetExp c) A = Some (iv__A, err__A) ->
        exists (af : affine_form Q) (err__af : R) (noise_map2 : noise_mapping),
          contained_flover_map expr_map1 expr_map2 /\
          (noise1 <= noise2)%nat /\
          fresh noise2 (afQ2R af) /\
          contained_map noise_map1 noise_map2 /\
          (forall n0 : nat, (n0 >= noise2)%nat -> noise_map2 n0 = None) /\
          FloverMap.find (elt:=affine_form Q) (getRetExp c) expr_map2 = Some af /\
          (0 <= err__af)%R /\
          toInterval (afQ2R af) = ((- err__af)%R, err__af) /\
          (err__af <= Q2R err__A)%R /\
          af_evals (afQ2R af) (v__R - v__FP) noise_map2 /\
          validErrorBoundsCmdRec c E1 E2 A Gamma DeltaMap /\
          (forall e' : FloverMap.key,
              ~ FloverMap.In (elt:=affine_form Q) e' expr_map1 ->
              FloverMap.In (elt:=affine_form Q) e' expr_map2 ->
              exists E1 E2,
                checked_error_expressions e' E1 E2 A Gamma DeltaMap noise_map2 noise2 expr_map2)).
Proof.
  induction c;
    intros * Hdeltamap Henv Heval__R Hrange Hvalidbounds Hssa Hsubset Htypes Hnoise1
                       Hnoise_map1 Hdvars Hcontainedsubexpr Hcheckedex Hcheckedall;
    cbn in Hvalidbounds.
  - destruct (validErrorboundAA e Gamma A dVars noise1 expr_map1) eqn: Hvalidbounds';
      cbn in Hvalidbounds; [|congruence].
    destruct p as (subexpr_map, subnoise).
    destruct (FloverMap.find e subexpr_map) eqn: Hsubfind;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find e A) eqn: Hsubcert;
      cbn in Hvalidbounds; [|congruence].
    destruct p as (subiv, suberr).
    destruct (FloverMap.find (Var Q n) A) eqn: Hvarcert;
      cbn in Hvalidbounds; [|congruence].
    destruct p as (variv, varerr).
    destruct (Qeq_bool suberr varerr) eqn: Heqerr;
      cbn in Hvalidbounds; [|congruence].
    destruct (FloverMap.find (Var Q n) subexpr_map) eqn: Hvarnew;
      cbn in Hvalidbounds; [congruence|].
    inversion Hssa; subst.
    cbn in Hsubset.
    assert (NatSet.Subset (usedVars e -- dVars) fVars) as Hsubs.
    { set_tac. repeat split; auto.
      hnf; intros; subst.
      set_tac. }
    pose proof (validErrorboundAA_sound e) as Hvalid__e.
    inversion Heval__R; subst.
    destruct Htypes as ((? & ? & ? & ? & ? & ?) & ?).
    destruct Hrange as ((? & ?) & ?).
    specialize Hvalid__e as (((v__FP & m__FP & Heval__e) & Hcheckedex__e) & Hvalidall__e); eauto.
    assert (NatSet.Equal (NatSet.add n (NatSet.union fVars dVars))
                         (NatSet.union fVars (NatSet.add n dVars))) as Hseteq.
    {
      hnf. intros ?; split; intros in_set; set_tac.
      - destruct in_set as [ ? | [? ?]]; try auto; set_tac.
        destruct H14; auto.
      - destruct in_set as [? | ?]; try auto; set_tac.
        destruct H13 as [? | [? ?]]; auto.
    }
    assert (ssa c (fVars ∪ (NatSet.add n dVars)) outVars) as Hssa'.
    {
      eapply ssa_equal_set; symmetry in Hseteq.
      exact Hseteq.
      assumption.
    }
    assert (NatSet.Subset (freeVars c -- NatSet.add n dVars) fVars) as Hsubset'.
    {
      hnf. intros ? a_freeVar.
      rewrite NatSet.diff_spec in a_freeVar.
      destruct a_freeVar as [a_freeVar a_no_dVar].
      apply Hsubset.
      simpl.
      rewrite NatSet.diff_spec, NatSet.remove_spec, NatSet.union_spec.
      repeat split; try auto.
      { hnf; intros; subst.
        apply a_no_dVar.
        rewrite NatSet.add_spec; auto. }
      { hnf; intros a_dVar.
        apply a_no_dVar.
        rewrite NatSet.add_spec; auto. }
    }
    specialize (Hvalidall__e v__FP m__FP Heval__e) as (af__e & err__e & noise_map2 & ? & ? & ? & ? & ? & ? &
                                               ? & Hiv & ? & Hevals & Hcheckedall__e).
    pose proof Heqerr as Heqerr_bool.
    rewrite Qeq_bool_iff in Heqerr.
    apply Qeq_eqR in Heqerr.
    assert (approxEnv (updEnv n v E1) (toRExpMap Gamma) A fVars
                      (NatSet.add n dVars) (updEnv n v__FP E2)).
    {
      eapply approxUpdBound; eauto.
      - eapply toRExpMap_some; eauto.
        simpl; auto.
      - apply Rle_trans with (r2:= err__e); try lra.
        apply to_interval_containment in Hevals.
        rewrite Hiv in Hevals.
        cbn in Hevals.
        now apply Rabs_le.
    }
    specialize (H9 v H11).
    assert (dVars_contained (NatSet.add n dVars) (FloverMap.add (Var Q n) a subexpr_map)).
    {
      unfold dVars_contained in Hdvars |-*.
      intros v' Hinv'.
      destruct (v' =? n) eqn:Heq.
      - rewrite Nat.eqb_eq in Heq; subst.
        rewrite FloverMapFacts.P.F.add_in_iff.
        left.
        apply Q_orderedExps.exprCompare_refl.
      - pose proof Heq as Heq'.
        rewrite Nat.eqb_neq in Heq.
        apply NatSetProps.FM.add_3 in Hinv'; auto.
        move Hdvars at bottom.
        specialize (Hdvars v' Hinv').
        rewrite FloverMapFacts.P.F.add_neq_in_iff.
        + eapply flover_map_in_extension; eauto.
        + cbn; intros Heq''.
          apply nat_compare_eq in Heq''.
          auto.
    }
    rewrite <- FloverMapFacts.P.F.not_find_in_iff in Hvarnew.
    specialize IHc with (dVars := NatSet.add n dVars) as ((IHex & IHchecked) & IHall);
      eauto.
    1: lia.
    {
      intros e' Hin'.
      edestruct validErrorboundAA_contained_subexpr as (? & ? & ?); eauto.
      destruct (q_expr_eq_dec (Var Q n) e').
      - eapply contained_subexpr_eq_compat; eauto.
        cbn.
        split; auto.
        apply flover_map_in_add.
      - rewrite FloverMapFacts.P.F.add_neq_in_iff in Hin'; eauto.
        destruct (flover_map_in_dec e' expr_map1) as [Hin|Hnin];
          apply contained_subexpr_add_compat; eauto using contained_subexpr_map_extension.
    }
    {
      intros e' Hin.
      destruct (q_expr_eq_dec (Var Q n) e') as [Heqe'|Hneqe'].
      - rewrite FloverMapFacts.P.F.In_iff in Hvarnew; eauto.
        specialize (flover_map_el_eq_extension Hvarnew Hin) as [Heq Heqexp].
        rewrite Heqexp.
        split.
        + rewrite freeVars_eq_compat; unfold Q_orderedExps.eq;
            try eapply Q_orderedExps.exprCompare_eq_sym; eauto.
          cbn; set_tac.
        + split.
          * erewrite FloverMapFacts.P.F.find_o in Hvarcert; eauto.
          * exists v__FP, m.
            constructor; auto.
            1: eapply toRExpMap_some with (e := Var Q n); eauto.
            unfold updEnv.
            now rewrite <- beq_nat_refl.
      - rewrite FloverMapFacts.P.F.add_neq_in_iff in Hin; auto.
        destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
        + move Hcheckedex at bottom.
          specialize (Hcheckedex _ Hin1).
          destruct Hcheckedex as (Hsubsete' & Hfind' & vfp & mfp & Hevalfp).
          split.
          * rewrite NatSetProps.union_sym.
            rewrite NatSetProps.union_add.
            apply NatSetProps.subset_add_2.
            now rewrite NatSetProps.union_sym.
          * split; eauto.
            exists vfp, mfp.
            eapply eval_expr_ssa_extension; eauto; [now rewrite usedVars_toRExp_compat|].
            specialize ssa_inv_let as (? & ?); eauto.
        + specialize (Hcheckedex__e _ Hnin1 Hin).
          destruct Hcheckedex__e as (Hsubsete' & Hcert' & vfp & mfp & Hevalfp).
          split.
          * rewrite NatSetProps.union_sym.
            rewrite NatSetProps.union_add.
            apply NatSetProps.subset_add_2.
            now rewrite NatSetProps.union_sym.
          * split; eauto.
            exists vfp, mfp.
            eapply eval_expr_ssa_extension; eauto; [now rewrite usedVars_toRExp_compat|].
            specialize ssa_inv_let as (? & ?); eauto.
    }
    {
      intros e' Hin.
      destruct (q_expr_eq_dec (Var Q n) e') as [Heqe'|Hneqe'].
      - rewrite FloverMapFacts.P.F.In_iff in Hvarnew; eauto.
        specialize (flover_map_el_eq_extension Hvarnew Hin) as [Heq Heqexp].
        unfold checked_error_expressions.
        rewrite Heqexp.
        intros v__R' v__FP' m__FP' iv__A' err__A' Heval__R' Heval__FP' Hcert'.
        exists af__e, err__e.
        repeat split; auto.
        + replace af__e with a by congruence.
          eapply FloverMapFacts.P.F.add_eq_o; auto.
        + erewrite FloverMapFacts.P.F.find_o in Hvarcert; eauto.
          replace err__A' with varerr by congruence.
          now rewrite <- Heqerr.
        + inversion Heval__R'; subst.
          inversion Heval__FP'; subst.
          unfold updEnv in H25, H27.
          rewrite <- beq_nat_refl in H25.
          rewrite <- beq_nat_refl in H27.
          inversion H25; subst.
          inversion H27; subst.
          assumption.
      - rewrite FloverMapFacts.P.F.add_neq_in_iff in Hin; auto.
        destruct (flover_map_in_dec e' expr_map1) as [Hin1|Hnin1].
        + move Hcheckedex at bottom.
          unfold checked_error_expressions.
          intros v__R' v__FP' m__FP' iv__A' err__A' Heval__R' Heval__FP' Hcert'.
          move Hcheckedall at bottom.
          move Hcheckedex at bottom.
          specialize (Hcheckedex _ Hin1) as (Hsubset__e' & _).
          specialize (Hcheckedall _ Hin1).
          assert (contained_flover_map expr_map1 (FloverMap.add (Var Q n) a subexpr_map)).
          {
            etransitivity; eauto.
            apply contained_flover_map_extension.
            now apply FloverMapFacts.P.F.not_find_in_iff.
          }
          apply checked_error_expressions_extension with
              (noise_map2 := noise_map2) (noise2 := subnoise)
              (expr_map2 := FloverMap.add (Var Q n) a subexpr_map) in Hcheckedall; auto.
          specialize (Hcheckedall v__R' v__FP' m__FP' iv__A' err__A').
          apply Hcheckedall.
          * eapply eval_expr_ssa_extension2; eauto;
              [now rewrite usedVars_toREval_toRExp_compat|].
            specialize ssa_inv_let as (? & ?); eauto.
          * eapply eval_expr_ssa_extension2; eauto;
              [now rewrite usedVars_toRExp_compat|].
            specialize ssa_inv_let as (? & ?); eauto.
          * congruence.
        + unfold checked_error_expressions.
          intros v__R' v__FP' m__FP' iv__A' err__A' Heval__R' Heval__FP' Hcert'.
          move Hcheckedall__e at bottom.
          move Hcheckedex__e at bottom.
          specialize (Hcheckedex__e _ Hnin1 Hin).
          destruct Hcheckedex__e as (Hsubset__e' & _).
          specialize (Hcheckedall__e _ Hnin1 Hin).
          assert (contained_flover_map subexpr_map (FloverMap.add (Var Q n) a subexpr_map)).
          {
            apply contained_flover_map_extension.
            now apply FloverMapFacts.P.F.not_find_in_iff.
          }
          apply checked_error_expressions_extension with
              (noise_map2 := noise_map2) (noise2 := subnoise)
              (expr_map2 := FloverMap.add (Var Q n) a subexpr_map) in Hcheckedall__e; auto; trivial.
          unfold checked_error_expressions in Hcheckedall__e.
          eapply Hcheckedall__e.
          * eapply eval_expr_ssa_extension2; eauto;
              [now rewrite usedVars_toREval_toRExp_compat|].
            specialize ssa_inv_let as (? & ?); eauto.
          * eapply eval_expr_ssa_extension2; eauto;
              [now rewrite usedVars_toRExp_compat|].
            specialize ssa_inv_let as (? & ?); eauto.
          * instantiate (1 := iv__A'). congruence.
          * reflexivity.
    }
    split.
    + split.
      * clear IHchecked.
        destruct IHex as (v__FP' & m__FP' & IHex).
        exists v__FP', m__FP'.
        assert (FloverMap.find e Gamma = Some m).
        {
          clear - H H0 H1.
          rewrite H.
          f_equal.
          symmetry.
          now rewrite <- mTypeEq_compat_eq.
        }
        econstructor; eauto.
        replace m with m__FP; auto.
        symmetry.
        eapply validTypes_exec; eauto.
      * intros e' Hnin Hin.
        destruct (flover_map_in_dec e' subexpr_map) as [Hsubin|Hsubnin];
          [specialize (Hcheckedex__e _ Hnin Hsubin); intuition; eauto|].
        destruct (flover_map_in_dec e' (FloverMap.add (Var Q n) a subexpr_map)) as [IHin|IHnin];
          [|specialize (IHchecked e' IHnin Hin); apply IHchecked].
        apply flover_map_el_eq_extension in IHin; auto.
        specialize IHin as [Heq Hexpeq].
        rewrite <- usedVars_toRExp_compat.
        rewrite Hexpeq.
        rewrite usedVars_toRExp_compat.
        apply not_in_not_mem in H6.
        split; [exists (NatSet.add n dVars); auto; set_tac; cbn; set_tac|].
        split; [erewrite FloverMapFacts.P.F.find_o in Hvarcert; eauto|].
        exists (updEnv n v__FP E2), v__FP, m.
        econstructor; eauto.
        1: eapply toRExpMap_some with (e := (Var Q n)); eauto.
        unfold updEnv.
        now rewrite <- beq_nat_refl.
    + intros v__FP' m__FP' iv__A err__A Heval__FP' Hcert'.
      cbn in Hcert'.
      inversion Heval__FP'; subst.
      replace m with m__FP in * by (eapply Gamma_det; eauto); clear m.
      replace v0 with v__FP in * by (eapply eval_expr_functional; eauto); clear v0.
      specialize (IHall v__FP' m__FP' iv__A err__A H33 Hcert') as (af' & err__af' & noise_map' & ? & ? & ? & ? &
                                           ? & ? & ? & ? & ? & ? & ? & IHcheckedall).
      exists af', err__af', noise_map'.
      repeat split; auto.
      * etransitivity; eauto.
        etransitivity; eauto.
        apply contained_flover_map_extension; eauto.
        now apply FloverMapFacts.P.F.not_find_in_iff.
      * etransitivity; eauto.
      * etransitivity; eauto.
      * eapply validErrorbound_sound_validErrorBounds with (expr_map := subexpr_map); eauto.
        {
          intros e' Hine'.
          destruct (flover_map_in_dec e' expr_map1) as [Hin|Hnin].
          - specialize (Hcheckedex e' Hin) as (? & ? & ?).
            split; auto.
            eapply checked_error_expressions_extension; try apply Hcheckedall; eauto.
          - specialize (Hcheckedex__e e' Hnin Hine') as (? & ? & ?).
            split; auto.
        }
        edestruct validErrorboundAA_contained_subexpr as (? & ? & ?);
          try exact Hvalidbounds'; eauto.
      * exists subiv, suberr, variv, varerr.
        repeat split; auto.
      * intros v__R0 v__FP0 Heval__R0 Heval__FP0.
        apply eval_expr_functional with (v1 := v) in Heval__R0; eauto.
        apply eval_expr_functional with (v1 := v__FP) in Heval__FP0; eauto.
        subst; auto.
      * eexists; eexists.
        econstructor; eauto.
      * intros v__FP0 m__FP0 Hbstep0.
        replace m__FP0 with m__FP' in * by eauto using bstep_Gamma_det.
        assert (v__FP0 = v__FP') by eauto using bstep_det.
        assert (v__R0 = v__R) by eauto using bstep_det.
        cbn in H37.
        assert (err = err__A) by congruence.
        subst.
        eapply Rle_trans; eauto.
        apply to_interval_containment in H34.
        rewrite H30 in H34.
        cbn in H34.
        now rewrite Rabs_Rle_condition.
      * intros e' Hnin Hin.
        {
          destruct (flover_map_in_dec e' subexpr_map) as [Hsubin|Hsubnin].
          - move Hcheckedall__e at bottom.
            specialize (Hcheckedall__e _ Hnin Hsubin).
            exists E1, E2.
            eapply checked_error_expressions_extension with
                (noise1 := subnoise) (noise_map1 := noise_map2) (expr_map1 := subexpr_map); eauto.
            etransitivity; eauto.
            apply contained_flover_map_extension; eauto.
            now apply FloverMapFacts.P.F.not_find_in_iff.
          - destruct (flover_map_in_dec e' (FloverMap.add (Var Q n) a subexpr_map)) as [IHin|IHnin];
              [|apply IHcheckedall; auto].
            eapply flover_map_el_eq_extension in Hsubnin; eauto.
            specialize Hsubnin as [Heq Hexpeq].
            exists (updEnv n v E1), (updEnv n v__FP E2).
            unfold checked_error_expressions.
            rewrite Hexpeq.
            intros v__R'' v__FP'' m__FP'' iv__A'' err__A'' Heval__R'' Heval__FP'' Hcert''.
            replace v__R'' with v in *
              by (inversion Heval__R''; subst; unfold updEnv in H38;
                  rewrite <- beq_nat_refl in H38; congruence); clear v__R''.
            replace m__FP'' with m__FP in *
              by (inversion Heval__FP''; subst; assert (toRExpMap Gamma (Var R n) = Some m__FP)
                    by (eapply toRExpMap_some with (e := Var Q n); eauto);
                  congruence); clear m__FP''.
            replace v__FP'' with v__FP in *
              by (inversion Heval__FP''; subst; unfold updEnv in H38;
                  rewrite <- beq_nat_refl in H38; congruence); clear v__FP''.
            exists af__e, err__e.
            repeat split; auto.
            + apply fresh_monotonic with (n := subnoise); eauto.
            + apply H23.
              replace af__e with a by congruence.
              apply FloverMapFacts.P.F.add_eq_o; auto.
            + erewrite FloverMapFacts.P.F.find_o in Hvarcert; eauto.
              replace err__A'' with varerr in * by congruence.
              now rewrite <- Heqerr.
            + eapply af_evals_map_extension; eauto.
        }
  - split.
    + inversion Heval__R; subst.
      edestruct validErrorboundAA_some_cert as (? & ? & ?); eauto.
      1: intros; edestruct Hcheckedex as (? & ? & ?); eauto.
      edestruct (validErrorboundAA_sound e) as (((v__FP & m__FP & Hex) & Hcheckedex') & _); eauto;
        [now destruct Hrange|now destruct Htypes|].
      assert (exists (v__FP : R) (m__FP : mType),
                 bstep (toRCmd (Ret e)) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP).
      {
        exists v__FP, m__FP.
        constructor; auto.
      }
      split; auto.
      intros e' Hnin Hin.
      specialize (Hcheckedex' _ Hnin Hin).
      intuition; eauto.
    + intros v__FP m__FP iv__A err__A Heval__FP Hcert.
      cbn in Hcert.
      inversion Heval__R; subst.
      inversion Heval__FP; subst.
      edestruct (validErrorboundAA_sound e) as (Hex & Hall); eauto;
        [now destruct Hrange|now destruct Htypes|].
      specialize (Hall v__FP m__FP H1) as (af & err__af & noise_map2 & Hall).
      exists af, err__af, noise_map2.
      intuition; eauto.
      cbn.
      split.
      * edestruct validErrorboundAA_contained_subexpr as (? & ? & ?); eauto.
        eapply validErrorbound_sound_validErrorBounds; eauto.
        intros e' Hine'.
        {
          destruct (flover_map_in_dec e' expr_map1) as [Hin|Hnin].
          - edestruct Hcheckedex as (? & ? & ?); eauto.
            split; eauto.
            eapply checked_error_expressions_extension; try apply Hcheckedall; eauto.
          - edestruct H2 as (? & ? & ?); eauto.
        }
      * intros v__R0 iv err Heval__R' Hcert'.
        split; [eexists; eexists; eauto|].
        intros v__FP0 m__FP0 Hbstep0.
        replace m__FP0 with m__FP in * by eauto using bstep_Gamma_det.
        assert (v__FP0 = v__FP) by eauto using bstep_det.
        assert (v__R0 = v__R) by eauto using bstep_det.
        cbn in Hcert'.
        assert (err = err__A) by congruence.
        subst.
        eapply Rle_trans; eauto.
        apply to_interval_containment in H12.
        rewrite H10 in H12.
        cbn in H12.
        now rewrite Rabs_Rle_condition.
Qed.
*)

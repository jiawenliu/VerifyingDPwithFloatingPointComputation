From Coq
     Require Import Reals.Reals QArith.Qreals.

From Flover
     Require Export Infra.ExpressionAbbrevs ErrorAnalysis ErrorValidationProofs
     ErrorValidation
     ExpressionSemantics RealRangeValidator
     TypeValidator Environments.

Definition RoundoffErrorValidator (e:expr Q) (tMap:FloverMap.t mType)
           (A:analysisResult) (dVars:NatSet.t) :=
  validErrorbound e tMap A dVars.
  (* TODO
  if
  validErrorbound e tMap A dVars
  then true
  else match validErrorboundAA e tMap A dVars 1 (FloverMap.empty (affine_form Q)) with
       | Some _ => true
       | None => false
       end.
*)

Theorem RoundoffErrorValidator_sound:
  forall (e : expr Q) (E1 E2 : env) (fVars dVars : NatSet.t) (A : analysisResult)
    (nR : R) (err : error) (iv : intv) (Gamma : FloverMap.t mType)
    outVars,
    ssa e (NatSet.union fVars dVars) outVars ->
    validTypes e Gamma ->
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    NatSet.Subset (freeVars e -- dVars) fVars ->
    eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) nR REAL ->
    RoundoffErrorValidator e Gamma A dVars = true ->
    validRanges e A E1 (toRTMap (toRExpMap Gamma)) ->
    FloverMap.find e A = Some (iv, err) ->
    (* dVars_contained dVars (FloverMap.empty (affine_form Q)) -> *)
    validErrorBounds e E1 E2 A Gamma.
Proof.
  unfold RoundoffErrorValidator.
  intros; cbn in *.
  intros DeltaMap deltas_matched.
  destruct (validErrorbound e Gamma A dVars) eqn: Hivvalid.
  - eapply validErrorbound_sound; eauto.
  - congruence.
    (*
  - destruct (validErrorboundAA e Gamma A dVars 1 (FloverMap.empty (affine_form Q))) eqn: Hafvalid;
      [|congruence].
    destruct p as (expr_map, noise).
    pose proof validErrorboundAA_contained_subexpr as Hsubexpr.
    specialize (Hsubexpr e Gamma A dVars 1%nat noise (FloverMap.empty (affine_form Q)) expr_map).
    specialize Hsubexpr as (Hsubexpr & Hcont & Hcheckedsubexpr); eauto;
      [intros ? Hin; now rewrite FloverMapFacts.P.F.empty_in_iff in Hin|].
    pose proof validErrorboundAA_sound as Hvalidbound.
    specialize (Hvalidbound e E1 E2 A Gamma DeltaMap fVars dVars).
    specialize Hvalidbound as (Hex & Hall); eauto.
    + instantiate (1 := fun x => None); auto.
    + intros ? Hin.
      now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
    + intros ? Hin.
      now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
    + specialize Hex as ((v__e & m__e & Hev) & Hexchecked).
      specialize (Hall v__e m__e Hev) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hall).
      eapply validErrorbound_sound_validErrorBounds; eauto.
      intros e' Hin.
      specialize Hexchecked as (_ & _ & Hex); eauto;
        [now rewrite FloverMapFacts.P.F.empty_in_iff|].
      split; eauto.
      eapply Hall; eauto; now rewrite FloverMapFacts.P.F.empty_in_iff.
*)
Qed.

(*
Definition RoundoffErrorValidatorCmd (f:cmd Q) (tMap:FloverMap.t mType)
           (A:analysisResult) (dVars:NatSet.t) :=
  if
  validErrorboundCmd f tMap A dVars
  then true
  else match validErrorboundAACmd f tMap A dVars 1 (FloverMap.empty (affine_form Q)) with
       | Some _ => true
       | None => false
       end.

Theorem RoundoffErrorValidatorCmd_sound f:
  forall A E1 E2 outVars fVars dVars Gamma v__R,
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ->
    ssa f (NatSet.union fVars dVars) outVars ->
    NatSet.Subset (NatSet.diff (Commands.freeVars f) dVars) fVars ->
    bstep (toREvalCmd (toRCmd f)) E1 (toRTMap (toRExpMap Gamma)) DeltaMapR v__R REAL ->
    dVars_contained dVars (FloverMap.empty (affine_form Q)) ->
    RoundoffErrorValidatorCmd f Gamma A dVars = true ->
    validRangesCmd f A E1 (toRTMap (toRExpMap Gamma)) ->
    validTypesCmd f Gamma ->
    validErrorBoundsCmd f E1 E2 A Gamma.
Proof.
  intros; intros DeltaMap deltas_matched.
  unfold RoundoffErrorValidatorCmd in *.
  destruct (validErrorboundCmd f Gamma A dVars) eqn: Hivvalid.
  - eapply validErrorboundCmd_sound; eauto.
  - destruct (validErrorboundAACmd f Gamma A dVars 1 (FloverMap.empty (affine_form Q)))
             eqn: Hvalid; [|congruence].
    destruct p as (expr_map2, noise2).
    edestruct validErrorboundAACmd_sound; eauto.
    + instantiate (1 := fun x => None).
      auto.
    + intros ? Hin; now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
    + intros ? Hin; now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
    + intros ? Hin; now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
    + destruct H7 as ((v__FP & m__FP & Heval) & ?).
      edestruct validErrorBoundAACmd_contained_command_subexpr; eauto.
      1: intros ? Hin; now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
      apply contained_command_subexpr_get_retexp_in in H10.
      edestruct H7 as (? & (iv__A & err__A & Hcert) & ?); eauto.
      1: intros Hin; now rewrite FloverMapFacts.P.F.empty_in_iff in Hin.
      specialize (H8 v__FP m__FP iv__A err__A Heval Hcert).
      edestruct H8 as (? & ? & ? & ?); eauto.
      intuition.
Qed.
*)

(**
   This file contains the coq implementation of the certificate checker as well as its soundness proof.
   The checker is a composition of the range analysis validator and the error bound validator.
   Running this function on the encoded analysis result gives the desired theorem
   as shown in the soundness theorem.
**)
From Flover
     Require Import Infra.RealRationalProps Environments TypeValidator
     ResultChecker SubdivsChecker.

Require Export List ExpressionSemantics Coq.QArith.QArith Flover.SMTArith
        RealRangeArith ErrorAnalysis FPRangeValidator ssaPrgs.
Export ListNotations.

(** Certificate checking function **)
Definition CertificateChecker (e: expr Q) (absenv: analysisResult)
           (P: precond) Qmap subdivs (defVars: FloverMap.t  mType):=
  let tMap := (getValidMap defVars e (FloverMap.empty mType)) in
  match tMap with
  |Succes Gamma =>
   match subdivs with
   | [] => ResultChecker e absenv P Qmap defVars Gamma
   | _ => SubdivsChecker e absenv P subdivs defVars Gamma
   end
  | _ => false
  end.

(**
   General soundness theorem, exposing all invariants that are shown by
   the separate validator functions
**)
Theorem Certificate_checking_is_sound_general (e:expr Q) (absenv:analysisResult)
        P Qmap subdivs defVars:
  forall (E1 E2:env) DeltaMap,
    (forall (v : R) (m' : mType),
        exists d : R, DeltaMap v m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    eval_precond E1 P ->
    unsat_queries Qmap ->
    (forall Qmap, In Qmap (queriesInSubdivs subdivs) -> unsat_queries Qmap) ->
    CertificateChecker e absenv P Qmap subdivs defVars = true ->
    exists Gamma,
      approxEnv E1 (toRExpMap Gamma) absenv (freeVars e) NatSet.empty E2 ->
      exists iv err vR vF m outVars,
        FloverMap.find e absenv = Some (iv, err) /\
        eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) vR REAL /\
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) vF m /\
        (forall vF m,
            eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) vF m ->
            (Rabs (vR - vF) <= Q2R err))%R /\
        ssa e (freeVars e) outVars /\
        validTypes e Gamma /\
        getValidMap defVars e (FloverMap.empty mType) = Succes Gamma /\
        validRanges e absenv E1 (toRTMap (toRExpMap Gamma)) /\
        validErrorBounds e E1 E2 absenv Gamma /\
        validFPRanges e E2 Gamma DeltaMap.
(**
   The proofs is a simple composition of the soundness proofs for the range
   validator and the error bound validator.
**)
Proof.
  intros * deltas_matched P_valid unsat_qs unsat_qs_subdivs certificate_valid.
  unfold CertificateChecker in certificate_valid.
  destruct (getValidMap defVars e (FloverMap.empty mType)) eqn:?; try congruence.
  rename t into Gamma.
  assert (validTypes e Gamma).
  { eapply getValidMap_top_correct; eauto.
    intros. cbn in *; congruence. }
  exists Gamma; intros approxEnv_E1E2.
  destruct subdivs.
  - edestruct result_checking_sound as ((outVars & Hssa) & validR & validErr & validFPR); eauto.
    edestruct validRanges_single as (iv_e & err_e & vR & find_e & eval_real_e & ?); eauto.
    edestruct validErrorBoundsRec_single as ((vFP & mFP & eval_fp_e) & ?); eauto.
    repeat eexists; eauto.
  - edestruct subdivs_checking_sound as ((outVars & Hssa) & validR & validErr & validFPR); eauto.
    edestruct validRanges_single as (iv_e & err_e & vR & find_e & eval_real_e & ?); eauto.
    edestruct validErrorBoundsRec_single as ((vFP & mFP & eval_fp_e) & ?); eauto.
    repeat eexists; eauto.
Qed.

(**
   Soundness proof for the certificate checker.
   Apart from assuming two executions, one in R and one on floats, we assume that
   the real valued execution respects the precondition and dissatisfies the queries.
**)
Theorem Certificate_checking_is_sound (e:expr Q) (absenv:analysisResult)
        P Qmap subdivs defVars:
  forall (E1 E2:env) DeltaMap,
    (forall (v : R) (m' : mType),
        exists d : R, DeltaMap v m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    eval_precond E1 P ->
    unsat_queries Qmap ->
    (forall Qmap, In Qmap (queriesInSubdivs subdivs) -> unsat_queries Qmap) ->
    CertificateChecker e absenv P Qmap subdivs defVars = true ->
    exists Gamma,
      approxEnv E1 (toRExpMap Gamma) absenv (freeVars e) NatSet.empty E2 ->
      exists iv err vR vF m,
        FloverMap.find e absenv = Some (iv, err) /\
        eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) vR REAL /\
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) vF m /\
        (forall vF m,
            eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) vF m ->
            (Rabs (vR - vF) <= Q2R err))%R.
Proof.
  intros * deltas_matched P_valid unsat_qs unsat_qs_subdivs certificate_valid.
  edestruct (Certificate_checking_is_sound_general)as [Gamma validCert]; eauto.
  exists Gamma. intros approxEnvs.
  specialize (validCert approxEnvs).
  destruct validCert as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  repeat eexists; eauto.
Qed.

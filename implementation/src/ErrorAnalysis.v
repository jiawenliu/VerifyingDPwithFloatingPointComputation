From Coq
     Require Import Reals.Reals QArith.Qreals QArith.QArith.

From Snapv
     Require Import ExpressionSemantics Environments 
     Infra.RationalSimps TypeValidator IntervalArithQ.

Fixpoint validErrorBoundsRec (e:expr Q) E1 E2 A Gamma DeltaMap :Prop :=
  (match e with
   | Unop Ln e => False
   | Unop Neg e => validErrorBoundsRec e E1 E2 A Gamma DeltaMap
(*  | Downcast m e => validErrorBoundsRec e E1 E2 A Gamma DeltaMap
*)  
  | Binop b e1 e2 =>
    (b = Div ->
     (forall iv2 err,
         SnapvMap.find e2 A = Some (iv2, err) ->
         let errIv2 := widenIntv iv2 err in
         ((Qleb (ivhi errIv2) 0) && (negb (Qeq_bool (ivhi errIv2) 0))) ||
         ((Qleb 0 (ivlo errIv2)) && (negb (Qeq_bool (ivlo errIv2) 0))) = true)) /\
    validErrorBoundsRec e1 E1 E2 A Gamma DeltaMap /\
    validErrorBoundsRec e2 E1 E2 A Gamma DeltaMap
(*  | Fma e1 e2 e3 =>
    validErrorBoundsRec e1 E1 E2 A Gamma DeltaMap /\
    validErrorBoundsRec e2 E1 E2 A Gamma DeltaMap /\
    validErrorBoundsRec e3 E1 E2 A Gamma DeltaMap
  | Let m x e1 e2 =>
    validErrorBoundsRec e1 E1 E2 A Gamma DeltaMap /\
    (forall iv_e1 err_e1 iv_x err_x,
        SnapvMap.find e1 A = Some (iv_e1, err_e1) ->
        SnapvMap.find (Var Q x) A = Some (iv_x, err_x) ->
        (Q2R (ivhi iv_e1) = Q2R (ivhi iv_x) /\
         Q2R (ivlo iv_e1) = Q2R (ivlo iv_x) /\
         Q2R (err_e1) = Q2R (err_x))) /\
    (forall v__R v__FP,
        eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e1)) v__R REAL ->
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e1) v__FP m ->
        validErrorBoundsRec e2 (updEnv x v__R E1) (updEnv x v__FP E2) A Gamma DeltaMap)
*)      
(*
  | Cond e1 e2 e3 =>
    validErrorBounds e1 E1 E2 A Gamma DeltaMap /\
    validErrorBounds e2 E1 E2 A Gamma DeltaMap /\
    validErrorBounds e3 E1 E2 A Gamma DeltaMap
*)
  | _ => True
   end)  /\
  forall v__R (iv: intv) (err: error),
    eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) v__R REAL ->
    SnapvMap.find e A = Some (iv, err) ->
    (exists v__FP m__FP,
      eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP) /\
    (forall v__FP m__FP,
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP ->
        (Rabs (v__R - v__FP) <= (Q2R err))%R).

Definition validErrorBounds e E1 E2 A Gamma: Prop :=
  forall DeltaMap,
    (forall (v : R) (m' : mType),
        exists d : R, DeltaMap v m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    validErrorBoundsRec e E1 E2 A Gamma DeltaMap.

Lemma validErrorBoundsRec_single e E1 E2 A Gamma DeltaMap:
  validErrorBoundsRec e E1 E2 A Gamma DeltaMap ->
  forall v__R iv err,
    eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) v__R REAL ->
    SnapvMap.find e A = Some (iv, err) ->
    (exists v__FP m__FP,
      eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP) /\
    (forall v__FP m__FP,
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m__FP ->
        (Rabs (v__R - v__FP) <= (Q2R err))%R).
Proof.
  intros validError_e;
    intros;  destruct e; cbn in *; split;
      edestruct validError_e as (? & ? & ?); eauto.
Qed.

(*
Fixpoint validErrorBoundsCmd (c: cmd Q) E1 E2 A Gamma DeltaMap: Prop :=
  match c with
  | Let m x e k =>
    validErrorBoundsRec e E1 E2 A Gamma DeltaMap /\
    (exists iv_e err_e iv_x err_x,
       SnapvMap.find e A = Some (iv_e, err_e) /\
       SnapvMap.find (Var Q x) A = Some (iv_x, err_x) /\
       Qeq_bool err_e err_x = true) /\
    (forall v__R v__FP,
        eval_expr E1 (toRTMap (toRExpMap Gamma)) DeltaMapR (toREval (toRExp e)) v__R REAL ->
        eval_expr E2 (toRExpMap Gamma) DeltaMap (toRExp e) v__FP m ->
        validErrorBoundsCmdRec k (updEnv x v__R E1) (updEnv x v__FP E2) A Gamma DeltaMap)
  | Ret e => validErrorBoundsRec e E1 E2 A Gamma DeltaMap
  end  /\
  forall v__R (iv: intv) (err: error),
    bstep (toREvalCmd (toRCmd c)) E1 (toRTMap (toRExpMap Gamma)) DeltaMapR v__R REAL ->
    SnapvMap.find (getRetExp c) A = Some (iv, err) ->
    (exists v__FP m__FP,
      bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP) /\
    (forall v__FP m__FP,
        bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP ->
        (Rabs (v__R - v__FP) <= (Q2R err))%R).

Definition validErrorBoundsCmd (c: cmd Q) E1 E2 A Gamma: Prop :=
  forall DeltaMap,
    (forall (v : R) (m' : mType),
        exists d : R, DeltaMap v m' = Some d /\ (Rabs d <= mTypeToR m')%R) ->
    validErrorBoundsCmdRec c E1 E2 A Gamma DeltaMap.

Lemma validErrorBoundsCmdRec_single c E1 E2 A Gamma DeltaMap:
  validErrorBoundsCmdRec c E1 E2 A Gamma DeltaMap ->
  forall v__R (iv: intv) (err: error),
    bstep (toREvalCmd (toRCmd c)) E1 (toRTMap (toRExpMap Gamma)) DeltaMapR v__R REAL ->
    SnapvMap.find (getRetExp c) A = Some (iv, err) ->
    (exists v__FP m__FP,
      bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP) /\
    (forall v__FP m__FP,
        bstep (toRCmd c) E2 (toRExpMap Gamma) DeltaMap v__FP m__FP ->
        (Rabs (v__R - v__FP) <= (Q2R err))%R).
Proof.
  intros validError_e;
    intros;  destruct c; cbn in *; split;
      edestruct validError_e as (? & ? & ?); eauto.
Qed.
 *)

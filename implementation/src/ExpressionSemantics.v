From Coq
     Require Import Reals.Reals.

From Snapv.Infra
     Require Import RealRationalProps RationalSimps Ltacs.

From Snapv.Infra
     Require Export ExpressionAbbrevs.
(**
  Finally, define an error function that computes an errorneous value for a
  given type. For a fixed-point datatype, truncation is used and any
  floating-point type is perturbed. As we need not compute on this function we
  define it in Prop.
**)
Definition perturb (rVal:R) (m:mType) (delta:R) :R :=
  match m with
  (* The Real-type has no error *)
  |REAL => rVal
  (* Fixed-point numbers have an absolute error *)
  |F w f => rVal + delta
  (* Floating-point numbers have a relative error *)
  | _ => rVal * (1 + delta)
  end.

Hint Unfold perturb.

(**
Define expression evaluation relation parametric by an "error" epsilon.
The result value exprresses float computations according to the IEEE standard,
using a perturbation of the real valued computation by (1 + delta), where
|delta| <= machine epsilon.
**)
Open Scope R_scope.

Inductive eval_expr (E:env)
          (Gamma: expr R -> option mType)
          (DeltaMap: R -> mType -> option R)
  :(expr R) -> R -> mType -> Prop :=
| Var_load m x v:
    Gamma (Var R x) = Some m ->
    E x = Some v ->
    eval_expr E Gamma DeltaMap (Var R x) v m
| Const_dist m c delta:
    DeltaMap c m = Some delta ->
    Rabs delta <= mTypeToR m ->
    eval_expr E Gamma DeltaMap (Const m c) (perturb c m delta) m
| Unop_neg m mN f1 v1:
    Gamma (Unop Neg f1) = Some mN ->
    isCompat m mN = true ->
    eval_expr E Gamma DeltaMap f1 v1 m ->
    eval_expr E Gamma DeltaMap (Unop Neg f1) (evalUnop Neg v1) mN
| Unop_inv m mN f1 v1 delta:
    Gamma (Unop Ln f1) = Some mN ->
    DeltaMap (evalUnop Ln v1) mN = Some delta ->
    isCompat m mN = true ->
    Rabs delta <= mTypeToR mN ->
    eval_expr E Gamma DeltaMap f1 v1 m ->
    (~ v1 = 0)%R  ->
    eval_expr E Gamma DeltaMap (Unop Ln f1) (perturb (evalUnop Ln v1) mN delta) mN
(*| Downcast_dist m m1 f1 v1 delta:
    Gamma (Downcast m f1) = Some m ->
    DeltaMap v1 m = Some delta ->
    isMorePrecise m1 m = true ->
    Rabs delta <= mTypeToR m ->
    eval_expr E Gamma DeltaMap f1 v1 m1 ->
    eval_expr E Gamma DeltaMap (Downcast m f1) (perturb v1 m delta) m*)
| Binop_dist m1 m2 op f1 f2 v1 v2 delta m:
    Gamma (Binop op f1 f2) = Some m ->
    DeltaMap (evalBinop op v1 v2) m = Some delta ->
    isJoin m1 m2 m = true ->
    Rabs delta <= mTypeToR m ->
    eval_expr E Gamma DeltaMap f1 v1 m1 ->
    eval_expr E Gamma DeltaMap f2 v2 m2 ->
    ((op = Div) -> (~ v2 = 0)%R) ->
    eval_expr E Gamma DeltaMap (Binop op f1 f2) (perturb (evalBinop op v1 v2) m delta) m
.

Definition DeltaMapR: R -> mType -> option R := (fun x m => Some 0).

Close Scope R_scope.

Hint Constructors eval_expr.

(** *)
(*   Show some simpler (more general) rule lemmata *)
(* **)
Lemma Const_dist' DeltaMap m c delta v m' E Gamma:
  Rle (Rabs delta) (mTypeToR m') ->
  DeltaMap c m = Some delta ->
  v = perturb c m delta ->
  m' = m ->
  eval_expr E Gamma DeltaMap (Const m c) v m'.
Proof.
  intros; subst; auto.
Qed.

Hint Resolve Const_dist'.

Lemma Unop_neg' DeltaMap m mN f1 v1 v m' E Gamma:
  eval_expr E Gamma DeltaMap f1 v1 m ->
  v = evalUnop Neg v1 ->
  Gamma (Unop Neg f1) = Some mN ->
  isCompat m mN = true ->
  m' = mN ->
  eval_expr E Gamma DeltaMap (Unop Neg f1) v m'.
Proof.
  intros; subst; eauto.
Qed.

Hint Resolve Unop_neg'.

Lemma Unop_inv' DeltaMap m mN f1 v1 delta v m' E Gamma:
  Rle (Rabs delta) (mTypeToR m') ->
  eval_expr E Gamma DeltaMap f1 v1 m ->
  DeltaMap (evalUnop Ln v1) m' = Some delta ->
  (~ v1 = 0)%R  ->
  v = perturb (evalUnop Ln v1) mN delta ->
  Gamma (Unop Ln f1) = Some mN ->
  isCompat m mN = true ->
  m' = mN ->
  eval_expr E Gamma DeltaMap (Unop Ln f1) v m'.
Proof.
  intros; subst; eauto.
Qed.

Hint Resolve Unop_inv'.

(*
Lemma Downcast_dist' DeltaMap m m1 f1 v1 delta v m' E Gamma:
  isMorePrecise m1 m = true ->
  Rle (Rabs delta) (mTypeToR m') ->
  eval_expr E Gamma DeltaMap f1 v1 m1 ->
  DeltaMap v1 m' = Some delta ->
  v = (perturb v1 m delta) ->
  Gamma (Downcast m f1) = Some m ->
  m' = m ->
  eval_expr E Gamma DeltaMap (Downcast m f1) v m'.
Proof.
  intros; subst; eauto.
Qed.

Hint Resolve Downcast_dist'.*)

Lemma Binop_dist' DeltaMap m1 m2 op f1 f2 v1 v2 delta v m m' E Gamma:
  Rle (Rabs delta) (mTypeToR m') ->
  eval_expr E Gamma DeltaMap f1 v1 m1 ->
  eval_expr E Gamma DeltaMap f2 v2 m2 ->
  DeltaMap (evalBinop op v1 v2) m' = Some delta ->
  ((op = Div) -> (~ v2 = 0)%R) ->
  v = perturb (evalBinop op v1 v2) m' delta ->
  Gamma (Binop op f1 f2) = Some m ->
  isJoin m1 m2 m = true ->
  m = m' ->
  eval_expr E Gamma DeltaMap (Binop op f1 f2) v m'.
Proof.
  intros; subst; eauto.
Qed.

Hint Resolve Binop_dist'.


Lemma Gamma_det e E1 E2 Gamma DeltaMap v1 v2 m1 m2:
  eval_expr E1 Gamma DeltaMap e v1 m1 ->
  eval_expr E2 Gamma DeltaMap e v2 m2 ->
  m1 = m2.
Proof.
  induction e; intros * eval_e1 eval_e2;
    inversion eval_e1; subst;
      inversion eval_e2; subst; try auto;
        match goal with
        | [H1: Gamma ?e = Some ?m1, H2: Gamma ?e = Some ?m2 |- _ ] =>
          rewrite H1 in H2; inversion H2; subst
        end;
        auto.
Qed.

Lemma toRTMap_eval_REAL f:
  forall v E Gamma DeltaMap m, eval_expr E (toRTMap Gamma) DeltaMap (toREval f) v m -> m = REAL.
Proof.
  induction f; intros * eval_f; inversion eval_f; subst.
  repeat
    match goal with
    | H: context[toRTMap _ _] |- _ => unfold toRTMap in H
    | H: context[match ?Gamma ?v with | _ => _ end ] |- _ => destruct (Gamma v) eqn:?
    | H: Some ?m1 = Some ?m2 |- _ => inversion H; try auto
    | H: None = Some ?m |- _ => inversion H
    end; try auto.
  - auto.
  - rewrite (IHf _ _ _ _ _ H5) in H2.
    unfold isCompat in H2.
    destruct m; type_conv; subst; try congruence; auto.
  - rewrite (IHf _ _ _ _ _ H5) in H3.
    unfold isCompat in H3.
    destruct m; type_conv; subst; try congruence; auto.
  - rewrite (IHf1 _ _ _ _ _ H6) in H4.
    rewrite (IHf2 _ _ _ _ _ H9) in H4.
    unfold isJoin in H4; simpl in H4.
    destruct m; try congruence; auto.
  (*
- rewrite (IHf1 _ _ _ _ _ H6) in H4.
    rewrite (IHf2 _ _ _ _ _ H9) in H4.
    rewrite (IHf3 _ _ _ _ _ H10) in H4.
    unfold isJoin3 in H4; simpl in H4.
    destruct m; try congruence; auto.
  - auto.
  - eapply IHf2; eauto.
   
*)
Qed.

(**
  If |delta| <= 0 then perturb v delta is exactly v.
**)
Lemma delta_0_deterministic (v:R) m (delta:R):
  (Rabs delta <= 0)%R ->
  perturb v m delta = v.
Proof.
  intros abs_0; apply Rabs_0_impl_eq in abs_0; subst.
  unfold perturb. destruct m; lra.
Qed.

(**
Evaluation with 0 as machine epsilon is deterministic
**)
Lemma meps_0_deterministic (f:expr R) (E:env) Gamma DeltaMap:
  forall v1 v2,
  eval_expr E (toRTMap Gamma) DeltaMap (toREval f) v1 REAL ->
  eval_expr E (toRTMap Gamma) DeltaMap (toREval f) v2 REAL ->
  v1 = v2.
Proof.
  induction f in E |- *;
    intros v1 v2 ev1 ev2.
  - inversion ev1; inversion ev2; subst.
    rewrite H1 in H6.
    inversion H6; auto.
  - inversion ev1; inversion ev2; subst.
    simpl in *; subst; auto.
  - inversion ev1; inversion ev2; subst; try congruence.
    + rewrite (IHf E v0 v3); [ auto | |];
        destruct m, m0; cbn in *; congruence.
    + cbn in *. Snapv_compute; rewrite (IHf E v0 v3); [auto | | ];
                  destruct m, m0; cbn in *; congruence.
  - inversion ev1; inversion ev2; subst.
    assert (m0 = REAL) by (eapply toRTMap_eval_REAL; eauto).
    assert (m3 = REAL) by (eapply toRTMap_eval_REAL; eauto).
    assert (m1 = REAL) by (eapply toRTMap_eval_REAL; eauto).
    assert (m2 = REAL) by (eapply toRTMap_eval_REAL; eauto).
    subst.
    rewrite (IHf1 E v0 v4); try auto.
    rewrite (IHf2 E v3 v5); try auto.
Qed.

(**
Helping lemmas. Needed in soundness proof.
For each evaluation of using an arbitrary epsilon, we can replace it by
evaluating the subexprressions and then binding the result values to different
variables in the Environment.
 **)
Lemma binary_unfolding b f1 f2 E v1 v2 m1 m2 m Gamma DeltaMap delta:
  (b = Div -> ~(v2 = 0 )%R) ->
  (Rabs delta <= mTypeToR m)%R ->
  DeltaMap (evalBinop b v1 v2) m = Some delta ->
  eval_expr E Gamma DeltaMap f1 v1 m1 ->
  eval_expr E Gamma DeltaMap f2 v2 m2 ->
  eval_expr E Gamma DeltaMap (Binop b f1 f2) (perturb (evalBinop b v1 v2) m delta) m ->
  eval_expr (updEnv 2 v2 (updEnv 1 v1 emptyEnv))
            (updDefVars (Binop b (Var R 1) (Var R 2)) m
                        (updDefVars (Var R 2) m2 (updDefVars (Var R 1) m1 Gamma)))
            (fun x _ => if Req_dec_sum x (evalBinop b v1 v2)
                     then DeltaMap (evalBinop b v1 v2) m
                     else None)
            (Binop b (Var R 1) (Var R 2)) (perturb (evalBinop b v1 v2) m delta) m.
Proof.
  intros no_div_zero err_v delta_map eval_f1 eval_f2 eval_float.
  inversion eval_float; subst.
  rewrite H2 in *.
  repeat
    (match goal with
     | [H1: eval_expr ?E ?Gamma ?DeltaMap ?f ?v1 ?m1,
        H2: eval_expr ?E ?Gamma ?DeltaMap ?f ?v2 ?m2 |- _] =>
       assert (m1 = m2)
         by (eapply Gamma_det; eauto);
       revert H1 H2
     end); intros; subst.
  eapply Binop_dist' with (v1:=v1) (v2:=v2) (delta:=delta); try eauto.
  - eapply Var_load; eauto.
  - eapply Var_load; eauto.
  - destruct Req_dec_sum as [?|H]; auto.
    exfalso; now apply H.
  - unfold updDefVars.
    unfold R_orderedExps.compare; rewrite R_orderedExps.exprCompare_refl; auto.
Qed.

(* *)
(* *)


Lemma eval_eq_env e:
  forall E1 E2 Gamma DeltaMap v m,
    (forall x, E1 x = E2 x) ->
    eval_expr E1 Gamma DeltaMap e v m ->
    eval_expr E2 Gamma DeltaMap e v m.
Proof.
  induction e; intros;
    (match_pat (eval_expr _ _ _ _ _ _) (fun H => inversion H; subst; simpl in H));
    try eauto.
  - eapply Var_load; auto.
    rewrite <- (H n); auto.
    (*
  - econstructor; eauto.
    eapply IHe2; try eassumption.
    intros x. unfold updEnv.
    now destruct (x =? n) eqn:?.*)
Qed.

Lemma eval_expr_ignore_bind e:
  forall x v m Gamma DeltaMap E,
    eval_expr E Gamma DeltaMap e v m ->
    ~ NatSet.In x (freeVars e) ->
    forall v_new,
    eval_expr (updEnv x v_new E) Gamma DeltaMap e v m.
Proof.
  induction e; intros * eval_e no_usedVar *; cbn in *;
    inversion eval_e; subst; try eauto.
  - assert (n <> x).
    { hnf. intros. subst. apply no_usedVar; set_tac. }
    rewrite <- Nat.eqb_neq in H.
    eapply Var_load.
    + unfold updDefVars.
      cbn.
      apply beq_nat_false in H.
      destruct (n ?= x)%nat eqn:?; try auto.
    + unfold updEnv.
      rewrite H; auto.
  - eapply Binop_dist'; eauto;
      [ eapply IHe1 | eapply IHe2];
      eauto;
      hnf; intros; eapply no_usedVar;
      set_tac.
Qed.

Lemma eval_expr_det_ignore_bind2 e:
  forall x v v_new m Gamma E DeltaMap,
    eval_expr (updEnv x v_new E) Gamma DeltaMap e v m ->
    ~ NatSet.In x (freeVars e) ->
    eval_expr E Gamma DeltaMap e v m.
Proof.
  induction e; intros * eval_e no_usedVar *; cbn in *;
    inversion eval_e; subst; try eauto.
  - assert (n <> x).
    { hnf. intros. subst. apply no_usedVar; set_tac. }
    rewrite <- Nat.eqb_neq in H.
    eapply Var_load.
    + unfold updDefVars.
      cbn.
      apply beq_nat_false in H.
      destruct (n ?= x)%nat eqn:?; try auto.
    + unfold updEnv.
      rewrite <- H1.
      unfold updEnv.
      now rewrite H.
  - eapply Binop_dist'; eauto;
      [ eapply IHe1 | eapply IHe2];
      eauto;
      hnf; intros; eapply no_usedVar;
      set_tac.
Qed.

Lemma swap_Gamma_eval_expr e E vR m Gamma1 Gamma2 DeltaMap:
  (forall e, Gamma1 e = Gamma2 e) ->
  eval_expr E Gamma1 DeltaMap e vR m ->
  eval_expr E Gamma2 DeltaMap e vR m.
Proof.
  revert E vR Gamma1 Gamma2 DeltaMap m;
    induction e; intros * Gamma_eq eval_e;
      inversion eval_e; subst; simpl in *;
        [ eapply Var_load
        | eapply Const_dist'
        | eapply Unop_neg'
        | eapply Unop_inv'
        | eapply Binop_dist'
 (*       | eapply Fma_dist'
        | eapply Downcast_dist'
        | eapply Let_dist*)
        (* | eapply Cond_then
        | eapply Cond_else *) ]; try eauto;
          rewrite <- Gamma_eq; auto.
Qed.

Lemma Rmap_updVars_comm Gamma n m:
  forall x,
    updDefVars n REAL (toRMap Gamma) x = toRMap (updDefVars n m Gamma) x.
Proof.
  unfold updDefVars, toRMap; simpl.
  intros x; destruct (R_orderedExps.compare x n); auto.
Qed.

Lemma eval_expr_functional E Gamma DeltaMap e v1 v2 m:
  eval_expr E Gamma DeltaMap e v1 m ->
  eval_expr E Gamma DeltaMap e v2 m ->
  v1 = v2.
Proof.
  revert E v1 v2 m.
  induction e; intros E v1 v2 m__FP Heval1 Heval2.
  - inversion Heval1; inversion Heval2; subst.
    now replace v1 with v2 by congruence.
  - inversion Heval1; inversion Heval2; subst.
    now replace delta with delta0 by congruence.
  - destruct u; inversion Heval1; inversion Heval2; subst.
    + f_equal; eapply IHe; eauto.
      erewrite Gamma_det; eauto.
    + replace m0 with m in * by (eapply Gamma_det; eauto).
      replace v3 with v0 in * by (eapply IHe; eauto).
      replace delta with delta0 by congruence.
      reflexivity.
  - inversion Heval1; inversion Heval2; subst.
    replace m1 with m0 in * by (eapply Gamma_det; eauto).
    replace m3 with m2 in * by (eapply Gamma_det; eauto).
    replace v4 with v0 in * by (eapply IHe1; eauto).
    replace v5 with v3 in * by (eapply IHe2; eauto).
    now replace delta with delta0 by congruence.
  (*- inversion Heval1; inversion Heval2; subst.*)
    (*replace m1 with m0 in * by (eapply Gamma_det; eauto).
    replace m4 with m2 in * by (eapply Gamma_det; eauto).
    replace m5 with m3 in * by (eapply Gamma_det; eauto).
    replace v5 with v0 in * by (eapply IHe1; eauto).
    replace v6 with v3 in * by (eapply IHe2; eauto).
    replace v7 with v4 in * by (eapply IHe3; eauto).
    now replace delta with delta0 by congruence.*)
  (*- inversion Heval1; inversion Heval2; subst.*)
(*    replace m3 with m1 in * by (eapply Gamma_det; eauto).
    replace v3 with v0 in * by (eapply IHe; eauto).
    replace delta with delta0 by congruence.
    reflexivity.*)
  (*- inversion Heval1; inversion Heval2; subst.*)

    (*replace v0 with v3 in * by (eapply IHe1; eauto).
    eapply IHe2; eauto.*)
    (*
  - inversion Heval1; inversion Heval2; subst.
    + eapply IHe2; erewrite Gamma_det; eauto.
    + exfalso. apply H6. eapply IHe1; eauto. erewrite Gamma_det; eauto.
    + exfalso. apply H17. eapply IHe1; eauto. erewrite Gamma_det; eauto.
    + eapply IHe3; erewrite Gamma_det; eauto.
*)
Qed.

Lemma real_eval_expr_ignores_delta_map (f:expr R) (E:env) Gamma:
  forall v1 DeltaMap,
  eval_expr E (toRTMap Gamma) DeltaMap (toREval f) v1 REAL ->
  eval_expr E (toRTMap Gamma) DeltaMapR (toREval f) v1 REAL.
Proof.
  induction f in E |- *; unfold DeltaMapR;
    intros v1 DeltaMap ev1.
  - inversion ev1; subst.
    constructor; auto.
  - inversion ev1; subst.
    simpl in *; subst; auto.
    eapply Const_dist'; eauto.
    apply Rabs_0_impl_eq in H3; f_equal; now symmetry.
  - inversion ev1; subst; try congruence.
    + unfold isCompat in H2; destruct m; cbn in H2; try congruence; clear H2.
      specialize (IHf _ _ _ H5).
      eapply Unop_neg'; eauto.
    + unfold isCompat in H3; destruct m; cbn in H3; try congruence; clear H3.
      specialize (IHf _ _ _ H5).
      eapply Unop_inv'; eauto.
      apply Rabs_0_impl_eq in H4; f_equal; now symmetry.
  - inversion ev1; subst.
    assert (m1 = REAL) by (eapply toRTMap_eval_REAL; eauto).
    assert (m2 = REAL) by (eapply toRTMap_eval_REAL; eauto).
    subst.
    specialize (IHf1 _ _ _ H6).
    specialize (IHf2 _ _ _ H9).
    eapply Binop_dist'; eauto.
    apply Rabs_0_impl_eq in H5; f_equal; now symmetry.
  (*- inversion ev1; subst.*)
    
  (*- inversion ev1; subst.*)
 (*- inversion ev1; subst.*)
    (*econstructor; eauto.*)
Qed.

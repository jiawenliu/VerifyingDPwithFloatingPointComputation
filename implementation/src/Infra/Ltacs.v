(** Ltac definitions **)
From Coq
     Require Import Bool.Bool Reals.Reals QArith.QArith QArith.Qreals micromega.Psatz.
From Snapv.Infra
     Require Import RealSimps NatSet RationalSimps RealRationalProps Results.

Global Set Implicit Arguments.

Ltac iv_assert iv name:=
  assert (exists ivlo ivhi, iv = (ivlo, ivhi)) as name by (destruct iv; repeat eexists; auto).

(** Automatic translation and destruction of conjuctinos with andb into Props **)
Ltac andb_to_prop H :=
  apply Is_true_eq_left in H;
  apply andb_prop_elim in H;
  let Left := fresh "L" in
  let Right := fresh "R" in
  destruct H as [Left Right];
  apply Is_true_eq_true in Left;
  apply Is_true_eq_true in Right;
  try andb_to_prop Left;
  try andb_to_prop Right.

Ltac split_bool :=
  match goal with
  | [|- (_ && _) = true ] => apply Is_true_eq_true;
                             apply andb_prop_intro;
                             split;
                             apply Is_true_eq_left
  | _ => fail "Cannot case split on non-boolean conjunction"
  end.

Ltac canonize_Q_prop :=
  match goal with
  | [ H: Qle_bool ?a ?b = true |- _] => rewrite Qle_bool_iff in H
  | [ H: Qleb ?a ?b = true |- _ ] => rewrite Qle_bool_iff in H
  | [ H: Qeq_bool ?a ?b = true |- _] => rewrite Qeq_bool_iff in H
  end.

Ltac canonize_Q_to_R :=
  match goal with
  | [ H: (?a <= ?b)%Q |- _ ] => apply Qle_Rle in H
  | [ H: (?a == ?b)%Q |- _ ] => apply Qeq_eqR in H
  | [ H: context [Q2R 0] |- _ ] => rewrite Q2R0_is_0 in H
  | [ |- context [Q2R 0] ] => rewrite Q2R0_is_0
  end.

Ltac canonize_hyps := repeat canonize_Q_prop; repeat canonize_Q_to_R.

Ltac Q2R_to_head_step :=
  match goal with
  | [ H: context[Q2R ?a + Q2R ?b] |- _] => rewrite <- Q2R_plus in H
  | [ H: context[Q2R ?a - Q2R ?b] |- _] => rewrite <- Q2R_minus in H
  | [ H: context[Q2R ?a * Q2R ?b] |- _] => rewrite <- Q2R_minus in H
  | [ |- context[Q2R ?a + Q2R ?b]] => rewrite <- Q2R_plus
  | [ |- context[Q2R ?a - Q2R ?b]] => rewrite <- Q2R_minus
  | [ |- context[Q2R ?a * Q2R ?b]] => rewrite <- Q2R_minus
  end.

Ltac Q2R_to_head := repeat Q2R_to_head_step.

Definition optionBind (X: Type) (Y: Type) (v: option X) (f: X -> Y) (e: Y): Y :=
  match v with
  | Some v => f v
  | None => e
  end.

Definition resultBind (X:Type) (r:result X) (f: X  -> result X) :result X :=
  match r with
  | Succes res => f res
  | _ => r
  end.

Definition resultReturn (X:Type) (r:X) :=
  Succes r.

Notation "'olet' x ':=' u 'in' t" := (optionBind u (fun x => t) None)
                                       (only parsing, at level 0, t at level 200).
Notation "'plet' x ':=' u 'in' t" := (optionBind u (fun x => t) False)
                                       (only parsing, at level 0, t at level 200).
Notation "'rlet' x ':=' u 'in' t" := (resultBind u (fun x => t))
                                       (only parsing, at level 0, t at level 200).
Notation "'ret' x" := (resultReturn x) (only parsing, at level 0 ).

Ltac optionD :=
  match goal with
  |H: context[resultBind ?v ?f] |- _ =>
   destruct v eqn:?
  |H: context[optionBind ?v ?default ?f] |- _ =>
   destruct v eqn:?
  end.

Lemma optionBind_eq (X Y: Type) v (f: X -> Y) (e: Y):
  match v with |Some val => f val | None => e end = optionBind v f e.
Proof.
  reflexivity.
Qed.

Lemma optionBind_cond X (a:bool) (b c: X):
  (if a then b else c) = match a with |true => b |false => c end.
Proof.
  reflexivity.
Qed.

Ltac remove_matches := rewrite optionBind_eq in *.

Ltac remove_matches_asm := rewrite optionBind_eq in * |- .

Ltac remove_conds := rewrite <- andb_lazy_alt in *.

Ltac remove_conds_asm := rewrite <- andb_lazy_alt in * |- .

Ltac result_factorize_asm :=
  match goal with
  | [ H: ?t = ?u |- context [resultBind ?t _ ]]
    => rewrite H; cbn
  | [ H1: ?t = ?u, H2: context [resultBind ?t _] |- _ ]
    => rewrite H1 in H2; cbn in H2
  | [ H: context [resultBind ?t _ ] |- _ ]
    => destruct t eqn:?; cbn in H; try congruence
  end.

Ltac result_factorize :=
  result_factorize_asm ||
  match goal with
  | [ |- context [resultBind ?t _] ]
    => destruct t eqn:?; cbn; try congruence
  end.

Ltac match_factorize_asm :=
  match goal with
  | [ H: ?t = ?u |- context [optionBind ?t _ _]]
    => rewrite H; cbn
  | [ H1: ?t = ?u, H2: context [optionBind ?t _ _] |- _ ]
    => rewrite H1 in H2; cbn in H2
  | [ H: context [optionBind ?t _ _] |- _ ]
    => destruct t eqn:?; cbn in H; try congruence
  end.

Ltac match_factorize :=
  match_factorize_asm ||
  match goal with
  | [ |- context [optionBind ?t _ _] ]
    => destruct t eqn:?; cbn; try congruence
  end.

Ltac pair_factorize :=
  match goal with
  | [H: context[let (_, _) := ?p in _] |- _] => destruct p; cbn in H
  end.

Ltac destr_factorize :=
  match goal with
  | [H1: _ ?v = Some ?a, H2: _ ?v = Some ?b |- _]
      => rewrite H1 in H2; inversion H2; subst; clear H2
  | [H1:  _ ?k ?M = Some ?a, H2: _ ?k ?M = Some ?b |- _]
    => rewrite H1 in H2; inversion H2; subst; clear H2
  end.

Ltac match_simpl :=
  try remove_conds;
  try remove_matches;
  repeat match_factorize;
  repeat result_factorize;
  try pair_factorize.

Ltac bool_factorize :=
  match goal with
  | [H: _ = true |- _] => andb_to_prop H
  end.

Ltac Snapv_compute_asm :=
  repeat (
      (try remove_conds_asm;
       try remove_matches_asm;
       repeat match_factorize_asm;
       repeat result_factorize_asm;
       try pair_factorize) ||
      bool_factorize).

Ltac Snapv_compute :=
  repeat (
      (try remove_conds;
      try remove_matches;
      repeat match_factorize;
      repeat result_factorize;
      try pair_factorize) ||
      bool_factorize).

(* Ltac destruct_if := *)
(*   match goal with *)
(*   | [H: if ?c then ?a else ?b = _ |- _ ] => *)
(*     case_eq ?c; *)
(*     let name := fresh "cond" in *)
(*     intros name; *)
(*     rewrite name in *; *)
(*     try congruence *)
(*   | [H: _ |- if ?c then ?a else ?b = _] => *)
(*       case_eq ?c; *)
(*       let name := fresh "cond" in *)
(*       intros name; *)
(*       rewrite name in *; *)
(*       try congruence *)
(*       end. *)

(* Ltac match_destr t:= *)
(*   match goal with *)
(*   | H: context [optionBind (SnapvMap.find ?k ?M) _ _] |- _ => *)
(*     destruct (SnapvMap.find (elt:=intv * error) k M); idtac H *)
(*   end. *)

Tactic Notation "match_pat" open_constr(pat) tactic(t) :=
  match goal with
  | [H: ?ty |- _ ] => unify pat ty; t H
  end.

Ltac telling_rewrite pat hyp :=
  match goal with
  | [H: context[pat] |- _ ] => rewrite hyp in H; constr:(H)
  end.

Tactic Notation "unify asm" open_constr(pat) hyp(H):=
  telling_rewrite pat H.

(* Takes a field-structure equality expression, tries to rewrite the *)
(* the left side in the goal with right if the equality holds        *)
Ltac field_rewrite H :=
  let tmp := fresh "tmp" in
  assert H as tmp by (try field; try lra); rewrite tmp; clear tmp.

Ltac destruct_ex H pat :=
  match type of H with
  | exists v, ?H' =>
               let vFresh:=fresh v in
               let fN := fresh "ex" in
               destruct H as [vFresh fN];
               destruct_ex fN pat
  | _ => destruct H as pat
  end.

Tactic Notation "destruct_smart" simple_intropattern(pat) hyp(H) := destruct_ex H pat.

(* Debugging tactics, if scripts fail *)
Ltac debug_term t :=
  let name := fresh "debug" in
  let res := (eval compute in t) in
  assert (t = res) as name by (vm_compute; auto);
  rewrite name; clear name.

Ltac step f :=
  cbn iota beta delta [f].

Require Import Snapv.Infra.Ltacs.
Require Import Snapv.Infra.NatSet.
Require Import Snapv.IntervalArithQ.

Ltac debug_auto :=
  match goal with
  | [ |- context[match ?t with Some _ => _ | None => _ end] ] => debug_term t
  | [ |- context[if ?t  then _ else _ ]] => debug_term t
  end.

Ltac solve_set :=
  match goal with
  | [ |- context[ ?x mem ?S ]] => debug_term (x mem S)
  end.

Ltac subset_tac :=
  match goal with
  | [ |- context[ isSupersetIntv ?new_iv ?iv ]] =>
    let name := fresh "subset" in
    let res := eval compute in (isSupersetIntv new_iv iv) in
        assert (name : isSupersetIntv new_iv iv = res)
      by (vm_compute; auto); rewrite name
  end.

Ltac clear_if_true_once :=
  match goal with
  | [ H: _ = true |- _ ] => clear H
  end.

Ltac clear_true := repeat clear_if_true_once.

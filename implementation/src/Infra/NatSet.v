Require Import Coq.MSets.MSets Coq.Arith.PeanoNat.

(**
 Module for an ordered type with leibniz, based on code from coq-club mailing list
http://coq-club.inria.narkive.com/zptqoou2/how-to-use-msets
**)
Module OWL.
  Definition t := nat.
  Definition eq := @eq t.
  Definition eq_equiv :Equivalence eq := eq_equivalence.
  Definition lt := lt.
  Definition lt_strorder : StrictOrder lt := Nat.lt_strorder.
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    now unfold eq; split; subst.
  Qed.
  Definition compare := Nat.compare.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
  intros; case_eq (compare x y); constructor.
  now apply Compare_dec.nat_compare_eq.
  now apply Compare_dec.nat_compare_Lt_lt.
  now apply Compare_dec.nat_compare_Gt_gt.
Qed.

Definition eq_dec := Peano_dec.eq_nat_dec.
Definition eq_leibniz a b (H:eq a b) := H.
End OWL.

Module NatSet := MakeWithLeibniz OWL.

Module NatSetProps := WPropertiesOn OWL NatSet.

Notation "S1 ∪ S2" := (NatSet.union S1 S2) (at level 80, right associativity).

Notation "'{{' x '}}'" := (NatSet.singleton x) (at level 0, no associativity).

Notation "S1 -- S2" := (NatSet.diff S1 S2) (at level 80, right associativity).

Notation "x 'mem' S" := (NatSet.mem x S) (at level 0, no associativity).

Notation "x '∈' S" := (NatSet.In x S) (at level 100, no associativity).

Lemma not_in_not_mem:
  forall n S,
    NatSet.mem n S = false ->
    ~ NatSet.In n S.
Proof.
  intros * not_mem; hnf; intros not_in.
  rewrite <- NatSet.mem_spec in not_in;
    rewrite not_in in *;
    congruence.
Qed.

Lemma add_spec_strong:
  forall x y S,
    (x ∈ (NatSet.add y S)) <-> x = y \/ ((~ (x = y)) /\ (x ∈ S)).
Proof.
  split; intros x_in_add.
  - rewrite NatSet.add_spec in x_in_add.
    case_eq (Nat.eqb x y); intros x_eq_case.
    + left; apply Nat.eqb_eq; auto.
    + right; destruct x_in_add as [x_eq | x_in_S]; subst.
      * rewrite Nat.eqb_refl in x_eq_case; congruence.
      * split; try auto.
        hnf; intros; subst.
        rewrite Nat.eqb_refl in x_eq_case; congruence.
  - rewrite NatSet.add_spec.
    destruct x_in_add as [ x_eq | [x_neq x_in_S]]; auto.
Qed.

Lemma subset_diff_to_subset_union s1 s2 s3:
  NatSet.Subset (s1 -- s3) s2 ->
  NatSet.Subset s1 (NatSet.union s2 s3).
Proof.
  intros diff.
  hnf in diff |-*.
  intros a Hin1.
  specialize (diff a).
  destruct (NatSet.mem a s3) eqn: Hmem.
  - rewrite NatSet.mem_spec in Hmem.
    rewrite NatSet.union_spec.
    now right.
  - apply not_in_not_mem in Hmem.
    rewrite NatSet.union_spec.
    left.
    apply diff.
    apply NatSetProps.Dec.F.diff_3; auto.
Qed.

Ltac set_bool_to_prop :=
  match goal with
  | [ H: NatSet.mem ?x _ = true |- _ ] => rewrite NatSet.mem_spec in H
  | [ H: NatSet.mem ?x _ = false |- _] => apply not_in_not_mem in H
  | [ |- context [NatSet.mem ?x _]] => rewrite NatSet.mem_spec
  end.

Ltac solve_simple_sets :=
  match goal with
  | [ H: NatSet.In ?x ?S1 |- NatSet.In ?x (NatSet.union ?S1 ?S2)]
    => rewrite NatSet.union_spec; auto
  end.

Ltac set_hnf_tac :=
  match goal with
  | [ H: context [NatSet.In ?x (NatSet.diff ?A ?B)] |- _] => rewrite NatSet.diff_spec in H; destruct H
  | [ H: NatSet.Subset ?SA ?SB |- NatSet.In ?v ?SB] => apply H
  | [ H: NatSet.In ?x (NatSet.singleton ?y) |- _] => apply NatSetProps.Dec.F.singleton_1 in H
  | [ H: NatSet.In ?x NatSet.empty |- _ ] => inversion H
  | [ H: NatSet.In ?x (NatSet.union ?S1 ?S2) |- _ ] => rewrite NatSet.union_spec in H
  | [ H: NatSet.In ?x (NatSet.add ?y ?S) |- _ ] => rewrite add_spec_strong in H
  | [ |- context [NatSet.In ?x (NatSet.union ?SA ?SB)]] => rewrite NatSet.union_spec
  | [ |- context [NatSet.In ?x (NatSet.diff ?A ?B)]] => rewrite NatSet.diff_spec
  | [ |- context [NatSet.In ?x (NatSet.singleton ?y)]] => rewrite NatSet.singleton_spec
  | [ |- context [NatSet.In ?x (NatSet.remove ?y ?S)]] => rewrite NatSet.remove_spec
  | [ |- context [NatSet.In ?x (NatSet.add ?y ?S)]] => rewrite NatSet.add_spec
  | [ |- context [NatSet.Subset ?SA ?SB]] => hnf; intros
  end.

Ltac set_tac :=
  repeat set_bool_to_prop;
  repeat solve_simple_sets;
  repeat set_hnf_tac;
  simpl in *;
  repeat solve_simple_sets;
  try auto.

Require Import Coq.ZArith.ZArith Coq.ZArith.Zbool Coq.micromega.Psatz Recdef.
Require Import Snapv.Infra.Abbrevs.

Inductive affine_form (V: Type): Type :=
| Const: V -> affine_form V
| Noise: nat -> V -> affine_form V -> affine_form V.

Fixpoint get_const V (a: affine_form V): V := match a with
| Const v => v
| Noise n c a' => get_const a'
end.

(* Helper function to serve as a measure for fixpoint termination *)
Fixpoint aff_length (V: Type) (a: affine_form V): nat := match a with
| Const _ => 0
| Noise _ _ a' => 1 + aff_length a'
end.

Definition aff_length_tuple V (a: affine_form V * affine_form V) :=
  (aff_length (fst a) + aff_length (snd a))%nat.

Definition aff_tuple_order V (a b:affine_form V * affine_form V):=
  (aff_length_tuple a < aff_length_tuple b)%nat.

Fixpoint get_max_index_aux V (current_max: nat) (a: affine_form V): nat := match a with
| Const _ => current_max
| Noise n v a' => if (Nat.leb current_max n) then
                    get_max_index_aux n a'
                else
                    get_max_index_aux current_max a'
end.

Functional Scheme get_max_index_aux_ind := Induction for get_max_index_aux Sort Prop.

Definition get_max_index V (a: affine_form V) := get_max_index_aux 0 a.

Definition fresh V (n: nat) (a: affine_form V) :=
  (n > get_max_index a)%nat.

Lemma get_mia_monotonic V (a: affine_form V) (n: nat):
  (get_max_index_aux n a >= n)%nat.
Proof.
  functional induction get_max_index_aux V n a.
  - lia.
  - apply Nat.leb_le in e0.
    unfold Peano.ge; auto.
    eapply Nat.le_trans; eauto.
  - lia.
Qed.

Lemma get_mia_monotonic2 V (a: affine_form V) (p q: nat):
  (p >= q)%nat ->
  (get_max_index_aux p a >= get_max_index_aux q a)%nat.
Proof.
  revert p q; induction a; intros p q pgeqq; simpl in *.
  - auto.
  - case_eq (p <=? n)%nat; intros pleqn.
    + assert ((q <=? n)%nat = true) as qleqn by (apply Nat.leb_le; apply Nat.leb_le in pleqn; lia).
      rewrite qleqn.
      lia.
    + case_eq (q <=? n)%nat; intros qleqn.
      * apply leb_complete_conv in pleqn.
        assert (p >= n)%nat by lia.
        specialize (IHa p n H); auto.
      * specialize (IHa p q pgeqq); auto.
Qed.

Lemma fresh_noise_compat V (a: affine_form V) m n v:
  fresh m (Noise n v a) -> fresh m a.
Proof.
  unfold fresh, get_max_index in *; destruct a; intros.
  rewrite get_max_index_aux_equation.
  - simpl in H. lia.
  - simpl in H.
    case_eq (n <=? n0); intros; rewrite H0 in H.
    + apply Nat.leb_le in H0.
      simpl.
      auto.
    + simpl.
      apply leb_complete_conv in H0.
      assert (get_max_index_aux n a >= get_max_index_aux n0 a)%nat
        by (apply get_mia_monotonic2; lia).
      lia.
Qed.

Lemma fresh_noise_gt V (a: affine_form V) m n v:
  fresh m (Noise n v a) -> (m > n)%nat.
Proof.
  intros A.
  unfold fresh, get_max_index in *; induction a.
  - rewrite get_max_index_aux_equation in A.
    now simpl in A.
  - simpl in A.
    destruct (n <=? n0) eqn: Hn.
    + apply Nat.leb_le in Hn.
      pose proof (get_mia_monotonic a n0) as mono.
      apply (le_lt_trans _ _ _ mono) in A.
      lia.
    + apply leb_complete_conv in Hn.
      auto.
Qed.

Lemma fresh_noise V (a: affine_form V) m n v:
  (m > n)%nat -> fresh m a -> fresh m (Noise n v a).
Proof.
  intros A B.
  unfold fresh, get_max_index in *; induction a.
  - trivial.
  - simpl in *.
    destruct (n <=? n0) eqn: Hn.
    + assumption.
    + apply leb_complete_conv in Hn.
      apply IHa.
      clear IHa A Hn n v v0.
      assert ((get_max_index_aux n0 a >= get_max_index_aux 0 a)%nat)
        by (eapply get_mia_monotonic2; omega).
      apply (le_lt_trans _ _ _ H B).
Qed.

Lemma fresh_monotonic V (a: affine_form V) m n:
  (m >= n)%nat -> fresh n a -> fresh m a.
Proof.
  unfold fresh; lia.
Qed.

Lemma fresh_inc V (a: affine_form V) n:
  fresh n a ->
  fresh (n + 1) a.
Proof.
  unfold fresh.
  lia.
Qed.

Lemma fresh_n_gt_O V (a: affine_form V) n:
  fresh n a ->
  (n > 0)%nat.
Proof.
  destruct a.
  - unfold fresh, get_max_index; rewrite get_max_index_aux_equation; auto.
  - intros ? % fresh_noise_gt; lia.
Qed.
    

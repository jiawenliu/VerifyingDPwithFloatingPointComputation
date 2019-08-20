(** * IterFlip.v: An example of probabilistic termination *)

Require Export Prog.
Require ZArith.
Set Implicit Arguments.

Module IterFlip (Univ:Universe).
Module RP := (Rules Univ).
(* begin hide *)
Import Univ.
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.
(* end hide *)
(** ** Definition of a random walk 
We interpret the probabilistic program 
<<
let rec iter x = if flip() then iter (x+1) else x 
>>*)
Import ZArith.

Definition Fiter (f: Z -> (distr Z)) (x:Z) := Mif Flip (f (Zsucc x)) (Munit x).

Lemma Fiter_mon : forall f g : Z -> distr Z, 
  (forall n, le_distr (f n) (g n)) -> forall n, le_distr (Fiter f n) (Fiter g n).
unfold Fiter; intros.
apply Mif_mon; auto.
Qed.

Definition iterflip : Z -> (distr Z) := Mfix Fiter Fiter_mon.

(** ** Main result 
     Probability for [iter] to terminate is $1$ *)
(** *** Auxiliary function $p_n$
   Definition $ p_n = 1 - \frac{1}{2^n} $ *)

Fixpoint p (n : nat) : U := match n with O => 0 | (S n) => [1/2] * p n + [1/2] end.

Lemma p_eq : forall n:nat, p n == [1-]([1/2]^n).
induction n; simpl; auto.
setoid_rewrite IHn.
apply Ueq_trans with ([1/2] * [1-]([1/2]^n) + [1-][1/2]);auto.
Qed.
Hint Resolve p_eq.

Lemma p_le : forall n:nat, [1-]([1/]1+n) <= p n.
intro; setoid_rewrite (p_eq n).
apply Uinv_le_compat.
induction n; simpl; intros; auto.
apply Ule_trans with ([1/2] * ([1/]1+n)); auto.
Qed.

Hint Resolve p_le.

Lemma lim_p_one : 1 <= lub p.
apply Ule_lt_lim; intros.
assert (exc (fun n : nat => t <= [1-] ([1/]1+n))).
assert (~(0==[1-] t)).
red; intro; apply H; auto.
apply Ule_trans with ([1-] 0); auto.
apply (archimedian H0); auto; intros m H1.
apply exc_intro with m; auto.
apply H0; auto; intros.
apply Ule_trans with (p x); auto.
apply Ule_trans with ([1-] ([1/]1+x)); auto.
Qed.

Hint Resolve lim_p_one.

(** *** Proof of probabilistic termination  *)
Definition q1 (z1 z2:Z) := 1.

Lemma iterflip_term : okfun (fun k => 1) iterflip q1.
unfold iterflip; intros.
apply okfun_le_compat with (fun (k:Z) => lub p) q1; auto.
apply fixrule with (p:= fun (x:Z) => p); auto; intros.
red; simpl; intros.
unfold Fiter.
red.
setoid_rewrite (Mif_eq Flip (f (Zsucc x)) (Munit x) (q1 x)); simpl.
unfold unit; simpl.
setoid_rewrite flip_ctrue.
setoid_rewrite flip_cfalse.
unfold q1 at 2.
setoid_rewrite (Umult_one_left [1/2]).
apply Uplus_le_compat_left.
apply Ule_trans with (p i * [1/2]); auto.
apply Umult_le_compat_left; auto.
apply (H (Zsucc x)%Z).
Qed.

End IterFlip.

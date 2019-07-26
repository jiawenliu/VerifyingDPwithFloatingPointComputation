Require Export Carac.
Set Implicit Arguments.
Require Arith.

Module Ycart (Univ:Universe).
(* begin hide *)
Import Univ.
Module CP := (CaracFun Univ).
Import CP.
Import CP.RP.
Import CP.RP.PP.
Import CP.RP.PP.MP.
Import CP.RP.PP.MP.UP.
(* end hide *)

Section UniformSec.
(** * Ycart.v: Axiomatisation of the uniform measure *)

(** ** Interval [[0,x]] *)
Hypothesis Ule_dec : forall a b, {a<=b}+{b<a}.
 
Definition inf (a : U) := carac  (fun x => Ule_dec x a).

Variable uniform : distr U.
Hypothesis uniform_inf : forall a, mu uniform (inf a) == a.

Lemma uniform_one : mu uniform (f_one U) == 1.
intros; apply Ueq_trans with (mu uniform (inf 1)); auto.
apply mu_stable_eq; red; auto.
intros; unfold inf,carac.
case (Ule_dec x 1); intros; auto.
absurd (x<=1); auto.
Qed.

Lemma uniform_inv_inf : forall a, mu uniform (finv (inf a)) == [1-] a.
intros; rewrite inv_minus_distr; auto.
rewrite uniform_inf; rewrite uniform_one; auto.
Qed.

Hint Resolve uniform_inf uniform_inv_inf uniform_one.

(** * Ycart.v: An exemple of partial termination  *)

(** ** Program giving an example of partiality
given a function F : int -> U
<<
let rec ycart x = if uniform < F x then x else ycart (x+1)
>>
The probability of termination is $1-\prod_{k=x}^{\infty}(1-F(k))$
*)
Variable F : nat -> U.

Definition FYcart (f:nat -> distr nat) n := 
    Mlet uniform (fun x => if Ule_dec x (F n) then Munit n else f (S n)).

Lemma FYcart_mon : forall f g : nat -> distr nat, 
       (forall n, le_distr (f n) (g n)) -> forall n, le_distr (FYcart f n) (FYcart g n).
unfold FYcart; intros; auto.
apply Mlet_mon; intros; auto.
case (Ule_dec x (F n)); auto.
Qed.

Definition Ycart : nat -> distr nat := Mfix FYcart FYcart_mon.

(** ** Properties of Ycart *)

Lemma FYcart_val : forall q:nat->U, forall f x, 
     mu (FYcart f x) q == F x * q x + [1-](F x) * mu (f (S x)) q.
intros; unfold  FYcart.
unfold Mlet; simpl.
unfold star.
apply Ueq_trans with 
   (mu uniform (fplus (fmult (q x) (inf (F x))) (fmult (mu (f (S x)) q) (finv (inf (F x)))))).
apply mu_stable_eq; red; intros.
unfold fplus,fmult,finv,inf, carac.
case (Ule_dec x0 (F x)); simpl; intros; repeat Usimpl; auto.
assert (fok:fplusok (fmult (q x) (inf (F x))) (fmult (mu (f (S x)) q) (finv (inf (F x))))); auto.
rewrite (mu_stable_plus uniform fok).
rewrite (mu_stable_mult uniform (q x)).
rewrite (mu_stable_mult uniform (mu (f (S x)) q)).
rewrite uniform_inf.
apply Uplus_eq_compat; auto.
rewrite uniform_inv_inf; auto.
Qed.

Definition P (x k : nat) := prod (fun i => [1-]F (x+i)) k.

Definition p (x:nat) (n:nat) := sigma (fun k => F (x+k) * P x k) n.

Lemma P_prod : forall x k, F (x+k) * P x k == P x k - P x (S k).
intros; unfold P; rewrite prod_minus; auto.
Qed.
Hint Resolve P_prod.

Lemma p_diff : forall x n,  p x n == [1-] P x n.
unfold p; intros.
apply Ueq_trans with (sigma (fun k => P x k - P x (S k)) n).
apply sigma_eq_compat; intros; auto.
rewrite sigma_minus_decr.
unfold P; rewrite prod_0; auto.
unfold P; auto.
Qed.
Hint Resolve p_diff.

Lemma p_lub : forall x, lub (p x) == [1-] prod_inf (fun i => [1-]F (x+i)).
unfold prod_inf; intros.
apply Ueq_trans with (lub (fun n => [1-] P x n)).
apply lub_eq_stable; auto.
apply Ueq_trans with ([1-]glb (P x)); auto.
Qed.
Hint Resolve p_lub.

Lemma p_equation : forall x n,  p x (S n) == F x + [1-](F x) * p (S x) n.
unfold p; intros.
rewrite sigma_S_lift.
unfold P at 1; rewrite prod_0; Usimpl.
apply Uplus_eq_compat.
replace ((x+0)%nat) with x; auto.
rewrite <- sigma_mult; auto.
apply sigma_eq_compat; intros; auto.
unfold P; rewrite prod_S_lift.
rewrite Umult_assoc.
rewrite (Umult_sym (F (x+S k)) ([1-]F (x+0))).
rewrite <- Umult_assoc.
apply Umult_eq_compat.
replace ((x+0)%nat) with x; auto.
apply Umult_eq_compat.
replace ((x + S k)%nat) with ((S x + k)%nat); auto.
omega.
apply prod_eq_compat; intro; auto.
replace ((x + S k0)%nat) with ((S x + k0)%nat); auto.
omega.
red; intros.
apply Ule_trans with (P (S x) k); auto.
change (P (S x) k <= [1-]p (S x) k).
rewrite p_diff; auto.
Qed.
Hint Resolve p_equation.

Lemma Ycart_term1 : forall x, mu (Ycart x) (f_one nat) == [1-] prod_inf (fun i => [1-]F (x+i)).
intros; apply Ueq_trans with (lub (p x)); auto.
apply Ule_antisym.
apply (fixrule_up_lub FYcart FYcart_mon) with (p:=p) (q:=fun (x:nat) => f_one nat); red; intros.
red; rewrite FYcart_val.
unfold f_one; Usimpl.
apply Ule_trans with (F x0 + [1-] F x0 * p (S x0) i).
repeat Usimpl; auto.
apply (H (S x0)).
rewrite p_equation; auto.
apply (fixrule FYcart FYcart_mon) with (p:=p) (q:=fun (x:nat) => f_one nat); intros.
unfold p; rewrite sigma_0; auto.
repeat red; intros.
rewrite FYcart_val.
unfold f_one; Usimpl.
apply Ule_trans with (F x0 + [1-] F x0 * p (S x0) i).
rewrite p_equation; auto.
repeat Usimpl; auto.
apply (H (S x0)).
Qed.

(** A  shorter proof using mu (Ycart x) (f_one nat) = mu h. muYcart h x *)

Lemma Ycart_term2 : forall x, mu (Ycart x) (f_one nat) == [1-] prod_inf (fun i => [1-]F (x+i)).
intros; apply Ueq_trans with (mufix (fun (p:nat->U) (y:nat) => F y + [1-](F y) * p (S y)) x).
unfold Ycart; apply Ueq_sym.
apply mufix_mu with (q:=fun (y:nat) => f_one nat); intros.
red; auto.
rewrite FYcart_val; unfold f_one; repeat Usimpl; auto.
apply Ueq_trans with (lub (p x)); auto.
unfold mufix.
apply lub_eq_stable.
intro n; generalize x; induction n; simpl; intros; auto.
rewrite IHn; auto.
Qed.

Lemma le_dec : forall x, dec (fun y => le y x).
intros x y; case (le_lt_dec y x); auto with arith.
Defined.

Lemma lt_dec : forall x, dec (fun y => lt y x).
intros x y; case (le_lt_dec x y); auto with arith.
Defined.

Lemma gt_dec : forall x, dec (lt x).
intros x y; case (le_lt_dec y x); auto with arith.
Defined.

Lemma Ycart_ltx : forall x, mu (Ycart x) (carac (lt_dec x)) <= 0.
intros; apply Ule_trans with (mufix (fun (p:nat->U) (y:nat) => [1-](F y) * p (S y)) x).
unfold Ycart; apply mu_mufix_le with (q:=fun (y:nat) => carac (lt_dec y)); intros; auto.
red; intros; rewrite FYcart_val.
rewrite carac_zero; auto with arith.
repeat Usimpl.
apply mu_monotonic; apply carac_incl; red; auto with arith.
apply mufix_inv with (f:=fun y:nat => 0); auto.
Qed.

Lemma Ycart_eqx : forall x, mu (Ycart x) (carac (eq_nat_dec x)) == F x.
intros; apply Ueq_trans with (mufix (fun (p:nat->U) (y:nat) => F y) x).
unfold Ycart; apply Ueq_sym; apply mufix_mu with (q:=fun (y:nat) => carac (eq_nat_dec y)); intros; auto.
rewrite FYcart_val.
rewrite (carac_one (eq_nat_dec x0) x0); auto with arith; Usimpl.
setoid_replace (mu (f (S x0)) (carac (eq_nat_dec x0))) with 0; repeat Usimpl; auto.
apply Ule_zero_eq; apply Ule_trans with (mu (Mfix FYcart FYcart_mon (S x0)) (carac (eq_nat_dec x0))).
apply H.
apply Ule_trans with (2:=Ycart_ltx (S x0)); auto.
apply mu_monotonic; apply carac_incl; red; intros; subst; auto with arith.
exact (mufix_cte F x).
Qed.

End UniformSec.
End Ycart.

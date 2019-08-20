(** * Uprop.v : Properties of operators on [[0,1]] *)
Set Implicit Arguments.
Unset Standard Proposition Elimination Names.
Require Export Arith.
Require Export Omega.
Require Export Ubase.
Module Univ_prop (Univ:Universe).
Import Univ.

Hint Resolve Ueq_refl.
Hint Resolve Upos Unit Udiff_0_1 Unth_prop Ueq_le.
Hint Resolve Uplus_sym Uplus_assoc Umult_sym Umult_assoc.
Hint Resolve Uinv_one Uinv_opp_left Uinv_plus_left.
Hint Resolve Uplus_zero_left Umult_one_left Udistr_plus_right Udistr_inv_right.
Hint Resolve Uplus_le_compat_left Umult_le_compat_left Uinv_le_compat.
Hint Resolve lub_le le_lub lub_eq_mult lub_eq_plus_cte_right.
Hint Resolve Ule_total Ule_class.
Hint Immediate Ueq_sym Ule_antisym.
Open Scope nat_scope.
Open Scope U_scope.

(** ** Direct consequences of axioms  *)

Lemma Ueq_class : forall x y, class (x==y).
red; intros.
apply Ule_antisym;
apply Ule_class; intuition.
Qed.

Lemma Ueq_double_neg : forall x y : U, ~ ~x == y -> x == y.
exact Ueq_class.
Qed.
Hint Resolve Ueq_class.
Hint Immediate Ueq_double_neg.

Lemma Ule_orc : forall x y, orc (x<=y) (~ x<=y).
auto.
Qed.
Implicit Arguments Ule_orc [].

Lemma Ueq_orc : forall x y, orc (x==y) (~ x==y).
auto.
Qed.
Implicit Arguments Ueq_orc [].

Lemma Ule_0_1 : 0 <= 1.
auto.
Qed.

Lemma Ule_refl : forall x:U,x <= x.
auto.
Qed.
Hint Resolve Ule_refl.

Add Relation  U Ule reflexivity proved by Ule_refl transitivity proved by Ule_trans as Ule_Relation.

(** ** Properties of == derived from properties of $\le$ *)

Lemma Ueq_trans : forall x y z:U, x == y -> y == z -> x == z.
intros; apply Ule_antisym; apply Ule_trans with y; auto.
Qed.
Hint Resolve Ueq_trans.

Lemma Uplus_eq_compat_left : forall x y z:U, x == y -> (x + z) == (y + z).
intros; apply Ule_antisym; auto.
Qed.

Hint Resolve Uplus_eq_compat_left.

Lemma Uplus_eq_compat_right : forall x y z:U, x == y -> (z + x) == (z + y).
intros; apply Ueq_trans with (x + z); auto.
apply Ueq_trans with (y + z); auto.
Qed.

Lemma Umult_eq_compat_left : forall x y z:U, x == y -> (x * z) == (y * z).
intros;  apply Ule_antisym; auto.
Qed.
Hint Resolve Umult_eq_compat_left.

Lemma Umult_eq_compat_right :  forall x y z:U, x == y -> (z * x) == (z * y).
intros; apply Ueq_trans with (x * z); auto.
apply Ueq_trans with (y * z); auto.
Qed.

Hint Resolve Uplus_eq_compat_right Umult_eq_compat_right.

Lemma Uinv_opp_right : forall x, x + [1-] x == 1.
intros; apply Ueq_trans with ([1-] x + x); auto.
Qed.
Hint Resolve Uinv_opp_right.

(** ** [U] is a setoid *)

Lemma Usetoid : Setoid_Theory U Ueq.
split; red ; auto. apply Ueq_trans.
Qed.

Add Setoid U Ueq Usetoid as U_setoid.

Add Morphism Uplus with signature Ueq ==> Ueq ==> Ueq as Uplus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ueq_trans with (x1+x4); auto.
Qed.

Add Morphism Umult with signature Ueq ==> Ueq ==> Ueq as Umult_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ueq_trans with (x1 * x4); auto.
Qed.

Hint Immediate Umult_eq_compat Uplus_eq_compat.

Add Morphism Uinv with signature Ueq ==> Ueq as Uinv_eq_compat.
intros; apply Ule_antisym; auto.
Qed.

Add Morphism Ule with signature Ueq ==> Ueq ==> iff as Ule_eq_compat_iff.
intros x1 x2 eq1 x3 x4 eq2; split; intro Hle.
apply Ule_trans with x1; auto.
apply Ule_trans with x3; auto.
apply Ule_trans with x2; auto.
apply Ule_trans with x4; auto.
Qed.

Lemma Ule_eq_compat : 
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 <= x3 -> x2 <= x4.
intros x1 x2 eq1 x3 x4 eq2; elim (Ule_eq_compat_iff eq1 eq2); auto.
Qed.

(** ** Definition and properties of $x<y$ *)
Definition Ult (r1 r2:U) : Prop := ~ (r2 <= r1).

Infix "<" := Ult : U_scope.

Hint Unfold Ult.


Add Morphism Ult with signature Ueq ==> Ueq ==> iff as Ult_eq_compat_iff.
unfold Ult, not; intros x1 x2 eq1 x3 x4 eq2.
generalize (Ule_eq_compat_iff eq2 eq1); intuition.
Qed.

Lemma Ult_eq_compat : 
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 < x3 -> x2 < x4.
intros x1 x2 eq1 x3 x4 eq2; elim (Ult_eq_compat_iff eq1 eq2); auto.
Qed.

Lemma Ult_class : forall x y, class (x<y).
unfold Ult; auto.
Qed.
Hint Resolve Ult_class.

(* begin hide *)
(** Tactic for left normal form with respect to associativity *)
Ltac norm_assoc_left := 
     match goal with 
      | |- context [(Uplus ?X1 (Uplus ?X2 ?X3))] 
        => (setoid_rewrite (Uplus_assoc X1 X2 X3))
     end.

Ltac norm_assoc_right := 
     match goal with 
      | |- context [(Uplus (Uplus ?X1 ?X2) ?X3)] 
        => (setoid_rewrite <- (Uplus_assoc X1 X2 X3))
     end.
(* end hide *)

(** *** Properties of $x \leq y$ *)

Lemma Ule_zero_eq :  forall x, x <= 0 -> x == 0.
intros; apply Ule_antisym; auto.
Qed.

Lemma Uge_one_eq : forall x, 1 <= x -> x == 1.
intros; apply Ule_antisym; auto.
Qed.

Hint Immediate Ule_zero_eq Uge_one_eq.

(** *** Properties of $x < y$ *)

Lemma Ult_neq : forall x y:U, x < y -> ~x == y.
unfold Ult; red; auto.
Qed.

Lemma Ult_neq_rev : forall x y:U, x < y -> ~y == x.
unfold Ult; red; auto.
Qed.

Lemma Ult_trans : forall x y z, x<y -> y<z -> x <z.
repeat red; intros.
apply (Ule_total y z); intros; auto.
apply H; apply Ule_trans with z; auto.
Qed.

Lemma Ult_le : forall x y:U, x < y -> x <= y.
unfold Ult; intros; apply Ule_class; repeat red; intros.
assert (x < x).
apply Ult_trans with y; auto.
apply H1; auto. 
Qed.

Lemma Ule_diff_lt : forall x y : U,  x <= y -> ~x==y -> x < y.
red; intuition.
Qed.

Hint Immediate Ult_neq Ult_neq_rev Ult_le.
Hint Resolve Ule_diff_lt.

Lemma Ult_neq_zero : forall x, ~(0==x) -> 0 < x.
auto.
Qed.

Hint Resolve Ule_total Ult_neq_zero.

(** ** Properties of $+$ and $\times$  *)

Lemma Udistr_plus_left :  forall x y z, y <= [1-] z -> (x * (y + z)) == (x * y + x * z).
intros.
setoid_rewrite (Umult_sym x (y+z)); setoid_rewrite (Umult_sym x y); 
setoid_rewrite (Umult_sym x z);auto.
Qed.

Lemma Udistr_inv_left :  forall x y, [1-](x * y) == (x * ([1-] y)) + [1-] x.
intros.
setoid_rewrite (Umult_sym x y).
setoid_rewrite (Udistr_inv_right y x); auto.
Qed.

Hint Resolve Uinv_eq_compat Udistr_plus_left Udistr_inv_left.

Lemma Uplus_perm2 : forall x y z:U, x + (y + z) == y + (x + z).
intros; setoid_rewrite (Uplus_assoc x y z).
setoid_rewrite (Uplus_sym x y); auto.
Qed.

Lemma Umult_perm2 : forall x y z:U, x * (y * z) == y * (x * z).
intros; setoid_rewrite (Umult_assoc x y z).
setoid_rewrite (Umult_sym x y); auto.
Qed.

Lemma Uplus_perm3 : forall x y z : U, (x + (y + z)) == z + (x + y).
intros; setoid_rewrite (Uplus_assoc x y z); auto.
Qed.

Lemma Umult_perm3 : forall x y z : U, (x * (y * z)) == z * (x * y).
intros; setoid_rewrite (Umult_assoc x y z); auto.
Qed.

Hint Resolve Uplus_perm2 Umult_perm2 Uplus_perm3 Umult_perm3.

Lemma Uplus_le_compat_right : forall x y z:U, (x <= y) -> (z + x <= z + y).
intros; setoid_rewrite (Uplus_sym z x);
setoid_rewrite (Uplus_sym z y);auto.
Qed.

Hint Resolve Uplus_le_compat_right.

Lemma Uplus_le_compat : forall x y z t:U, x <= y -> z <= t -> (x + z <= y + t).
intros; apply Ule_trans with (y + z); auto.
Qed.
Hint Immediate Uplus_le_compat.

Lemma Uplus_zero_right : forall x:U, x + 0 == x.
intros; setoid_rewrite (Uplus_sym x 0); auto.
Qed.
Hint Resolve Uplus_zero_right.

(* ** Properties of [1-] *)

Lemma Uinv_zero : [1-] 0 == 1.
apply Ueq_trans with (([1-] (0 + 0))+0); auto.
apply Ueq_trans with ([1-] (0 + 0)); auto.
setoid_rewrite (Uplus_zero_right 0); auto.
Qed.
Hint Resolve Uinv_zero.


Lemma Uinv_inv : forall x : U, [1-] [1-] x == x.
intros; apply Ueq_trans with ([1-] (x + [1-] x) + x); auto.
apply Ueq_sym; auto.
setoid_rewrite (Uinv_opp_right x); setoid_rewrite Uinv_one; auto.
Qed.
Hint Resolve Uinv_inv.

Lemma Uinv_simpl :  forall x y : U, [1-] x == [1-] y -> x == y.
intros; setoid_rewrite <- (Uinv_inv x); 
 setoid_rewrite <- (Uinv_inv y); auto.
Qed.

Hint Immediate Uinv_simpl.

(** ** More properties on [+] and [*]  and [Uinv] *)

Lemma Umult_le_compat_right :  forall x y z: U,  x <= y -> (z * x) <= (z * y).
intros; setoid_rewrite (Umult_sym z x); setoid_rewrite (Umult_sym z y).
apply Umult_le_compat_left; trivial.
Qed.

Hint Resolve Umult_le_compat_right.

Add Morphism Umult with signature Ule ++> Ule ++> Ule as Umult_le_compat.
intros x1 x2 H1 x3 x4 H2; apply Ule_trans with (x1 * x4); auto.
Qed.
Hint Immediate Umult_le_compat.

Lemma Umult_one_right : forall x:U, (x * 1) == x.
intros; setoid_rewrite (Umult_sym x 1); auto.
Qed.
Hint Resolve Umult_one_right.


Lemma Udistr_plus_left_le :  forall x y z : U, x * (y + z) <= x * y + x * z.
intros; apply (Ule_total y ([1-]z)); intros; auto.
setoid_replace (y+z) with ([1-]z+z); auto.
rewrite Udistr_plus_left; auto.
apply Ule_antisym; auto.
rewrite Uinv_opp_left; auto.
Qed.

Lemma Uplus_eq_simpl_right : 
forall x y z:U, z <= [1-] x -> z <= [1-] y -> (x + z) == (y + z) -> x == y.
intros; apply Ule_antisym.
apply Uplus_le_simpl_right with z; auto.
apply Uplus_le_simpl_right with z; auto.
Qed.

Lemma Ule_plus_right : forall x y, x <= x + y.
intros; apply Ule_eq_compat with (x + 0) (x + y); auto.
Qed.

Lemma Ule_plus_left : forall x y, y <= x + y.
intros; apply Ule_eq_compat with (0 + y) (x + y); auto.
Qed.
Hint Resolve Ule_plus_right Ule_plus_left.

Lemma Ule_mult_right : forall x y, x * y <= x .
intros; apply Ule_eq_compat with (x * y) (x * 1); auto.
Qed.

Lemma Ule_mult_left : forall x y, x * y <= y.
intros; apply Ule_eq_compat with (x * y) (1 * y); auto.
Qed.
Hint Resolve Ule_mult_right Ule_mult_left.

Lemma Uinv_le_perm_right : forall x y:U, x <= [1-] y -> y <= [1-] x.
intros; apply Ule_trans with ([1-] ([1-] y)); auto.
Qed.
Hint Resolve Uinv_le_perm_right.

Lemma Uinv_le_perm_left :  forall x y:U, [1-] x <= y -> [1-] y <= x.
intros; apply Ule_trans with ([1-] ([1-] x)); auto.
Qed.
Hint Resolve Uinv_le_perm_left.

Lemma Uinv_eq_perm_left :  forall x y:U, x == [1-] y -> [1-] x == y.
intros; apply Ueq_trans with ([1-] ([1-] y)); auto.
Qed.
Hint Immediate Uinv_eq_perm_left.

Lemma Uinv_eq_perm_right :  forall x y:U, [1-] x == y ->  x == [1-] y.
intros; apply Ueq_trans with ([1-] ([1-] x)); auto.
Qed.

Hint Immediate Uinv_eq_perm_right.

Lemma Uinv_plus_right : forall x y, y <= [1-] x -> [1-] (x + y) + y == [1-] x.
intros; setoid_rewrite (Uplus_sym x y); auto.
Qed.
Hint Resolve Uinv_plus_right.

Lemma Uplus_eq_simpl_left : 
forall x y z:U, x <= [1-] y -> x <= [1-] z -> (x + y) == (x + z) -> y == z.
intros x y z H1 H2; setoid_rewrite (Uplus_sym x y); setoid_rewrite (Uplus_sym x z); auto.
intros; apply Uplus_eq_simpl_right with x; auto.
Qed.

Lemma Uplus_eq_zero_left : forall x y:U, x <= [1-] y -> (x + y) == y -> x == 0.
intros; apply Uplus_eq_simpl_right with y; auto.
setoid_rewrite H0; auto.
Qed.

Lemma Uinv_le_trans : forall x y z t, x <= [1-] y -> z<=x -> t<=y -> z<= [1-] t.
intros; apply Ule_trans with x; auto.
apply Ule_trans with ([1-] y); auto.
Qed.


Lemma Uinv_plus_left_le : forall x y, [1-]y <= [1-](x+y) +x.
intros; apply (Ule_total y ([1-]x)); auto; intros.
rewrite Uinv_plus_left; auto.
apply Ule_trans with x; auto.
Qed.

Lemma Uinv_plus_right_le : forall x y, [1-]x <= [1-](x+y) +y.
intros; apply (Ule_total y ([1-]x)); auto; intros.
rewrite Uinv_plus_right; auto.
apply Ule_trans with y; auto.
Qed.

Hint Resolve Uinv_plus_left_le Uinv_plus_right_le.

(** ** Disequality *)

Lemma neq_sym : forall x y, ~x==y -> ~y==x.
red; intros; apply H; auto.
Qed.
Hint Immediate neq_sym.

Lemma Uinv_neq_compat : forall x y, ~x == y -> ~ [1-] x == [1-] y.
red; intros; apply H; auto.
Qed.

Lemma Uinv_neq_simpl : forall x y, ~ [1-] x == [1-] y-> ~x == y.
red; intros; apply H; auto.
Qed.

Hint Resolve Uinv_neq_compat.
Hint Immediate Uinv_neq_simpl.

Lemma Uinv_neq_left : forall x y, ~x == [1-] y -> ~ [1-] x == y.
red; intros; apply H; auto.
Qed.

Lemma Uinv_neq_right : forall x y, ~ [1-] x == y -> ~x == [1-] y.
red; intros; apply H; auto.
Qed.

(** *** Properties of [<]  *)

Lemma Ult_antirefl : forall x:U, ~x < x.
unfold Ult; intuition.
Qed.

Lemma Ult_0_1 : (0 < 1).
red; intuition.
Qed.

Lemma Ule_lt_trans : forall x y z:U, x <= y -> y < z -> x < z.
unfold Ult; intuition.
apply H0; apply Ule_trans with x; trivial.
Qed.

Lemma Ult_le_trans : forall x y z:U, x < y -> y <= z -> x < z.
unfold Ult; intuition.
apply H; apply Ule_trans with z; trivial.
Qed.

Hint Resolve Ult_0_1 Ult_antirefl.


Lemma Uplus_neq_zero_left : forall x y, ~(0 == x) -> ~(0 == x+y).
intros; apply Ult_neq.
apply Ult_le_trans with x; auto.
Qed.

Lemma Uplus_neq_zero_right : forall x y, ~(0 == y) -> ~(0 == x+y).
intros; apply Ult_neq.
apply Ult_le_trans with y; auto.
Qed.

Lemma not_Ult_le : forall x y, ~x < y -> y <= x.
intros; apply Ule_class; auto.
Qed.

Lemma Ule_not_lt : forall x y, x <= y -> ~y < x.
repeat red; intros.
apply H0; auto.
Qed.

Hint Immediate not_Ult_le Ule_not_lt.

Theorem Uplus_le_simpl_left : forall x y z : U, z <= [1-] x -> z + x <= z + y -> x <= y.
intros.
apply Uplus_le_simpl_right with z; auto.
apply Ule_trans with (z + x); auto.
apply Ule_trans with (z + y); auto.
Qed.


Lemma Uplus_lt_compat_left : forall x y z:U, z <= [1-] y -> x < y -> (x + z) < (y + z).
unfold Ult; intuition.
apply H0; apply Uplus_le_simpl_right with z; trivial.
Qed.


Lemma Uplus_lt_compat_right : forall x y z:U, z <= [1-] y -> x < y -> (z + x) < (z + y).
intros; setoid_rewrite (Uplus_sym z x).
intros; setoid_rewrite (Uplus_sym z y).
apply Uplus_lt_compat_left; auto.
Qed.

Hint Resolve Uplus_lt_compat_right Uplus_lt_compat_left.

Lemma Uplus_lt_compat :
forall x y z t:U, z <= [1-] x -> t <= [1-] y -> x < y -> z < t -> (x + z) < (y + t).
intros; apply Ult_trans with (y + z); auto.
apply Uplus_lt_compat_left; auto.
apply Ule_trans with t; auto.
Qed.

Hint Immediate Uplus_lt_compat.

Lemma Uplus_lt_simpl_left : forall x y z:U, z <= [1-] y -> (z + x) < (z + y) -> x < y.
unfold lt; repeat red; intros.
apply H0; auto.
Qed.

Lemma Uplus_lt_simpl_right : forall x y z:U, z <= [1-] y -> (x + z) < (y + z) -> x < y.
unfold lt; repeat red; intros.
apply H0; auto.
Qed.

Lemma Uplus_one_le : forall x y, x + y == 1 -> [1-] y <= x.
intros; apply Ule_class; red; intros.
assert (x < [1-] y); auto.
assert (x + y < [1-] y + y); auto.
assert (x + y < 1); auto.
setoid_rewrite <- (Uinv_opp_left y); auto. 
Qed.
Hint Immediate Uplus_one_le.

Theorem Uplus_eq_zero : forall x, x <= [1-] x -> (x + x) == x -> x == 0.
intros x H1 H2; apply Uplus_eq_simpl_left with x; auto.
setoid_rewrite H2; auto.
Qed.

Lemma Umult_zero_left : forall x, 0 * x == 0.
intros; apply Uinv_simpl.
setoid_rewrite (Udistr_inv_right 0 x); auto.
setoid_rewrite Uinv_zero.
setoid_rewrite (Umult_one_left x); auto.
Qed.
Hint Resolve Umult_zero_left.

Lemma Umult_zero_right : forall x, (x * 0) == 0.
intros; setoid_rewrite (Umult_sym x 0); auto.
Qed.
Hint Resolve Uplus_eq_zero Umult_zero_right.

(** *** Compatibility of operations with respect to order. *)

Lemma Umult_le_simpl_right : forall x y z, ~(0 == z) -> (x * z) <= (y * z) -> x <= y.
intros; apply Umult_le_simpl_left with z; auto.
setoid_rewrite (Umult_sym z x); 
setoid_rewrite (Umult_sym z y);trivial.
Qed.
Hint Resolve Umult_le_simpl_right.

Lemma Umult_simpl_right : forall x y z, ~(0 == z) -> (x * z) == (y * z) -> x == y.
intros; apply Ule_antisym; auto.
apply Umult_le_simpl_right with z; auto.
apply Umult_le_simpl_right with z; auto.
Qed.

Lemma Umult_simpl_left : forall x y z, ~(0 == x) -> (x * y) == (x * z) -> y == z.
intros; apply Ule_antisym; auto.
apply Umult_le_simpl_left with x; auto.
apply Umult_le_simpl_left with x; auto.
Qed.

Lemma Umult_lt_compat_left : forall x y z, ~(0 == z)-> x < y -> (x * z) < (y * z).
unfold Ult,not;intros.
apply H0; apply Umult_le_simpl_right with z; auto.
Qed.

Lemma Umult_lt_compat_right : forall x y z, ~(0 == z) -> x < y -> (z * x) < (z * y).
unfold Ult,not;intros.
apply H0; apply Umult_le_simpl_left with z; auto.
Qed.


Lemma Umult_lt_simpl_right : forall x y z, ~(0 == z) -> (x * z) < (y * z) -> x < y.
unfold Ult,not;intros.
apply H0; auto.
Qed.

Lemma Umult_lt_simpl_left : forall x y z, ~(0 == z) -> (z * x) < (z * y) -> x < y.
unfold Ult,not;intros.
apply H0; auto.
Qed.

Hint Resolve Umult_lt_compat_left Umult_lt_compat_right.

Lemma Umult_zero_simpl_right : forall x y, 0 == x*y -> ~(0 == x) -> (0 == y).
intros.
apply Umult_simpl_left with x; auto.
rewrite (Umult_zero_right x); trivial.
Qed.

Lemma Umult_zero_simpl_left : forall x y, 0 == x*y -> ~(0 == y) -> 0 == x.
intros.
apply Umult_simpl_right with y; auto.
rewrite (Umult_zero_left y); trivial.
Qed.


Lemma Umult_neq_zero : forall x y, ~(0 == x) -> ~(0 == y) -> ~(0 == x*y).
red; intros.
apply H0; apply Umult_zero_simpl_right with x; trivial.
Qed.
Hint Resolve Umult_neq_zero.

Lemma Umult_lt_zero : forall x y, 0 < x -> 0 < y -> 0 < x*y.
auto.
Qed.
Hint Resolve Umult_lt_zero.

Lemma Umult_lt_compat : forall x y z t, x < y -> z < t -> x * z < y * t.
intros.
assert (0<y); auto.
apply Ule_lt_trans with x; auto.
assert (0<t); auto.
apply Ule_lt_trans with z; auto.
apply (Ueq_orc 0 z); auto; intros.
rewrite <- H3.
rewrite Umult_zero_right; auto.
apply Ult_trans with (y * z); auto.
Qed.

(** *** More Properties *)

Lemma Uplus_one : forall x y, [1-] x <= y -> x + y == 1.
intros; apply Ule_antisym; auto.
apply Ule_trans with (x + [1-] x); auto.
Qed.
Hint Resolve Uplus_one.

Lemma Uplus_one_right : forall x, x + 1 == 1.
auto.
Qed.

Lemma Uplus_one_left : forall x:U, 1 + x == 1.
auto.
Qed.
Hint Resolve Uplus_one_right Uplus_one_left. 

Lemma Uinv_mult_simpl : forall x y z t, x <= [1-] y -> (x * z) <= [1-] (y * t).
intros; apply Ule_trans with x; auto.
intros; apply Ule_trans with ([1-] y); auto.
Qed.
Hint Resolve Uinv_mult_simpl.

Lemma Umult_inv_plus :   forall x y, x * [1-] y + y == x + y * [1-] x.
intros; apply Ueq_trans with (x * [1-] y + y * ([1-] x + x)).
setoid_rewrite (Uinv_opp_left x); auto.
assert (H:[1-] x <= [1-] x); auto.
setoid_rewrite (Udistr_plus_left y H).
apply Ueq_trans with (x * [1-] y + y * x + y * [1-] x).
norm_assoc_right; auto.
setoid_rewrite (Umult_sym y x).
assert (H1:[1-] y <= [1-] y); auto.
setoid_rewrite <- (Udistr_plus_left x H1).
setoid_rewrite (Uinv_opp_left y); auto.
Qed.
Hint Resolve Umult_inv_plus.

Lemma Umult_inv_plus_le : forall x y z, y <= z -> x * [1-] y + y <= x * [1-] z + z.
intros.
setoid_rewrite (Umult_inv_plus x y); 
setoid_rewrite (Umult_inv_plus x z); auto.
Qed.
Hint Resolve Umult_inv_plus_le.

Lemma Uplus_lt_Uinv :   forall x y, x+y < 1 -> x <= [1-] y.
intros; apply (Ule_total x ([1-]y)); intro; auto.
case H.
rewrite Uplus_one; auto. 
Qed.

Lemma Uinv_lt_perm_left: forall x y : U, [1-] x < y -> [1-] y < x.
unfold Ult; intuition.
Qed.

Lemma Uinv_lt_perm_right: forall x y : U, x < [1-] y -> y < [1-] x.
unfold Ult; intuition.
Qed.

Hint Immediate Uinv_lt_perm_left Uinv_lt_perm_right.

Lemma Uinv_lt_one : forall x, 0 < x -> [1-]x < 1.
intro; setoid_replace 0 with ([1-]1); auto.
Qed.

Lemma Uinv_lt_zero : forall x, x < 1 -> 0 < [1-]x.
intro; setoid_replace 1 with ([1-]0); auto.
Qed.

Hint Resolve Uinv_lt_one Uinv_lt_zero.

Lemma Umult_lt_right : forall p q, p <1 -> 0 < q -> p * q < q.
intros.
apply Ult_le_trans with (1 * q); auto.
Qed.

Lemma Umult_lt_left : forall p q, 0 < p -> q < 1 -> p * q < p.
intros.
apply Ult_le_trans with (p * 1); auto.
Qed.

Hint Resolve Umult_lt_right Umult_lt_left.

(** ** Definition of $x^n$ *)
Fixpoint Uexp (x:U) (n:nat) {struct n} : U :=
   match n with 0 => 1 | (S p) => x * Uexp x p end.

Infix "^" := Uexp : U_scope.

Lemma Uexp_1 : forall x, x^1==x.
simpl; auto.
Qed.

Lemma Uexp_0 : forall x, x^0==1.
simpl; auto.
Qed.

Lemma Uexp_zero : forall n, (0<n)%nat -> 0^n==0.
destruct n; simpl; intro; auto.
casetype False; omega.
Qed.

Lemma Uexp_one : forall n, 1^n==1.
induction n; simpl; auto.
rewrite IHn; auto.
Qed.

Lemma Uexp_le_compat : 
      forall x n m, (n<=m)%nat -> x^m <= x^n.
induction 1; simpl; auto.
apply Ule_trans with (x^m); auto.
Qed.

Lemma Uexp_Ule_compat : 
      forall x y n,  x<=y -> x^n <= y^n.
induction n; simpl; intros; auto.
apply Ule_trans with (x * (y^n)); auto.
Qed.

Add Morphism Uexp with signature Ueq ==> (@eq nat) ==> Ueq as Uexp_eq_compat.
intros; apply Ule_antisym; apply Uexp_Ule_compat; auto.
Qed.

Lemma Uexp_inv_S : forall x n, ([1-]x^(S n))==x*([1-]x^n)+[1-]x.
simpl; auto.
Qed.

Lemma Uexp_lt_compat : forall p q n, (O<n)%nat->(p<q)->(p^n<q^n).
induction n; simpl; intros; auto.
casetype False; omega.
destruct n; auto.
apply Umult_lt_compat; auto with arith.
Qed.

Hint Resolve Uexp_lt_compat.

Lemma Uexp_lt_zero : forall p n, (0<p)->(0<p^n).
destruct n; intros; auto.
rewrite <- (Uexp_zero (n:=S n)); auto with arith.
Qed.
Hint Resolve Uexp_lt_zero.

Lemma Uexp_lt_one : forall p n, (0<n)%nat->(p<1)->(p^n<1).
intros; rewrite <- (Uexp_one n); auto with arith.
Qed.
Hint Resolve Uexp_lt_one.

Lemma Uexp_lt_antimon: forall p n m, (n<m)%nat-> 0<p -> p < 1 -> p^m < p^n.
induction 1; simpl; intros; auto with arith. 
apply Ult_trans with (p*p^n); auto with arith. 
Qed.
Hint Resolve Uexp_lt_antimon.

(** ** Definition and properties of $x \& y$
   A conjonction operation which coincides with min and mult 
   on 0 and 1, see Morgan & McIver *)

Definition Uesp (x y:U) := [1-] ([1-] x + [1-] y).

Infix "&" := Uesp  (left associativity, at level 40) : U_scope.

Lemma Uinv_plus_esp : forall x y, [1-] (x + y) == [1-] x & [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv x); setoid_rewrite (Uinv_inv y); auto.
Qed.
Hint Resolve Uinv_plus_esp.

Lemma Uinv_esp_plus : forall x y, [1-] (x & y) == [1-] x + [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)); trivial.
Qed.
Hint Resolve Uinv_esp_plus.


Lemma Uesp_sym : forall x y : U, x & y == y & x.
intros; unfold Uesp; auto.
Qed.

Lemma Uesp_one_right : forall x : U, x & 1 == x.
intro; unfold Uesp.
setoid_rewrite Uinv_one.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Qed.

Lemma Uesp_one_left : forall x : U, 1 & x  == x.
intros; rewrite Uesp_sym; apply Uesp_one_right.
Qed.

Lemma Uesp_zero : forall x y, x <= [1-] y -> x & y == 0.
intros; unfold Uesp.
setoid_rewrite <- Uinv_one; auto.
Qed.

Hint Resolve Uesp_sym Uesp_one_right Uesp_one_left Uesp_zero.

Lemma Uesp_zero_right : forall x : U, x & 0 == 0.
auto.
Qed.

Lemma Uesp_zero_left : forall x : U, 0 & x == 0.
auto.
Qed.

Hint Resolve Uesp_zero_right Uesp_zero_left.

Add Morphism Uesp with signature Ueq ==> Ueq ==> Ueq as  Uesp_eq_compat.
unfold Uesp; intros.
apply Uinv_eq_compat.
rewrite H; rewrite H0; auto.
Qed.

Lemma Uesp_le_compat : forall x y z t, x<=y -> z <=t -> x&z <= y&t.
unfold Uesp; intros.
apply Uinv_le_compat.
apply Uplus_le_compat; auto.
Qed.

Hint Immediate Uesp_le_compat Uesp_eq_compat.


Lemma Uesp_le_left : forall x y, x & y <= x.
unfold Uesp; intros.
apply Uinv_le_perm_left; auto.
Qed.

Lemma Uesp_le_right : forall x y, x & y <= y.
unfold Uesp; intros.
apply Uinv_le_perm_left; auto.
Qed.

Hint Resolve Uesp_le_left Uesp_le_right.

Lemma Uesp_plus_inv : forall x y, [1-] y <= x -> x == x & y + [1-] y.
unfold Uesp; intros.
rewrite Uinv_plus_right; auto.
Qed.
Hint Resolve Uesp_plus_inv.

Lemma Uesp_le_plus_inv : forall x y, x <= x & y + [1-] y.
intros; apply (Ule_total ([1-]y) x); intros; auto.
rewrite Uesp_zero; auto.
rewrite Uplus_zero_left; auto.
Qed.
Hint Resolve Uesp_le_plus_inv.

Lemma Uplus_inv_le_esp : forall x y z, x <= y + ([1-] z) -> x & z <= y.
intros; unfold Uesp.
apply Uinv_le_perm_left.
apply Ule_trans with ([1-](y+[1-]z) + [1-]z); auto.
Qed.
Hint Immediate Uplus_inv_le_esp.

(** ** Definition and properties of $x - y$ *)

Definition Uminus (x y:U) := [1-] ([1-] x + y).

Infix "-" := Uminus : U_scope.

Lemma Uminus_le_compat_left : forall x y z, x <= y -> x - z <= y - z.
unfold Uminus; auto.
Qed.

Lemma Uminus_le_compat_right :  forall x y z, y <= z -> x - z <= x - y.
unfold Uminus; auto.
Qed.

Hint Resolve Uminus_le_compat_left Uminus_le_compat_right.

Lemma Uminus_le_compat : forall x y z t, x <= y ->  t <= z -> x - z <= y - t.
intros; apply Ule_trans with (x-t); auto.
Qed.

Hint Immediate Uminus_le_compat.

Add Morphism Uminus with signature Ueq ==> Ueq ==> Ueq as Uminus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ule_antisym;
apply Ule_trans with (x1-x4); auto.
Qed.
Hint Immediate Uminus_eq_compat.

Lemma Uminus_zero_right : forall x, x - 0 == x.
unfold Uminus; intros.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Qed.

Lemma Uminus_one_left : forall x, 1 - x == [1-] x.
unfold Uminus; intros.
setoid_rewrite Uinv_one; auto.
Qed.

Lemma Uminus_le_zero : forall x y, x <= y -> x - y == 0.
unfold Uminus; intros.
setoid_rewrite <- Uinv_one.
apply Uinv_eq_compat.
apply Ule_antisym; auto.
apply Ule_trans with ([1-] y + y); auto.
Qed.

Hint Resolve Uminus_zero_right Uminus_one_left Uminus_le_zero.

Lemma Uminus_eq : forall x, x-x == 0.
auto.
Qed.
Hint Resolve Uminus_eq.

Lemma Uminus_le_left : forall x y, x - y <= x.
unfold Uminus; auto.
Qed.

Hint Resolve Uminus_le_left.


Lemma Uminus_le_inv : forall x y, x - y <= [1-]y.
intros.
unfold Uminus.
apply Uinv_le_compat; auto.
Qed.
Hint Resolve Uminus_le_inv.

Lemma Uminus_plus_simpl : forall x y, y <= x -> (x - y) + y == x.
unfold Uminus; intros.
assert (H1:y <= [1-] ([1-] x)); auto.
setoid_rewrite (Uinv_plus_right H1); auto.
Qed.

Lemma Uminus_plus_zero : forall x y, x <= y -> (x - y) + y == y.
intros; setoid_rewrite (Uminus_le_zero H); auto.
Qed.

Hint Resolve Uminus_plus_simpl Uminus_plus_zero.


Lemma Uesp_minus_distr_left : forall x y z, (x & y) - z  == (x - z) & y.
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv (([1-] x) + z)).
repeat norm_assoc_right; auto.
Qed.

Lemma Uesp_minus_distr_right : forall x y z, (x & y) - z  == x & (y - z).
intros; setoid_rewrite (Uesp_sym x y); 
setoid_rewrite (Uesp_sym x (y - z)); 
apply Uesp_minus_distr_left.
Qed.

Hint Resolve Uesp_minus_distr_left Uesp_minus_distr_right.

Lemma Uesp_minus_distr : forall x y z t, (x & y) - (z + t) == (x - z) & (y - t).
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv ([1-] x + z)).
setoid_rewrite (Uinv_inv ([1-] y + t)).
repeat norm_assoc_right; auto.
Qed.
Hint Resolve Uesp_minus_distr.
 
Lemma Uminus_esp_simpl_left : forall x y, [1-]x <= y -> x - (x & y) == [1-]y.
unfold Uesp,Uminus; intros.
apply Uinv_eq_compat.
rewrite (Uplus_sym ([1-]x)).
rewrite Uinv_plus_left; auto.
Qed.

Lemma Uplus_esp_simpl : forall x y, (x - (x & y))+y == x+y.
intros; apply (Ule_total ([1-]x) y); auto; intros.
rewrite Uminus_esp_simpl_left; auto.
rewrite (@Uplus_one x y); auto.
rewrite (@Uesp_zero x y); auto.
Qed.
Hint Resolve Uminus_esp_simpl_left Uplus_esp_simpl.

Lemma Uminus_esp_le_inv  : forall x y, x - (x & y) <= [1-]y.
intros; apply (Ule_total ([1-]x) y); auto; intros.
rewrite (@Uesp_zero x y); auto.
rewrite Uminus_zero_right; auto.
Qed.

Hint Resolve Uminus_esp_le_inv.

Lemma Uplus_esp_inv_simpl : forall x y, x <= [1-]y -> (x + y) & [1-]y == x.
unfold Uesp; intros.
apply Uinv_eq_perm_left.
rewrite Uinv_inv; auto.
Qed.
Hint Resolve Uplus_esp_inv_simpl.

Lemma Uplus_inv_esp_simpl : forall x y, x <= y -> (x + [1-]y) & y == x.
intros.
apply Ueq_trans with ((x + [1-] y) & [1-][1-]y); auto.
rewrite Uinv_inv; auto.
Qed.
Hint Resolve Uplus_inv_esp_simpl.


(** ** Definition and properties of max *)

Definition max (x y : U) : U := (x - y) + y.

Lemma max_eq_right : forall x y : U, y <= x -> max x y == x.
unfold max; auto.
Qed.

Lemma max_eq_left : forall x y : U, x <= y -> max x y == y.
unfold max; auto.
Qed.

Hint Resolve max_eq_right max_eq_left.

Lemma max_eq_case : forall x y : U, orc (max x y == x) (max x y == y).
intros; apply (Ule_total x y); auto.
Qed.

Add Morphism max with signature Ueq ==> Ueq ==> Ueq as max_eq_compat.
unfold max; intros.
apply Uplus_eq_compat; auto.
Qed.

Lemma max_le_right : forall x y : U, x <= max x y.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_left; auto.
rewrite max_eq_right; auto.
Qed.

Lemma max_le_left : forall x y : U, y <= max x y.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_left; auto.
rewrite max_eq_right; auto.
Qed.

Hint Resolve max_le_right max_le_left.

Lemma max_le : forall x y z : U, x <= z -> y <= z -> max x y <= z.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_left; auto.
rewrite max_eq_right; auto.
Qed.

(** ** Definition and properties of min *)

Definition min (x y : U) : U := [1-] ((y - x) + [1-]y).

Lemma min_eq_right : forall x y : U, x <= y -> min x y == x.
unfold min, Uminus; intros.
apply Uinv_eq_perm_left; auto.
Qed.

Lemma min_eq_left : forall x y : U, y <= x -> min x y== y.
unfold min; intros.
rewrite Uminus_le_zero; auto.
Qed.

Hint Resolve min_eq_right min_eq_left.

Lemma min_eq_case : forall x y : U, orc (min x y == x) (min x y == y).
intros; apply (Ule_total x y); auto.
Qed.

Add Morphism min with signature Ueq ==> Ueq ==> Ueq as min_eq_compat.
unfold min; intros.
apply Uinv_eq_compat; auto.
apply Uplus_eq_compat; auto.
Qed.

Lemma min_le_right : forall x y : U, min x y <=x.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto.
Qed.

Lemma min_le_left : forall x y : U, min x y <= y.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
Qed.

Hint Resolve min_le_right min_le_left.

Lemma min_le : forall x y z : U, z <= x -> z <= y -> z <= min x y.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
rewrite min_eq_left; auto.
Qed.

Lemma Uinv_min_max : forall x y, [1-](min x y)==max ([1-]x) ([1-]y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite max_eq_right; auto.
rewrite min_eq_left; auto; rewrite max_eq_left; auto.
Qed.

Lemma Uinv_max_min : forall x y, [1-](max x y)==min ([1-]x) ([1-]y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto; rewrite max_eq_left; auto.
rewrite min_eq_right; auto; rewrite max_eq_right; auto.
Qed.

Lemma min_mult : forall x y k, 
    min (k * x) (k * y) == k * (min x y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite min_eq_right; auto.
rewrite min_eq_left; auto; rewrite min_eq_left; auto.
Qed.
Hint Resolve min_mult.

Lemma min_plus : forall x1 x2 y1 y2, 
    (min x1 x2)  + (min y1 y2) <= min (x1+y1) (x2+y2).
intros; apply min_le; auto.
Qed.
Hint Resolve min_plus.

Lemma min_plus_cte : forall x y k, min (x + k) (y + k) == (min x y) + k.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite min_eq_right; auto.
rewrite min_eq_left; auto; rewrite min_eq_left; auto.
Qed.
Hint Resolve min_plus_cte.

Lemma min_le_compat : forall x1 x2 y1 y2, 
      x1<=y1 -> x2 <=y2 -> min x1 x2 <= min y1 y2.
intros; apply min_le.
apply Ule_trans with x1; auto.
apply Ule_trans with x2; auto.
Qed.

Lemma min_sym : forall x y, min x y == min y x.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
rewrite min_eq_left; auto.
rewrite min_eq_left; auto.
rewrite min_eq_right; auto.
Qed.
Hint Resolve min_sym.


Definition incr (f:nat->U) := forall n, f n <= f (S n).

Lemma incr_mon : forall f, incr f -> forall n m, (n<=m)%nat -> f n <= f m.
induction 2; auto.
apply Ule_trans with (f m); auto.
Qed.
Hint Resolve incr_mon.

Lemma incr_decomp_aux : forall f g, incr f -> incr g -> 
     forall n1 n2, (forall m, ~ ((n1<=m)%nat /\ f n1 <= g m))
           -> (forall m, ~((n2<=m)%nat /\ g n2<= f m)) -> (n1<=n2)%nat -> False.
intros; assert (absurd:~ g n2 < g n2); auto.
assert (~(f n1 <= g n2)).
apply not_and_elim_left with (1:= H1 n2); auto.
assert (~(g n2 <= f n2)); auto.
apply not_and_elim_left with (1:= H2 n2); auto.
apply absurd; apply Ult_le_trans with (f n1); auto.
apply Ule_trans with (f n2); auto.
Qed.

Lemma incr_decomp : forall f g, incr f -> incr g -> 
     orc (forall n, exc (fun m => (n<=m)%nat /\ f n <= g m)) 
           (forall n, exc (fun m => (n<=m)%nat /\ g n <= f m)).
intros f g incrf incrg; apply orc_intro; intros.
apply H; clear H; intros.
apply exc_intro_class; intros.
apply H0; clear H0; intros.
apply exc_intro_class; intros.
case (dec_le n n0); intro.
apply (incr_decomp_aux incrf incrg) with (n1:=n) (n2:=n0); auto.
apply (incr_decomp_aux incrg incrf) with (n1:=n0) (n2:=n); auto; omega.
Qed.



(** ** Other properties *)
Lemma Uplus_minus_simpl_right : forall x y, y <= [1-] x -> (x + y) - y == x.
unfold Uminus; intros.
setoid_rewrite (Uinv_plus_right H); auto.
Qed.
Hint Resolve Uplus_minus_simpl_right.

Lemma Uplus_minus_simpl_left : forall x y, y <= [1-] x -> (x + y) - x == y.
intros; setoid_rewrite (Uplus_sym x y); auto.
Qed.

Lemma Uminus_assoc_left : forall x y z, (x - y) - z == x - (y + z).
unfold Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
Qed.

Hint Resolve Uminus_assoc_left.

Lemma Uminus_perm : forall x y z, (x - y) - z == (x - z) - y.
intros; rewrite Uminus_assoc_left.
rewrite (Uplus_sym y z); auto.
Qed.
Hint Resolve Uminus_perm.

Lemma Uminus_le_perm_left : forall x y z, y <= x -> x - y <= z -> x <= z + y.
intros; setoid_rewrite <- (Uminus_plus_simpl H); auto.
Qed.

Lemma Uplus_le_perm_left : forall x y z, y <= x -> x <= y + z  -> x - y <= z.
intros; apply Uplus_le_simpl_left with y.
unfold Uminus; setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
setoid_rewrite (Uplus_sym y (x-y)); setoid_rewrite (Uminus_plus_simpl H); auto.
Qed.

Lemma Uminus_eq_perm_left : forall x y z, y <= x -> x - y == z -> x == z + y.
intros; setoid_rewrite <- (Uminus_plus_simpl H); auto.
Qed.

Lemma Uplus_eq_perm_left : forall x y z, y <= [1-] z -> x == y + z  -> x - y == z.
intros; setoid_rewrite H0; auto.
setoid_rewrite (Uplus_sym y z); auto.
Qed.

Hint Resolve Uminus_le_perm_left Uminus_eq_perm_left.
Hint Resolve Uplus_le_perm_left Uplus_eq_perm_left.

Lemma Uminus_le_perm_right : forall x y z, z <= y -> x <= y - z -> x + z <= y.
intros; setoid_rewrite <- (Uminus_plus_simpl H); auto.
Qed.

Lemma Uplus_le_perm_right : forall x y z, z <= [1-] x -> x + z <= y  -> x <= y - z.
intros; apply Uplus_le_simpl_right with z; auto.
Qed.
Hint Resolve Uminus_le_perm_right Uplus_le_perm_right.

Lemma Uminus_le_perm : forall x y z, z <= y -> x <= [1-] z -> x <= y - z -> z <= y - x.
intros; apply Uplus_le_perm_right; auto.
setoid_rewrite (Uplus_sym z x); auto.
Qed.
Hint Resolve Uminus_le_perm.

Lemma Uminus_eq_perm_right : forall x y z, z <= y -> x == y - z -> x + z == y.
intros; apply Ueq_trans with (y - z + z); auto.
Qed.
Hint Resolve Uminus_eq_perm_right.

Lemma Uminus_plus_perm : forall x y z, y <= x -> z <= [1-]x -> x - y + z == x + z - y.
intros; apply Uminus_eq_perm_right.
apply Ule_trans with (y + z - y); auto.
rewrite Uplus_minus_simpl_left; auto.
apply Ule_trans with ([1-]x); auto.
rewrite Uminus_perm.
rewrite Uplus_minus_simpl_right; auto.
Qed.

Lemma Uminus_zero_le : forall x y, x - y == 0 -> x <= y.
intros x y; unfold Uminus; intros.
setoid_rewrite <- (Uinv_inv x).
apply Uplus_one_le.
setoid_rewrite <- Uinv_zero; auto.
setoid_rewrite <- H; auto.
setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
Qed.

Lemma Uminus_lt_non_zero : forall x y, x < y -> ~(0 == y - x).
red; intros.
apply H; auto.
apply Uminus_zero_le; auto.
Qed.
Hint Immediate Uminus_zero_le Uminus_lt_non_zero.

Lemma Ult_le_nth : forall x y, x < y -> exc (fun n => x <= y - [1/]1+n).
intros; apply (archimedian (x:=(y - x))); intros; auto.
apply exc_intro with x0.
apply Uminus_le_perm; auto.
apply Ule_trans with (y - x); auto. 
Qed.

Lemma Uminus_distr_left : forall x y z, (x - y) * z == (x * z) - (y * z).
intros; apply (Ule_total x y); intros; auto.
(* first case x <= y, left and right hand side equal 0 *)
setoid_rewrite (Uminus_le_zero H).
setoid_rewrite (Umult_zero_left z).
assert (x * z <= y * z); auto.
setoid_rewrite (Uminus_le_zero H0); auto.
(* second case y <= x, use simplification *)
unfold Uminus; intros; auto.
apply Uplus_eq_simpl_right with (y * z); auto.
assert ([1-] ([1-] x + y) <= [1-] y); auto.
setoid_rewrite <- (Udistr_plus_right z H0); auto.
assert (y <= [1-] ([1-] x)); auto.
setoid_rewrite (Uinv_plus_right H1).
setoid_rewrite (Uinv_inv x); auto.
Qed.

Hint Resolve Uminus_distr_left.

Lemma Uminus_distr_right : forall x y z,  x * (y - z) == (x * y) - (x * z).
intros; setoid_rewrite (Umult_sym x y).
setoid_rewrite (Umult_sym x z).
setoid_rewrite (Umult_sym x (y - z)); auto.
Qed.

Hint Resolve Uminus_distr_right.


Lemma Uminus_assoc_right :  forall x y z, y <= x -> z <= y -> x - (y - z) == (x - y) + z.
intros.
apply Uplus_eq_perm_left; auto.
unfold Uminus at 1; apply Uinv_le_compat.
apply Ule_trans with (1 - y + z); auto.
apply Ueq_trans with ((y - z) + z + (x - y)).
setoid_rewrite (Uminus_plus_simpl H0).
setoid_rewrite (Uplus_sym y (x - y)); auto.
norm_assoc_right; auto.
Qed.

Lemma Uplus_minus_assoc_right : forall x y z, y <= [1-]x -> z <= y -> x + (y - z) == (x + y) - z.
intros; unfold Uminus.
apply Ueq_trans with ([1-] (x + ([1-] (x + y) + z)) + x).
rewrite Uplus_assoc.
rewrite (Uplus_sym x ([1-] (x + y))).
rewrite Uinv_plus_left; auto.
rewrite Uinv_plus_left; auto.
apply Ule_trans with ([1-] (x + y) + y); auto.
Qed.

(** ** Definition and properties of generalized sums *)

Definition sigma (alpha : nat -> U) (n:nat) := comp Uplus 0 alpha n.

Lemma sigma_0 : forall (f : nat -> U), sigma f 0 == 0.
trivial.
Qed.

Lemma sigma_S : forall (f :nat -> U) (n:nat), sigma f (S n) = (f n) + (sigma f n).
trivial.
Qed.

Lemma sigma_1 : forall (f : nat -> U), sigma f (S 0) == f O.
intros; rewrite sigma_S; auto.
Qed.

Lemma sigma_S_lift : forall (f :nat -> U) (n:nat), 
          sigma f (S n) == (f O) + (sigma (fun k => f (S k)) n).
intros f n; generalize f; induction n; simpl; intros; auto.
rewrite sigma_S.
rewrite IHn.
rewrite sigma_S.
rewrite Uplus_assoc.
rewrite (Uplus_sym (f0 (S n)) (f0 O)); auto.
Qed.

Lemma sigma_incr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> (sigma f n) <= (sigma f m).
intros f n m H; induction H; auto.
intros; rewrite sigma_S.
apply Ule_trans with (1:=IHle); auto.
Qed.

Hint Resolve sigma_incr.

Lemma sigma_eq_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k == g k) -> (sigma f n) == (sigma g n).
induction n; auto.
intros; repeat rewrite sigma_S.
apply Ueq_trans with (g n + sigma f n); auto with arith.
Qed.

Lemma sigma_le_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k <= g k) -> (sigma f n) <= (sigma g n).
induction n; auto.
intros; repeat rewrite sigma_S.
apply Ule_trans with (g n + sigma f n); auto with arith.
Qed.

Lemma sigma_zero : forall f n, (forall k, (k<n)%nat -> f k ==0)->(sigma f n)==0.
induction n; simpl; intros; auto.
rewrite sigma_S.
rewrite (H n); auto.
rewrite IHn; auto.
Qed.

Lemma sigma_not_zero : forall f n k, (k<n)%nat -> 0 < f k -> 0 < sigma f n.
induction n; simpl; intros; auto.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
apply Ult_le_trans with (sigma f n); auto.
apply (IHn k); auto.
apply Ult_le_trans with (f n); auto.
Qed.

Lemma sigma_zero_elim : forall f n, (sigma f n)==0->forall k, (k<n)%nat -> f k ==0.
intros; apply Ueq_class; red; intros.
assert (0 < sigma f n); auto.
apply sigma_not_zero with k; auto.
Qed.

Hint Resolve sigma_eq_compat sigma_le_compat sigma_zero.

Lemma sigma_le : forall f n k, (k<n)%nat -> f k <= sigma f n.
induction n; simpl; intros.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
apply Ule_trans with (sigma f n); auto.
Qed.

Lemma sigma_minus_decr : forall f n, (forall k, f (S k) <= f k) ->
         sigma (fun k => f k - f (S k)) n == f O - f n.
intros f n fmon;induction n; simpl.
rewrite sigma_0; auto.
rewrite sigma_S; rewrite IHn.
rewrite Uplus_sym.
rewrite Uplus_minus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
elim n; intros; auto.
apply Ule_trans with (f n0); auto.
Qed.

Lemma sigma_minus_incr : forall f n, (forall k, f k <= f (S k)) ->
         sigma (fun k => f (S k) - f k) n == f n - f O.
intros f n fmon;induction n; simpl.
rewrite sigma_0; auto.
rewrite sigma_S; rewrite IHn.
rewrite Uplus_minus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
elim n; intros; auto.
apply Ule_trans with (f n0); auto.
Qed.

Definition sigma_inf (f : nat -> U) : U := lub (sigma f).

(** ** Definition and properties of generalized products *)

Definition prod (alpha : nat -> U) (n:nat) := comp Umult 1 alpha n.

Lemma prod_0 : forall (f : nat -> U), prod f 0 = 1.
trivial.
Qed.

Lemma prod_S : forall (f :nat -> U) (n:nat), prod f (S n) = (f n) * (prod f n).
trivial.
Qed.

Lemma prod_1 : forall (f : nat -> U), prod f (S 0) == f O.
intros; rewrite prod_S; auto.
Qed.

Lemma prod_S_lift : forall (f :nat -> U) (n:nat), 
          prod f (S n) == (f O) * (prod (fun k => f (S k)) n).
intros f n; generalize f; induction n; simpl; intros; auto.
rewrite prod_S.
rewrite IHn.
rewrite prod_S.
rewrite Umult_assoc.
rewrite (Umult_sym (f0 (S n)) (f0 O)); auto.
Qed.

Lemma prod_decr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> (prod f m) <= (prod f n).
intros f n m H; induction H; auto.
intros; rewrite prod_S.
apply Ule_trans with (2:=IHle); auto.
Qed.

Hint Resolve prod_decr.

Lemma prod_eq_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k == g k) -> (prod f n) == (prod g n).
induction n; auto.
intros; repeat rewrite prod_S.
apply Ueq_trans with (g n * prod f n); auto with arith.
Qed.

Lemma prod_le_compat : forall (f g: nat -> U) (n:nat), 
 (forall k, (k < n)%nat -> f k <= g k) -> prod f n <= prod g n.
induction n; auto.
intros; repeat rewrite prod_S.
apply Ule_trans with (g n * prod f n); auto with arith.
Qed.

Lemma prod_zero : forall f n k, (k<n)%nat -> f k ==0 -> prod f n==0.
induction n; simpl; intros; auto.
absurd ((k < 0)%nat); auto with arith.
rewrite prod_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
rewrite (IHn k); auto.
rewrite H0; auto.
Qed.

Lemma prod_not_zero : forall f n, (forall k, (k<n)%nat -> 0 < f k )-> 0 < prod f n.
induction n; simpl; intros; auto.
rewrite prod_S; auto with arith.
Qed.

Lemma prod_zero_elim : forall f n, prod f n==0 -> exc (fun k => (k<n)%nat /\ f k ==0).
intros; apply class_exc; red; intros.
assert (forall k, (k<n)%nat -> 0 < f k); intros.
red; intro.
apply H0.
apply exc_intro with k; auto.
absurd (0 < prod f n); auto.
apply prod_not_zero; auto.
Qed.

Hint Resolve prod_eq_compat prod_le_compat prod_not_zero.

Lemma prod_le : forall f n k, (k<n)%nat -> prod f n <= f k.
induction n; simpl; intros.
casetype False; omega.
rewrite prod_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
apply Ule_trans with (prod f n); auto.
Qed.

Lemma prod_minus : forall f n, prod f n - prod f (S n) == ([1-]f n)  * prod f n.
intros f n; rewrite prod_S.
apply Ueq_trans with (1 * prod f n - f n * prod f n).
rewrite Umult_one_left; auto.
rewrite <- Uminus_distr_left; auto.
Qed.


(** ** Properties of [Unth] *)
Lemma Unth_zero : [1/]1+0 == 1.
setoid_rewrite (Unth_prop 0); auto.
Qed.

Notation "[1/2]" := (Unth 1).

Lemma Unth_one : [1/2] == [1-] [1/2].
apply Ueq_trans with (1:=Unth_prop 1); simpl; auto.
Qed.

Hint Resolve Unth_zero Unth_one.

Lemma Unth_one_plus : [1/2] + [1/2] == 1.
apply Ueq_trans with  ([1/2] + [1-][1/2]); auto.
Qed.
Hint Resolve Unth_one_plus.

Lemma Unth_not_null : forall n, ~ (0 == [1/]1+n).
red; intros.
apply Udiff_0_1.
apply Ueq_trans with ([1/]1+n); auto.
apply Ueq_trans with ([1-] (sigma (fun k => [1/]1+n) n)).
apply (Unth_prop n).
apply Ueq_trans with ([1-] (sigma (fun k => 0) n)).
apply Uinv_eq_compat.
apply sigma_eq_compat; auto.
apply Ueq_trans with ([1-] 0); auto.
Qed.
Hint Resolve Unth_not_null.

Lemma Unth_lt_zero : forall n, 0 < [1/]1+n.
auto.
Qed.
Hint Resolve Unth_lt_zero.

Lemma Unth_inv_lt_one : forall n, [1-][1/]1+n<1.
intro; setoid_replace 1 with ([1-]0); auto.
Qed.
Hint Resolve Unth_inv_lt_one.

Lemma Unth_not_one : forall n, ~ (1 == [1-][1/]1+n).
auto.
Qed.
Hint Resolve Unth_not_one.

Lemma Unth_prop_sigma : forall n, [1/]1+n == [1-] (sigma (fun k => [1/]1+n) n).
exact Unth_prop.
Qed.
Hint Resolve Unth_prop_sigma.

Lemma Unth_sigma_n : forall n : nat, ~ (1 == sigma (fun k => [1/]1+n) n).
intros; apply Uinv_neq_simpl.
setoid_rewrite Uinv_one.
setoid_rewrite <- (Unth_prop_sigma n); auto.
Qed.

Lemma Unth_sigma_Sn : forall n : nat, 1 == sigma (fun k => [1/]1+n) (S n).
intros; rewrite sigma_S.
apply Ueq_trans with 
([1-] (sigma (fun k => [1/]1+n) n) + (sigma (fun k => [1/]1+n) n));auto.
Qed.

Hint Resolve Unth_sigma_n Unth_sigma_Sn.


Lemma Unth_decr : forall n, [1/]1+(S n) < [1/]1+n.
repeat red; intros.
apply (Unth_sigma_n (S n)).
apply Ule_antisym; auto.
apply Ule_trans with (sigma (fun _ : nat => [1/]1+n) (S n)); auto.
Qed.
Hint Resolve Unth_decr.

Lemma Unth_anti_mon : 
forall n m, (n <= m)%nat -> [1/]1+m <= [1/]1+n.
induction 1; auto.
apply Ule_trans with ([1/]1+m); auto.
Qed.
Hint Resolve Unth_anti_mon.

Lemma Unth_le_half : forall n, [1/]1+(S n) <= [1/2].
auto with arith.
Qed.
Hint Resolve Unth_le_half.

(** *** Mean of two numbers : $\frac{1}{2}x+\frac{1}{2}y$*)
Definition mean (x y:U) := [1/2] * x + [1/2] * y.

Lemma mean_eq : forall x:U, mean x x ==x.
unfold mean; intros.
assert (H : ([1/2] <= [1-] ([1/2]))); auto.
setoid_rewrite <- (Udistr_plus_right x H); auto.
setoid_rewrite Unth_one_plus; auto.
Qed.

Lemma mean_le_compat_right : forall x y z, y <= z -> mean x y <= mean x z.
unfold mean; intros.
apply Uplus_le_compat_right; auto.
Qed.

Lemma mean_le_compat_left : forall x y z, x <= y -> mean x z <= mean y z.
unfold mean; intros.
apply Uplus_le_compat_left; auto.
Qed.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.

Lemma mean_lt_compat_right : forall x y z, y < z -> mean x y < mean x z.
unfold mean; intros.
apply Uplus_lt_compat_right; auto.
Qed.

Lemma mean_lt_compat_left : forall x y z, x < y -> mean x z < mean y z.
unfold mean; intros.
apply Uplus_lt_compat_left; auto.
Qed.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.
Hint Resolve mean_lt_compat_left mean_lt_compat_right.

Lemma mean_le_up : forall x y, x <= y -> mean x y <= y.
intros; apply Ule_trans with (mean y y); auto. 
Qed.

Lemma mean_le_down : forall x y, x <= y -> x <= mean x y.
intros; apply Ule_trans with (mean x x); auto. 
Qed.

Lemma mean_lt_up : forall x y, x < y -> mean x y < y.
intros; apply Ult_le_trans with (mean y y); auto. 
Qed.

Lemma mean_lt_down : forall x y, x < y -> x < mean x y.
intros; apply Ule_lt_trans with (mean x x); auto. 
Qed.

Hint Resolve mean_le_up mean_le_down mean_lt_up mean_lt_down.

(** *** Properties of $\frac{1}{2}$ *)

Lemma le_half_inv : forall x, x <= [1/2] -> x <= [1-] x.
intros; apply Ule_trans with ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Qed.

Hint Immediate le_half_inv.

Lemma ge_half_inv : forall x, [1/2] <= x  -> [1-] x <= x.
intros; apply Ule_trans with ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Qed.

Hint Immediate ge_half_inv.

Lemma Uinv_le_half_left : forall x, x <= [1/2] -> [1/2] <= [1-] x.
intros; setoid_rewrite Unth_one; auto.
Qed.

Lemma Uinv_le_half_right : forall x, [1/2] <= x -> [1-] x <= [1/2].
intros; setoid_rewrite Unth_one; auto.
Qed.

Hint Resolve Uinv_le_half_left Uinv_le_half_right.

Lemma half_twice : forall x,  (x <= [1/2]) -> ([1/2]) * (x + x) == x.
intros; assert (H1 : x <= [1-] x); auto. 
setoid_rewrite (Udistr_plus_left ([1/2]) H1).
exact (mean_eq x).
Qed.

Lemma half_twice_le : forall x, ([1/2]) * (x + x) <= x.
intros; apply (Ule_total x ([1/2])); intros; auto.
setoid_rewrite (half_twice H); trivial.
assert (x+x==1); auto.
setoid_rewrite H0.
setoid_rewrite (Umult_one_right ([1/2])); auto.
Qed.

Lemma Uinv_half : forall x, ([1/2]) * ([1-] x)  + ([1/2]) == [1-] (([1/2]) * x).
intros; setoid_rewrite (Udistr_inv_left ([1/2]) x).
setoid_rewrite Unth_one; auto.
Qed.

Lemma half_esp : 
forall x, ([1/2] <= x) -> ([1/2]) * (x & x) + [1/2] == x.
intros; unfold Uesp.
setoid_rewrite (Uinv_half ([1-] x + [1-] x)).
assert (H1:[1-] x <= [1/2]).
setoid_rewrite Unth_one; auto.
setoid_rewrite (half_twice H1); auto.
Qed.

Lemma half_esp_le : forall x, x <= ([1/2]) * (x & x) + [1/2].
intros; apply (Ule_total ([1/2]) x); intros; auto.
setoid_rewrite (half_esp H); trivial.
assert (x & x == 0); auto.
setoid_rewrite H0.
setoid_rewrite (Umult_zero_right ([1/2])).
setoid_rewrite (Uplus_zero_left ([1/2])); auto.
Qed.
Hint Resolve half_esp_le.


Lemma half_le : forall x y, y <= [1-] y -> x <= y + y -> ([1/2]) * x <= y.
intros.
apply not_Ult_le; red; intros.
assert (y + y < x); auto.
setoid_replace x with (mean x x); auto.
unfold mean; apply Uplus_lt_compat; auto.
Qed.

Lemma half_Unth: forall n, ([1/2])*([1/]1+n) <= [1/]1+(S n).
intros; apply half_le; auto.
setoid_rewrite (Unth_prop_sigma n).
apply Ule_trans with ([1-] (sigma (fun _ : nat => [1/]1+(S n)) n)).
apply Uinv_le_compat.
apply sigma_le_compat; auto.
apply Ule_trans with 
([1-] (sigma (fun _ : nat => [1/]1+(S n)) (S n)) + [1/]1+(S n)); auto.
rewrite sigma_S.
assert (sigma (fun _ : nat => [1/]1+(S n)) n <= [1-] ([1/]1+(S n))).
apply Ule_trans with (sigma (fun _ : nat => [1/]1+(S n)) (S n)); auto.
setoid_rewrite (Uinv_plus_left H); auto.
Qed.
Hint Resolve half_le half_Unth.

Lemma half_exp : forall n, [1/2]^n == [1/2]^(S n) + [1/2]^(S n).
intros; simpl; apply Ueq_sym; exact (mean_eq ([1/2]^n)).
Qed.

(** ** Density *)
Lemma Ule_lt_lim : forall x y,  (forall t, t < x -> t <= y) -> x <= y.
intros; apply Ule_class; red; intros.
pose (z:= mean y x).
assert (y < z); unfold z; auto.
apply H1; apply H; unfold z; auto.
Qed.

(** ** Properties of least upper bounds *)

Section lubs.

Lemma lub_le_stable : forall f g, (forall n, f n <= g n) -> lub f <= lub g.
intros; apply lub_le; intros.
apply Ule_trans with (g n); auto.
Qed.

Hint Resolve lub_le_stable.

Lemma lub_eq_stable : forall f g, (forall n, f n == g n) -> lub f == lub g.
intros; apply Ule_antisym; auto.
Qed.

Hint Resolve lub_eq_stable.

Lemma lub_zero : (lub (fun n => 0)) == 0.
apply Ule_antisym; auto.
Qed.

Lemma lub_un : (lub (fun n => 1)) == 1.
apply Ule_antisym; auto.
apply le_lub with (f:=fun _ : nat => 1) (n:=O); auto.
Qed.

Lemma lub_cte : forall c:U, (lub (fun n => c)) == c.
intro; apply Ueq_trans with (lub (fun n => c * 1)); auto.
apply Ueq_trans with (c * (lub (fun n => 1))); auto.
setoid_rewrite lub_un; auto.
Qed.

Hint Resolve lub_zero lub_un lub_cte.

Lemma lub_eq_plus_cte_left : forall (f : nat -> U) (k:U), lub (fun n => k + (f n)) == k + (lub f).
intros; apply Ueq_trans with ((lub f)+k); auto.
apply Ueq_trans with (lub (fun n => (f n) + k)); auto.
Qed.
Hint Resolve lub_eq_plus_cte_left.


Lemma min_lub_le : forall f g, 
         lub (fun n => min (f n) (g n)) <= min (lub f) (lub g).
intros; apply min_le.
apply lub_le.
intro; apply Ule_trans with (f n); auto.
apply lub_le.
intro; apply Ule_trans with (g n); auto.
Qed.

Lemma min_lub_le_incr_aux : forall f g, incr f -> 
         (forall n, exc (fun m => (n<=m)%nat /\ f n <= g m)) 
         -> min (lub f) (lub g) <= lub (fun n => min (f n) (g n)).
intros; apply Ule_trans with (lub f); auto.
apply lub_le; intros.
apply (H0 n); auto; intros m (H1,H2).
apply Ule_trans with (min (f m) (g m)); auto.
apply min_le; auto.
apply le_lub with (f:=fun k : nat => min (f k) (g k)) ; auto.
Qed.

Lemma min_lub_le_incr : forall f g, incr f -> incr g -> 
         min (lub f) (lub g) <= lub (fun n => min (f n) (g n)).
intros f g incrf incrg; apply (incr_decomp incrf incrg); auto; intros.
apply (min_lub_le_incr_aux g incrf); auto.
rewrite min_sym.
apply Ule_trans with (lub (fun n : nat => min (g n) (f n))); auto.
apply (min_lub_le_incr_aux f incrg); auto.
Qed.

Lemma lub_eq_esp_right : 
  forall (f : nat -> U) (k : U), lub (fun n : nat => f n & k) == lub f & k.
intros; apply Ule_antisym.
apply lub_le; auto.
apply Uplus_inv_le_esp.
rewrite <- lub_eq_plus_cte_right.
apply lub_le_stable; auto.
Qed.
Hint Resolve lub_eq_esp_right.

(** ** Greatest lower bounds *)

Definition glb (f:nat->U) := [1-]lub (fun n => [1-](f n)).

Definition prod_inf (f : nat -> U) : U := glb (prod f).

Lemma glb_le_stable:
  forall f g : nat -> U, (forall n : nat, f n <= g n) -> glb f <= glb g.
intros; unfold glb; auto.
Qed.
Hint Resolve glb_le_stable.

Lemma glb_eq_stable:
  forall f g : nat -> U, (forall n : nat, f n == g n) -> glb f == glb g.
intros; apply Ule_antisym; auto.
Qed.
Hint Resolve glb_eq_stable.

Lemma glb_cte: forall c : U, glb (fun _ : nat => c) == c.
intros; unfold glb; auto.
Qed.
Hint Resolve glb_cte.

Lemma glb_eq_plus_cte_right:
  forall (f : nat -> U) (k : U), glb (fun n : nat => f n + k) == glb f + k.
unfold glb; intros.
apply Ueq_trans with ([1-] lub (fun n => ([1-]f n) & [1-] k)); auto.
apply Ueq_trans with ([1-] (lub (fun n => [1-]f n) & [1-] k)).
apply Uinv_eq_compat; apply (lub_eq_esp_right (fun n => [1-]f n) ([1-]k)).
rewrite Uinv_esp_plus; auto.
Qed.

Lemma glb_eq_mult:
  forall (k : U) (f : nat -> U), glb (fun n : nat => k * f n) == k * glb f.
unfold glb; intros; auto.
apply Ueq_trans with ([1-] lub (fun n : nat => k * [1-] (f n) + [1-]k)); auto.
apply Ueq_trans with ([1-] (lub (fun n : nat => k * [1-] (f n)) + [1-]k)).
apply Uinv_eq_compat.
apply lub_eq_plus_cte_right with (f:=fun n : nat => k * [1-] f n).
rewrite (lub_eq_mult k (fun n : nat =>  [1-] f n)).
apply Uinv_eq_perm_left; auto.
rewrite Udistr_inv_left; auto.
Qed.

Lemma glb_le:   forall (f : nat -> U) (n : nat), glb f <= (f n).
unfold glb; intros; apply Uinv_le_perm_left.
apply le_lub with (f:=fun n => [1-]f n); auto.
Qed.

Lemma le_glb: forall (f : nat -> U) (x:U), (forall n : nat, x <= f n)-> x <= glb f.
unfold glb; intros; apply Uinv_le_perm_right.
apply lub_le with (f:=fun n => [1-]f n); auto.
Qed.
Hint Resolve glb_le.

(*
min_lub_le_incr:
  forall f g : nat -> U,
  incr f ->
  incr g -> min (lub f) (lub g) <= lub (fun n : nat => min (f n) (g n))
min_lub_le_incr_aux:
  forall f g : nat -> U,
  incr f ->
  (forall n : nat, exc (fun m : nat => (n <= m)%nat /\ f n <= g m)) ->
  min (lub f) (lub g) <= lub (fun n : nat => min (f n) (g n))
min_lub_le:
  forall f g : nat -> U,
  lub (fun n : nat => min (f n) (g n)) <= min (lub f) (lub g)
*)
Lemma glb_le_esp :  forall f g, (glb f) & (glb g) <= glb (fun n => (f n) & (g n)).
intros; apply le_glb; auto.
Qed.
Hint Resolve glb_le_esp.

Lemma Uesp_min : forall a1 a2 b1 b2, min a1 b1 & min a2 b2 <= min (a1 & a2) (b1 & b2).
intros; apply min_le.
apply Uesp_le_compat; auto.
apply Uesp_le_compat; auto.
Qed.

Lemma mon_seq_Succ : forall f : nat -> U, (forall n, f n <= f (S n)) -> mon_seq Ule f.
red; intros.
elim H0; auto.
Qed.
Hint Immediate mon_seq_Succ.

Variables f g : nat -> U.

Hypothesis monf : forall n, f n <= f (S n).
Hypothesis mong : forall n, g n <= g (S n).

Lemma mon_seqf : mon_seq Ule f.
auto.
Qed.

Lemma mon_seqg : mon_seq Ule g.
auto.
Qed.

Hint Resolve mon_seqf mon_seqg.

Lemma lub_lift : forall n,  (lub f) == (lub (fun k => f (n+k)%nat)).
intro; apply Ule_antisym; auto.
apply lub_le_stable; auto with arith.
Qed.

Hint Resolve lub_lift.

Let sum := fun n => f n + g n.

Lemma mon_sum : mon_seq Ule sum.
unfold mon_seq,sum in *; intros; apply Uplus_le_compat; auto.
Qed.

Hint Resolve mon_sum.

Lemma lub_eq_plus : lub (fun n => (f n) + (g n)) == (lub f) + (lub g).
apply Ule_antisym.
apply lub_le; auto.
apply Ule_trans with (lub (fun n => lub f + g n)); auto.
apply lub_le; intros.
apply Ule_trans with (lub (fun m => f (n+m)) + g n); auto.
setoid_rewrite <- (lub_eq_plus_cte_right (fun m : nat => f (n + m)) (g n)).
apply lub_le; intros.
apply Ule_trans with (f (n + n0) + g (n + n0)); auto with arith.
apply le_lub with (f:=fun n : nat => f n + g n) (n:=(n+n0)%nat).
Qed.
Hint Resolve lub_eq_plus.




Variables k : U.
Let prod := fun n => k * f n.

Lemma mon_prod : mon_seq Ule prod.
unfold mon_seq,prod in *; intros.
apply Umult_le_compat_right; auto.
Qed.

Let inv:= fun n => [1-] (g n).

Lemma lub_inv : (forall n, f n <= inv n) -> lub f <= [1-] (lub g).
unfold inv; intros.
apply Uinv_le_perm_right.
apply lub_le; intros.
apply Uinv_le_perm_right.
apply Ule_trans with (lub (fun k => f (n+k)%nat)); auto.
apply lub_le; intros.
apply Ule_trans with ([1-] (g (n+n0))); auto with arith.
Qed.

Variable h : nat -> U.
Hypothesis dech : forall n, h (S n) <= h n.

Lemma dec_sech : forall n m, (n <= m)%nat -> h m <= h n.
induction 1; auto.
apply Ule_trans with (h m); auto.
Qed.
Hint Resolve dec_sech.

Lemma glb_lift : forall n,  (glb h) == (glb (fun k => h (n+k)%nat)).
intro; apply Ule_antisym.
apply le_glb; auto.
apply glb_le_stable; auto with arith.
Qed.

Hint Resolve glb_lift.

Lemma lub_glb_le : (forall n, f n <= h n) -> lub f <= glb h.
intros; apply lub_le; intros.
apply Ule_trans with (glb (fun k => h (n+k)%nat)); auto.
apply le_glb; intros.
apply Ule_trans with (f (n+n0)); auto with arith.
Qed.

End lubs.

Lemma double_lub_simpl : forall h : nat -> nat -> U,
     (forall n m, h n m <= h (S n) m) ->  (forall n m, h n m <= h n (S m)) 
     -> lub (fun n => lub (h n)) == lub (fun n => h n n). 
intros; apply Ule_antisym.
apply lub_le; intros.
rewrite (lub_lift (h n) (H0 n) n); intros.
apply lub_le; intros.
apply Ule_trans with (h (n + n0)%nat (n+n0)%nat); auto.
apply (@mon_seq_Succ (fun p => h p (n+n0)%nat) (fun p => H p (n+n0)%nat)); auto with arith.
apply le_lub with (f:=fun p => h p p) (n:=(n + n0)%nat).
apply lub_le; intros.
apply Ule_trans with (lub (h n)); auto.
apply le_lub with (f:=fun n0 : nat => lub (h n0)) (n:=n).
Qed.

Lemma double_lub_exch_le : forall h : nat -> nat -> U,
 lub (fun n => lub (fun m => h n m)) <= lub (fun m => lub (fun n => h n m)).
intros; apply lub_le; intros.
apply lub_le; intros.
apply Ule_trans with (lub (fun m : nat => h n m)).
apply (le_lub (fun m => h n m)).
apply lub_le_stable; intros.
apply (le_lub (fun n2 : nat => h n2 n1)).
Qed.
Hint Resolve double_lub_exch_le.

Hint Resolve double_lub_exch_le.

Lemma double_lub_exch : forall h : nat -> nat -> U,
 lub (fun n => lub (fun m => h n m)) == lub (fun m => lub (fun n => h n m)).
intros; apply Ule_antisym; auto.
Qed.

Hint Resolve double_lub_exch.

(** *** Definitions *)
Definition fle (A:Type) (f g:A->U) : Prop := forall x:A, (f x) <=  (g x).
Definition feq (A:Type) (f g:A->U) : Prop := forall x:A, (f x) ==  (g x).
Hint Unfold fle feq.
Definition fplus (A:Type) (f g:A->U) (x:A) : U := (f x) + (g x).
Definition fesp (A:Type) (f g:A->U) (x:A) : U := (f x) & (g x).
Definition fminus (A:Type) (f g:A->U) (x:A) : U := (f x) - (g x).
Definition finv (A:Type) (f:A->U) (x:A) : U := Uinv (f x).
Definition fmult (A:Type) (k:U) (f:A->U) (x:A) : U := k * (f x).
Definition f_one (A:Type) (x : A) : U := U1.
Definition f_zero (A:Type) (x : A) : U := U0.
Definition f_cte (A:Type) (c:U) (x : A) : U := c.
Definition flub (A:Type) (fn:nat->A->U) (x : A) : U := lub (fun n => fn n x).
Definition fglb (A:Type) (fn:nat->A->U) (x : A) : U := glb (fun n => fn n x).
Definition increase (A:Type)(fn : nat -> A -> U) := forall n, fle (fn n) (fn (S n)).
Definition decrease (A:Type)(fn : nat -> A -> U) := forall n, fle (fn (S n)) (fn n).

Implicit Arguments f_one [].
Implicit Arguments f_zero [].
Implicit Arguments f_cte [].

(** *** Elementary properties *)

Lemma feq_refl : forall (A:Type) (f : A->U), feq f f.
auto.
Qed.
Hint Resolve feq_refl.

Lemma feq_sym : forall (A:Type) (f g : A->U), feq f g -> feq g f.
auto.
Qed.

Lemma feq_trans : forall (A:Type) (f g h : A->U), feq f g -> feq g h -> feq f h.
unfold feq; intros; apply Ueq_trans with (g x); auto.
Qed.

Lemma fSetoid : forall (A:Type), Setoid_Theory (A->U) (@feq A).
split; red; auto.
exact (@feq_trans A).
Qed.

Add Parametric Setoid A : (A->U) (@feq A) (@fSetoid A) as f_Setoid.

Lemma feq_fle : forall (A:Type) (f g : A->U), feq f g -> fle f g.
auto.
Qed.

Lemma feq_fle_sym : forall (A:Type) (f g : A->U), feq f g -> fle g f.
auto.
Qed.
Hint Immediate feq_fle feq_fle_sym.

Lemma fle_le : forall (A:Type) (f g : A->U), fle f g -> forall x, f x <= g x.
auto.
Qed.

Lemma fle_refl : forall (A:Type) (f:A->U), fle f f.
auto.
Qed.

Lemma fle_trans : forall (A:Type) (f g h : A->U), fle f g -> fle g h -> fle f h.
unfold fle; intros; apply Ule_trans with (g x); auto.
Qed.

Add Parametric Relation A : (A->U) (@fle A) 
   reflexivity proved by (@fle_refl A) transitivity proved by (@fle_trans A) as fle_Relation.

Lemma fle_feq_trans : forall (A:Type) (f g h : A->U), fle f g -> feq g h -> fle f h.
unfold fle; intros; apply Ule_trans with (g x); auto.
Qed.

Lemma feq_fle_trans : forall (A:Type) (f g h : A->U), feq f g -> fle g h -> fle f h.
unfold fle; intros; apply Ule_trans with (g x); auto.
Qed.

Lemma fle_antisym : forall (A:Type) (f g : A->U), fle f g -> fle g f -> feq f g.
auto.
Qed.
Hint Resolve fle_antisym.

Add Parametric Morphism A : (@fle A) with signature  (@feq A) ==> (@feq A) ==> iff as  fle_feq_compat. 
split; intros.
apply feq_fle_trans with x; auto.
apply fle_feq_trans with x0; auto.
apply feq_fle_trans with y; auto.
apply fle_feq_trans with y0; auto.
Qed.

Lemma fle_fplus_left : forall (A:Type) (f g : A->U), fle f (fplus f g).
unfold fle,fplus; auto.
Qed.

Lemma fle_fplus_right : forall (A:Type) (f g : A->U), fle g (fplus f g).
unfold fle,fplus; auto.
Qed.

Lemma fle_fmult : forall (A:Type) (k:U)(f : A->U), fle (fmult k f) f.
unfold fle,fmult; auto.
Qed.

Lemma fle_zero : forall (A:Type) (f : A->U), fle (f_zero A) f.
unfold fle,f_zero; auto.
Qed.

Lemma fle_one : forall (A:Type) (f : A->U), fle f (f_one A).
unfold fle,f_one; auto.
Qed.

Lemma feq_finv_finv : forall (A:Type) (f : A->U), feq (finv (finv f)) f.
unfold feq,finv; auto.
Qed.

Lemma fle_fesp_left : forall (A:Type) (f g : A->U), fle (fesp f g) f.
unfold fle,fesp; auto.
Qed.

Lemma fle_fesp_right : forall (A:Type) (f g : A->U), fle (fesp f g) g.
unfold fle,fesp; auto.
Qed.

(** *** Defining morphisms *)

Add Parametric Morphism A : (@fplus A) with signature (@feq A) ==> (@feq A) ==> (@feq A) as fplus_feq_compat.
unfold feq,fplus; auto.
Qed.

Add Parametric Morphism A : (@fplus A) with signature (@fle A) ++> (@fle A) ++> (@fle A) as fplus_fle_compat.
unfold fle,fplus; auto.
Qed.

Add Parametric Morphism A : (@finv A) with signature (@feq A) ==> (@feq A) as finv_feq_compat.
unfold feq,finv; auto.
Qed.

Add Parametric Morphism A : (@finv A) with signature (@fle A) --> (@fle A) as finv_fle_compat.
unfold fle,finv; auto.
Qed.

Add Parametric Morphism A : (@fmult A) with signature Ueq ==> (@feq A) ==> (@feq A) as fmult_feq_compat.
unfold feq,fmult; auto.
Qed.

Add Parametric Morphism A : (@fmult A) with signature Ule ++> (@fle A) ++> (@fle A) as fmult_fle_compat.
unfold fle,fmult; auto.
Qed.

Add Parametric Morphism A : (@fminus A) with signature (@feq A) ==> (@feq A) ==> (@feq A) as fminus_feq_compat.
unfold feq,fminus; auto.
Qed.

Add Parametric Morphism A : (@fminus A) with signature (@fle A) ++> (@fle A) --> (@fle A) as fminus_fle_compat.
unfold fle,fminus; auto.
Qed.


Add Parametric Morphism A : (@fesp A) with signature (@feq A) ==> (@feq A) ==> (@feq A) as fesp_feq_compat.
unfold feq,fesp; auto.
Qed.

Add Parametric Morphism A : (@fesp A) with signature (@fle A) ++> (@fle A) ++> (@fle A) as fesp_fle_compat.
unfold fle,fesp; auto.
Qed.

Hint Immediate feq_sym fplus_fle_compat fplus_feq_compat 
fmult_fle_compat fmult_feq_compat fminus_fle_compat fminus_feq_compat.

Hint Resolve fle_fplus_left  fle_fplus_right fle_zero  fle_one feq_finv_finv finv_fle_compat
fle_fmult fle_fesp_left fle_fesp_right.

Hint Resolve finv_feq_compat finv_fle_compat.

(** ** Fixpoints of functions of type $A\ra\U$ *)
Section FixDef.
Variable A :Type.

Variable F : (A->U) -> A -> U.
Definition Fmonotonic :=  forall f g, (fle f g) -> fle (F f) (F g).
Definition Fstable :=  forall f g, (feq f g) -> feq (F f) (F g).

Lemma Fmonotonic_stable : Fmonotonic -> Fstable.
unfold Fmonotonic, Fstable; auto.
Qed.

Lemma Fmonotonic_fle : Fmonotonic -> forall f g, fle f g -> fle (F f) (F g).
auto.
Qed.

Lemma Fmonotonic_le : Fmonotonic -> forall f g, fle f g -> forall x, F f x <= F g x.
auto.
Qed.

Lemma Fstable_feq : Fstable -> forall f g, feq f g -> feq (F f) (F g).
auto.
Qed.

Lemma Fstable_eq : Fstable -> forall f g, feq f g -> forall x, F f x == F g x.
auto.
Qed.

Hint Resolve Fmonotonic_fle Fstable_feq Fmonotonic_le  Fstable_eq.

Hypothesis Fmon : Fmonotonic.

Fixpoint muiter (n:nat) (x:A) {struct n} : U := 
        match n with O => 0 | S p => F (muiter p) x end.

Fixpoint nuiter (n:nat) (x:A) {struct n} : U := 
        match n with O => 1 | S p => F (nuiter p) x end.

Definition mufix (x:A) := lub (fun n => muiter n x).
Definition nufix (x:A) := glb (fun n => nuiter n x).

Lemma mufix_inv : forall f, fle (F f) f -> fle mufix f.
unfold mufix; red; intros; apply lub_le.
intro n; generalize x; induction n; simpl; intros; auto.
apply Ule_trans with (F f x0); auto.
Qed.
Hint Resolve mufix_inv.

Lemma nufix_inv : forall f, fle f (F f) -> fle f nufix.
unfold nufix; red; intros; apply le_glb.
intro n; generalize x; induction n; simpl; intros; auto.
apply Ule_trans with (F f x0); auto.
Qed.
Hint Resolve nufix_inv.

Lemma mufix_le : fle mufix (F mufix).
unfold mufix at 1; red; intros; apply lub_le.
destruct n; simpl; auto.
apply Fmon.
unfold mufix; intros.
red; intro x0; apply (le_lub (fun n0 : nat => muiter n0 x0)).
Qed.
Hint Resolve mufix_le.

Lemma nufix_sup : fle (F nufix) nufix.
unfold nufix at 2; red; intros; apply le_glb.
destruct n; simpl; auto.
apply Fmon.
unfold nufix; intros.
intro x0; apply (glb_le (fun n0 : nat => nuiter n0 x0)).
Qed.
Hint Resolve nufix_sup.

Definition Fcontlub := forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).
Definition Fcontglb := forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).

Lemma Fcontlub_fle : Fcontlub -> forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).
auto.
Qed.

Lemma Fcontglb_fle : Fcontglb -> forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).
auto.
Qed.


Hypothesis muFcont : forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).

Hypothesis nuFcont : forall (fn : nat -> A -> U), decrease fn -> 
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).

Implicit Arguments muFcont [].
Implicit Arguments nuFcont [].

Lemma incr_muiter : increase muiter.
red; intros; induction n; red; simpl; intros; auto.
Qed.

Lemma decr_nuiter : decrease nuiter.
red; intros; induction n; red; simpl; intros; auto.
Qed.

Hint Resolve incr_muiter decr_nuiter.

Lemma mufix_sup : forall x, F mufix x <= mufix x.
intros; apply Ule_trans with (lub (fun n => F (muiter n) x)); auto.
apply (muFcont muiter) with (x:=x); auto.
unfold mufix.
apply lub_le.
intro n; apply (le_lub (fun n0 : nat => muiter n0 x) (S n)); auto .
Qed.
Hint Resolve mufix_sup.

Lemma nufix_le : forall x, nufix x <= F nufix x.
intros; apply Ule_trans with (glb (fun n => F (nuiter n) x)); auto.
unfold nufix.
apply le_glb.
intro n; apply (glb_le (fun n0 : nat => nuiter n0 x) (S n)); auto .
apply (nuFcont nuiter) with (x:=x); auto.
Qed.
Hint Resolve nufix_le.

Lemma mufix_eq : forall x, mufix x == F mufix x.
intros; apply Ule_antisym; auto.
Qed.
Hint Resolve mufix_eq.

Lemma nufix_eq : forall x, nufix x == F nufix x.
intros; apply Ule_antisym; auto.
Qed.
Hint Resolve nufix_eq.

End FixDef.
Hint Unfold Fmonotonic.
Hint Resolve Fmonotonic_stable.
Hint Resolve Fmonotonic_fle Fstable_feq Fmonotonic_le  Fstable_eq.
Hint Resolve Fcontlub_fle Fcontglb_fle.

Definition Fcte (A:Type) (f:A->U) := fun (_:A->U) => f.
Lemma Fcte_mon : forall (A:Type) (f:A->U), Fmonotonic (Fcte f).
repeat red; unfold Fcte; auto.
Qed.

Lemma mufix_cte : forall (A:Type) (f:A->U), feq (mufix (Fcte f)) f.
red; intros; unfold mufix.
apply Ule_antisym.
apply lub_le; intros.
generalize x; induction n; unfold Fcte; simpl; intros; auto.
apply Ule_trans with (muiter (Fcte f) (S O) x); auto.
apply le_lub with (f:=fun n : nat => muiter (Fcte f) n x) (n:=S O).
Qed.

Lemma nufix_cte : forall (A:Type) (f:A->U), feq (nufix (Fcte f)) f.
red; intros; unfold nufix.
apply Ule_antisym.
apply Ule_trans with (nuiter (Fcte f) (S O) x); auto.
apply glb_le with (f:=fun n : nat => nuiter (Fcte f) n x) (n:=S O).
apply le_glb; intros.
generalize x; induction n; unfold Fcte; simpl; intros; auto.
Qed.

Hint Resolve mufix_cte nufix_cte.

(** ** Properties of barycenter of two points *)
Section Barycenter.
Variables a b : U.
Hypothesis sum_le_one : a <= [1-] b.

Lemma Uinv_bary : 
   forall x y : U, [1-] (a * x + b * y) == a * [1-] x + b * [1-] y + [1-] (a + b).
intros.
apply Uplus_eq_simpl_left with (a * x); auto.
apply Uinv_le_perm_right.
setoid_rewrite (Udistr_inv_left a x).
repeat norm_assoc_right.
apply Uplus_le_compat_right.
apply Ule_trans with (b + [1-] (a + b)); auto.
apply Ule_trans with ([1-] (a + b) + b); auto.
apply Ueq_trans with ([1-] (b * y)).
apply Ueq_trans with 
   ([1-] (a * x + b * y) + a * x); auto.
setoid_rewrite (Udistr_inv_left b y); auto.
apply Ueq_trans with  
 ((a * x + a * [1-] x) + b * [1-] y + [1-] (a + b)).
assert (x <= ([1-] ([1-] x))); auto.
setoid_rewrite <- (Udistr_plus_left a H); auto.
setoid_rewrite (Uinv_opp_right x).
setoid_rewrite (Umult_one_right a).
apply Ueq_trans with (b * [1-] y + ([1-] (a + b) + a)).
assert (b <= ([1-] a)); auto.
setoid_rewrite (Uinv_plus_left H0); auto.
setoid_rewrite (Uplus_sym a (b * [1-] y)); auto.
apply Ueq_trans with 
(b * [1-] y + (a + [1-] (a + b))); auto.
apply Ueq_trans with 
(((a * x + a * [1-] x) + (b * [1-] y + [1-] (a + b)))); auto.
apply Ueq_trans with 
(((a * x + (a * [1-] x + (b * [1-] y + [1-] (a + b)))))); auto.
Qed.

Lemma Uinv_bary_le : 
   forall x y : U,   a * [1-] x + b * [1-] y <= [1-] (a * x + b * y).
intros; rewrite Uinv_bary; auto.
Qed.

End Barycenter.
Hint Resolve Uinv_bary_le.

Lemma Uinv_half_bary : 
   forall x y : U, [1-] ([1/2] * x + [1/2] * y) == [1/2] * [1-] x + [1/2] * [1-] y.
intros; rewrite Uinv_bary; auto.
rewrite Unth_one_plus; rewrite Uinv_one; auto.
Qed.
Hint Resolve Uinv_half_bary.

(** ** Properties of generalized sums [sigma] *)
Lemma sigma_plus : forall (f g : nat -> U) (n:nat), 
   (sigma (fun k => (f k) + (g k)) n) == (sigma f n) + (sigma g n).
intros; induction n; simpl; auto.
repeat rewrite sigma_S; setoid_rewrite IHn.
repeat norm_assoc_right; apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym (g n) ((sigma f n) + (sigma g n))).
repeat norm_assoc_right; apply Uplus_eq_compat_right; auto.
Qed.


Definition retract (f : nat -> U) (n : nat) := forall k, (k < n)%nat -> (f k) <= [1-] (sigma f k).

Lemma retract0 : forall (f : nat -> U), retract f 0.
red; intros; absurd (k < O)%nat; auto with arith.
Qed.

Lemma retract_pred : forall (f : nat -> U) (n : nat), retract f (S n) -> retract f n.
unfold retract; auto with arith.
Qed.

Lemma retractS: forall (f : nat -> U) (n : nat), retract f (S n) -> f n <= [1-] (sigma f n).
unfold retract; auto with arith.
Qed.

Lemma retractS_intro: forall (f : nat -> U) (n : nat), 
   retract f n -> f n <= [1-] (sigma f n)->retract f (S n).
unfold retract; intros.
assert ((k<n)%nat \/ k=n); try omega; intuition; subst; auto.
Qed.

Hint Resolve retract0 retractS_intro.
Hint Immediate retract_pred retractS.

Lemma retract_lt : forall (f : nat -> U) (n : nat),  (sigma f n) < 1 -> retract f n.
induction n; simpl; auto.
rewrite sigma_S.
intros;assert ((sigma f n)<1).
apply Ule_lt_trans with (f n + sigma f n); auto.
assert (f n <= [1-](sigma f n)); auto.
apply Uplus_lt_Uinv; auto.
Qed.

Lemma sigma_mult : 
  forall (f : nat -> U) n c, retract f n -> (sigma (fun k => c * (f k)) n) == c * (sigma f n).
intros; induction n; simpl; auto.
repeat rewrite sigma_S.
assert (H1: retract f n); auto.
setoid_rewrite (IHn H1).
setoid_rewrite (Udistr_plus_left c (retractS H)); auto.
Qed.
Hint Resolve sigma_mult.

Lemma sigma_prod_maj :  forall (f g : nat -> U) n, 
   (sigma (fun k => (f k) * (g k)) n) <= (sigma f n).
auto.
Qed.

Hint Resolve sigma_prod_maj.

Lemma sigma_prod_le :  forall (f g : nat -> U) (c:U), (forall k, (f k) <= c) 
   -> forall n, (retract g n) -> (sigma (fun k => (f k) * (g k)) n) <= c * (sigma g n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
apply Ule_trans with ((f n) * (g n) + (c * sigma g n)); auto.
apply Ule_trans with ( c * (g n) + (c * sigma g n)); auto.
setoid_rewrite (Udistr_plus_left c (retractS H0)); auto.
Qed.

Lemma sigma_prod_ge :  forall (f g : nat -> U) (c:U), (forall k, c <= (f k)) 
   -> forall n, (retract g n) -> c * (sigma g n) <= (sigma (fun k => (f k) * (g k)) n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
setoid_rewrite (Udistr_plus_left c (retractS H0)); auto.
apply Ule_trans with (c * (g n) + sigma (fun k : nat => f k * g k) n); auto.
Qed.

Hint Resolve sigma_prod_maj sigma_prod_le  sigma_prod_ge.

Lemma sigma_inv : forall (f g : nat -> U) (n:nat), (retract f n) ->
  [1-] (sigma (fun k => f k * g k) n) == (sigma (fun k => f k * [1-] (g k)) n) + [1-] (sigma f n).
intros; induction n; simpl; repeat rewrite sigma_S; auto.
apply Uplus_eq_simpl_right with ((f n) * (g n)).
setoid_rewrite 
 (Uinv_inv (f n * g n + sigma (fun k : nat => f k * g k) n));auto.
apply Uinv_le_perm_right.
setoid_rewrite (Udistr_inv_left (f n) (g n)).
repeat norm_assoc_right; apply Uplus_le_compat_right.
apply Ule_trans with 
  (sigma f n + [1-] (f n + sigma f n)); auto.
assert (sigma f n <= [1-] (f n)); auto.
setoid_rewrite <- (Uinv_plus_right H0); auto.

assert (sigma (fun k : nat => f k * g k) n <= [1-] (f n * g n)).
apply Ule_trans with (sigma f n); auto.
apply Ule_trans with ([1-] (f n)); auto.
setoid_rewrite (Uinv_plus_left H0).
apply Ueq_trans with (1:=IHn (retract_pred H)).
setoid_rewrite (Uplus_sym (f n * [1-] (g n))
                          (sigma (fun k : nat => f k * [1-] (g k)) n)).
repeat norm_assoc_right; apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym  ([1-] (f n + sigma f n)) (f n * g n)).
repeat norm_assoc_left.
assert ([1-] (g n) <= [1-] (g n)); auto.

setoid_rewrite <- (Udistr_plus_left (f n) H1).
setoid_rewrite (Uinv_opp_left (g n)).
setoid_rewrite (Umult_one_right (f n)); auto.
setoid_rewrite (Uplus_sym (f n) ([1-] (f n + sigma f n))).
apply Ueq_sym; apply Uinv_plus_left; auto.
Qed.


(** ** Product by an integer *)

(** *** Definition of [Nmult n x] written [n */ x] *)
Fixpoint Nmult (n: nat) (x : U) {struct n} : U := 
   match n with O => 0 | (S O) => x | S p => x + (Nmult p x) end.

(** *** Condition for [n */ x] to be exact : $n = 0$ or $x\leq \frac{1}{n}$ *)
Definition Nmult_def (n: nat) (x : U) := 
   match n with O => True | S p => x <= [1/]1+p end.

Lemma Nmult_def_O : forall x, Nmult_def O x.
simpl; auto.
Qed.
Hint Resolve Nmult_def_O.

Lemma Nmult_def_1 : forall x, Nmult_def (S O) x.
simpl; intro; rewrite Unth_zero; auto.
Qed.
Hint Resolve Nmult_def_1.

Lemma Nmult_def_intro : forall n x , x <= [1/]1+n -> Nmult_def (S n) x.
destruct n; simpl; auto.
Qed.
Hint Resolve Nmult_def_intro.

Lemma Nmult_def_Unth: forall n , Nmult_def (S n) ([1/]1+n).
auto.
Qed.
Hint Resolve Nmult_def_Unth.

Lemma Nmult_def_pred : forall n x, Nmult_def (S n) x -> Nmult_def n x.
intros n x; case n; simpl; intros; auto.
apply Ule_trans with ([1/]1+(S n0)); auto.
Qed.

Hint Immediate Nmult_def_pred.

Lemma Nmult_defS : forall n x, Nmult_def (S n) x -> x <= [1/]1+n.
destruct n; simpl; intros; auto.
Qed.
Hint Immediate Nmult_defS.

Lemma Nmult_def_class : forall n p, class (Nmult_def n p).
unfold class; destruct n; intuition.
Qed.
Hint Resolve Nmult_def_class.

Add Morphism Nmult_def with signature (@eq _) ==> Ueq ==> iff as Nmult_def_eq_compat.

Infix "*/" := Nmult (at level 60) : U_scope.
unfold Nmult_def; destruct y; intuition.
rewrite <- H; auto.
rewrite H; auto.
Qed.

Lemma Nmult_def_zero : forall n, Nmult_def n 0.
destruct n; auto.
Qed.
Hint Resolve Nmult_def_zero.

(** *** Properties of [n */ x] *)

Lemma Nmult_0 : forall (x:U), O*/x = 0.
trivial.
Qed.

Lemma Nmult_1 : forall (x:U), (S O)*/x = x.
trivial.
Qed.

Lemma Nmult_zero : forall n, n */ 0 == 0.
induction n; simpl; auto.
destruct n; auto.
Qed.

Lemma Nmult_SS : forall (n:nat) (x:U), S (S n) */x = x + (S n */ x).
destruct n; simpl; auto.
Qed.

Lemma Nmult_2 : forall (x:U), 2*/x = x + x.
trivial.
Qed.

Lemma Nmult_S : forall (n:nat) (x:U), S n */ x == x + (n*/x).
destruct n; simpl; auto.
Qed.

Hint Resolve Nmult_1 Nmult_SS Nmult_2 Nmult_S.

Add Morphism Nmult with signature (@eq _) ==> Ueq ==> Ueq as Nmult_eq_compat.
intros n x1 x2 eq1; induction n; simpl; auto; intros.
destruct n; repeat rewrite Nmult_SS; trivial.
apply Uplus_eq_compat; auto.
Qed.
Hint Resolve Nmult_eq_compat.

Lemma Nmult_eq_compat_right : forall (n m:nat) (x:U), (n = m)%nat -> n */ x == m */ x.
intros; subst n; trivial.
Qed.
Hint Resolve Nmult_eq_compat_right.

Lemma Nmult_le_compat_right :  forall n x y, x <= y -> n */ x <= n */ y.
intros; induction n; auto.
rewrite (Nmult_S n x); rewrite (Nmult_S n y);auto.
Qed.

Lemma Nmult_le_compat_left : forall n m x, (n <= m)%nat -> n */ x <= m */ x.
induction 1; trivial.
rewrite (Nmult_S m x); auto.
apply Ule_trans with (m */ x); auto.
Qed.

Lemma Nmult_sigma : forall (n:nat) (x:U), n */ x == sigma (fun k => x) n.
intros n x; induction n; simpl; auto.
destruct n; auto.
unfold sigma; simpl; auto.
rewrite IHn; auto.
Qed.

Hint Resolve Nmult_eq_compat_right Nmult_le_compat_right 
Nmult_le_compat_left Nmult_sigma.

Lemma Nmult_Unth_prop : forall n:nat, [1/]1+n == [1-] (n*/ ([1/]1+n)).
intro.
rewrite (Nmult_sigma n ([1/]1+n)).
exact (Unth_prop n).
Qed.
Hint Resolve Nmult_Unth_prop.

Lemma Nmult_n_Unth: forall n:nat, n */ [1/]1+n == [1-] ([1/]1+n).
intro; apply Uinv_eq_perm_right; auto.
Qed.

Lemma Nmult_Sn_Unth: forall n:nat, S n */ [1/]1+n == 1.
intro; rewrite (Nmult_S n ([1/]1+n)).
rewrite (Nmult_n_Unth n); auto.
Qed.

Hint Resolve Nmult_n_Unth Nmult_Sn_Unth.

Lemma Nmult_ge_Sn_Unth: forall n k, (S n <= k)%nat -> k */ [1/]1+n == 1.
induction 1; auto.
rewrite (Nmult_S m ([1/]1+n)); rewrite IHle; auto.
Qed.

Lemma Nmult_le_n_Unth: forall n k, (k <= n)%nat -> k */ [1/]1+n <= [1-] ([1/]1+n).
intros; apply Ule_trans with (n */ [1/]1+n); auto.
Qed.

Hint Resolve Nmult_ge_Sn_Unth Nmult_le_n_Unth.


Lemma Nmult_Umult_assoc_left : forall n x y, Nmult_def n x -> n*/(x*y) == (n*/x)*y.
intros n x y; induction n; auto; intros.
destruct n; auto.
repeat rewrite Nmult_SS.
assert(Nmult_def (S n) x); auto.
setoid_rewrite (IHn H0).
assert (x <= [1-] ((S n) */ x)). 
apply Uinv_le_perm_right.
apply Ule_trans with ([1-] ([1/]1+(S n))); auto.
apply Ule_trans with ((S n) */ ([1/]1+(S n))); auto.
apply Ueq_sym; auto.
Qed.

Hint Resolve Nmult_Umult_assoc_left.

Lemma Nmult_Umult_assoc_right : forall n x y, Nmult_def n y -> n*/(x*y) == x*(n*/y).
intros; rewrite (Umult_sym x y); rewrite (Nmult_Umult_assoc_left n y x H); auto.
Qed.

Hint Resolve Nmult_Umult_assoc_right.

Lemma plus_Nmult_distr : forall n m x, (n + m) */ x== (n */ x) + (m */ x).
intros n m x; induction n; auto; intros.
rewrite plus_Sn_m.
rewrite (Nmult_S (n + m) x).
setoid_rewrite IHn.
rewrite (Nmult_S n x); auto.
Qed.

Lemma Nmult_Uplus_distr : forall n x y, n */ (x + y) == (n */ x) + (n */ y).
intros n x y; induction n.
simpl; auto.
rewrite (Nmult_S n (x+y)).
rewrite IHn.
norm_assoc_right.
rewrite (Uplus_perm2 y (n */ x) (n */ y)).
rewrite <- (Nmult_S n y).
norm_assoc_left.
apply Uplus_eq_compat; auto.
Qed.

Lemma Nmult_mult_assoc : forall n m x, (n * m) */ x == n */ (m */ x).
intros n m x; induction n; intros; auto.
simpl mult.
rewrite (plus_Nmult_distr m (n * m) x).
rewrite IHn; auto.
Qed.

Lemma Nmult_Unth_simpl_left : forall n x, (S n) */ ([1/]1+n * x) == x.
intros.
rewrite (Nmult_Umult_assoc_left (S n) ([1/]1+n) x (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Qed.

Lemma Nmult_Unth_simpl_right : forall n x, (S n) */ (x * [1/]1+n) == x.
intros.
rewrite (Nmult_Umult_assoc_right (S n) x ([1/]1+n) (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Qed.

Hint Resolve Nmult_Unth_simpl_left Nmult_Unth_simpl_right.

Lemma Uinv_Nmult : forall k n, [1-] (k */ [1/]1+n) == ((S n) - k)  */ [1/]1+n.
intros k n; case (le_lt_dec (S n) k); intro.
rewrite (Nmult_ge_Sn_Unth l).
replace (S n - k)%nat with O; auto.
omega.
induction k; intros.
rewrite Nmult_0; rewrite Uinv_zero.
replace (S n - O)%nat with (S n); auto with arith.
rewrite (Nmult_S k ([1/]1+n)).
apply Uplus_eq_simpl_right with ([1/]1+n); auto.
apply Uinv_le_perm_right.
apply Nmult_le_n_Unth.
omega.
apply Ueq_trans with (((S n - S k) + (S O)) */ [1/]1+n).
replace ((S n - S k) + (S O))%nat with (S n - k)%nat.
apply Ueq_trans with ([1-] (k */ [1/]1+n)); auto with arith.
apply Uinv_plus_left.
apply Nmult_le_n_Unth; omega.
omega.
rewrite (plus_Nmult_distr (S n - S k) (S O) ([1/]1+n)); auto.
Qed.

Lemma Nmult_neq_zero : forall n x, ~(0==x) -> ~(0==S n */ x).
intros; rewrite (Nmult_S n x); auto.
apply Uplus_neq_zero_left; trivial.
Qed.
Hint Resolve Nmult_neq_zero.


Lemma Nmult_le_simpl :  forall (n:nat) (x y:U), 
   Nmult_def (S n) x -> Nmult_def (S n) y -> (S n */ x) <= (S n */ y) -> x <= y.
intros; apply Umult_le_simpl_left with (S n */ [1/]1+n).
auto.
assert (Nmult_def (S n) ([1/]1+n)); auto.
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) x H2).
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) y H2).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) y H0).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) x H).
apply Ule_trans with ([1/]1+n * (S n */ x)); auto.
Qed.

Lemma Nmult_Unth_le : forall (n1 n2 m1 m2:nat), 
   (n2 * S n1<= m2 * S m1)%nat -> n2 */ [1/]1+m1 <= m2 */ [1/]1+n1.
intros.
apply Ule_trans with ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
apply Ule_trans with ((m2 * S m1) */ [1/]1+m1 * [1/]1+n1); auto.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto.
Qed.

Lemma Nmult_Unth_eq : 
   forall (n1 n2 m1 m2:nat), 
   (n2 * S n1= m2 * S m1)%nat -> n2 */ [1/]1+m1 == m2 */ [1/]1+n1.
intros.
apply Ueq_trans with ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat; trivial.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
rewrite H.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat; trivial.
Qed.

Hint Resolve Nmult_Unth_le Nmult_Unth_eq.

Lemma Nmult_def_lt : forall n x, n */ x <1 -> Nmult_def n x.
red; destruct n; intros; auto.
apply (Ule_total x ([1/]1+n)); intros; auto.
case H.
apply Ule_trans with (S n */ [1/]1+n); auto.
Qed.

Hint Immediate Nmult_def_lt.

(** ** Conversion from booleans to U *)

Definition B2U (b:bool) :U := if b then 1 else 0.
Definition NB2U (b:bool) :U := if b then 0 else 1.

Lemma B2Uinv : feq NB2U (finv B2U).
unfold NB2U,feq,finv,B2U; intro b; case b; auto.
Qed.

Lemma NB2Uinv : feq B2U (finv NB2U).
unfold NB2U,feq,finv,B2U; intro b; case b; auto.
Qed.

Hint Resolve B2Uinv NB2Uinv.

(** ** Particular sequences *)
  (**  $pmin (p)(n) = p - \frac{1}{2^n}$ *)

Definition pmin (p:U) (n:nat) :=  p - ([1/2]^n).

Add Morphism pmin with signature Ueq ==> (@eq _) ==> Ueq as pmin_eq_compat.
unfold pmin; auto.
Qed.

(** *** Properties of the invariant *)
Lemma pmin_esp_S : forall p n, pmin (p & p) n == pmin p (S n) & pmin p (S n).
unfold pmin at 1; intros.
setoid_rewrite (half_exp n).
setoid_rewrite (Uesp_minus_distr p p ([1/2]^(S n)) ([1/2]^(S n))); auto.
Qed.

Lemma pmin_esp_le : forall p n,  pmin p (S n) <= [1/2] * (pmin (p & p) n) + [1/2].
intros; setoid_rewrite (pmin_esp_S p n); auto.
Qed.

Lemma pmin_plus_eq :  forall p n, p <= [1/2] -> pmin p (S n) == [1/2] * (pmin (p + p) n).
intros; unfold pmin at 2.
setoid_rewrite (Uminus_distr_right [1/2] (p + p) ([1/2]^n)).
setoid_rewrite (half_twice H); auto.
Qed.

Lemma pmin_0 : forall p:U, pmin p O == 0.
unfold pmin; simpl; auto.
Qed.

Lemma pmin_le : forall (p:U) (n:nat), p - ([1/]1+n) <= pmin p n.
unfold pmin; intros.
apply Uminus_le_compat_right.
induction n; simpl; intros; auto.
apply Ule_trans with ([1/2] * ([1/]1+n)); auto.
Qed.

Hint Resolve pmin_0 pmin_le.

Lemma le_p_lim_pmin : forall p, p <= lub (pmin p).
intro; apply Ule_lt_lim; intros.
assert (exc (fun n : nat => t <= p - [1/]1+n)).
apply Ult_le_nth; trivial.
apply H0; auto; intros n H1.
apply Ule_trans with (p - [1/]1+n); auto.
apply Ule_trans with (pmin p n); auto.
Qed.

Lemma le_lim_pmin_p : forall p, lub (pmin p) <= p.
intro; apply lub_le; unfold pmin; auto.
Qed.
Hint Resolve le_p_lim_pmin le_lim_pmin_p.

Lemma eq_lim_pmin_p : forall p, lub (pmin p) == p.
intros; apply Ule_antisym; auto.
Qed.

Hint Resolve eq_lim_pmin_p.

(** Particular case where p = 1 *)

Definition U1min := pmin 1.

Lemma eq_lim_U1min : lub U1min == 1.
unfold U1min; auto.
Qed.

Lemma U1min_S : forall n, U1min (S n) == [1/2]*(U1min n) + [1/2].
intros; unfold U1min at 2,pmin.
rewrite (Uminus_distr_right [1/2] 1 ([1/2]^n)).
rewrite Umult_one_right.
rewrite Uminus_plus_perm; auto.
rewrite Unth_one_plus; auto.
Qed.

Lemma U1min_0 : U1min O == 0.
unfold U1min; auto.
Qed.

Hint Resolve eq_lim_U1min U1min_S U1min_0.

(** ** Tactic for simplification of goals *)

Ltac Usimpl :=  match goal with 
    |- context [(Uplus 0 ?x)]     => setoid_rewrite (Uplus_zero_left x)
 |  |- context [(Uplus ?x 0)]     => setoid_rewrite (Uplus_zero_right x)
 |  |- context [(Uplus 1 ?x)]     => setoid_rewrite (Uplus_one_left x)
 |  |- context [(Uplus ?x 1)]     => setoid_rewrite (Uplus_one_right x)
 |  |- context [(Umult 0 ?x)]     => setoid_rewrite (Umult_zero_left x)
 |  |- context [(Umult ?x 0)]     => setoid_rewrite (Umult_zero_right x)
 |  |- context [(Umult 1 ?x)]     => setoid_rewrite (Umult_one_left x)
 |  |- context [(Umult ?x 1)]     => setoid_rewrite (Umult_one_right x)
 |  |- context [(Uesp 0 ?x)]     => setoid_rewrite (Uesp_zero_left x)
 |  |- context [(Uesp ?x 0)]     => setoid_rewrite (Uesp_zero_right x)
 |  |- context [(Uesp 1 ?x)]     => setoid_rewrite (Uesp_one_left x)
 |  |- context [(Uesp ?x 1)]     => setoid_rewrite (Uesp_one_right x)
 |  |- context [(Uminus 0 ?x)]    => setoid_rewrite (Uminus_le_zero 0 x); 
                                        [apply (Upos x)| idtac]
 |  |- context [(Uminus ?x 0)]    => setoid_rewrite (Uminus_zero_right x)
 |  |- context [(Uminus ?x 1)]    => setoid_rewrite (Uminus_le_zero x 1);
                                        [apply (Unit x)| idtac]
 |  |- context [([1-] ([1-] ?x))] => setoid_rewrite (Uinv_inv x)
 |  |- context [([1-] 1)] => setoid_rewrite Uinv_one
 |  |- context [([1-] 0)] => setoid_rewrite Uinv_zero
 |  |- context [([1/]1+O)]        => setoid_rewrite Unth_zero
 |  |- context [?x^O] => setoid_rewrite (Uexp_0 x)
 |  |- context [?x^(S O)] => setoid_rewrite (Uexp_1 x)
 |  |- context [0^(?n)] => setoid_rewrite Uexp_zero; [omega|idtac]
 |  |- context [U1^(?n)] => setoid_rewrite Uexp_one
 |  |- context [(Nmult 0 ?x)]     => setoid_rewrite (Nmult_0 x)
 |  |- context [(Nmult 1 ?x)]     => setoid_rewrite (Nmult_1 x)
 |  |- context [(Nmult ?n 0)]     => setoid_rewrite (Nmult_zero n)
 |  |- context [(sigma ?f O)]     => setoid_rewrite (sigma_0 f)
 |  |- context [(sigma ?f (S O))]     => setoid_rewrite (sigma_1 f)
 |  |- (Ule (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_le_compat_right
 |  |- (Ule (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_le_compat_left
 |  |- (Ule (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y); 
					      apply Uplus_le_compat_left
 |  |- (Ule (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y); 
                                              apply Uplus_le_compat_left
 |  |- (Ule (Uinv ?y) (Uinv ?x)) => apply Uinv_le_compat
 |  |- (Ule (Uminus ?x ?y) (Uplus ?x ?z)) => apply Uminus_le_compat_right
 |  |- (Ule (Uminus ?x ?z) (Uplus ?y ?z)) => apply Uminus_le_compat_left
 |  |- (Ueq (Uinv ?x) (Uinv ?y)) => apply Uinv_eq_compat
 |  |- (Ueq (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_eq_compat_right
 |  |- (Ueq (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_eq_compat_left
 |  |- (Ueq (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y); 
                                             apply Uplus_eq_compat_left
 |  |- (Ueq (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y); 
					     apply Uplus_eq_compat_left
 |  |- (Ueq (Uminus ?x ?y) (Uplus ?x ?z)) => apply Uminus_eq_compat;[apply Ueq_refl|idtac]
 |  |- (Ueq (Uminus ?x ?z) (Uplus ?y ?z)) => apply Uminus_eq_compat;[idtac|apply Ueq_refl]
 |  |- (Ule (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_le_compat_right
 |  |- (Ule (Umult ?x ?z) (Umult ?y ?z)) => apply Umult_le_compat_left
 |  |- (Ule (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y); 
                                             apply Umult_le_compat_left
 |  |- (Ule (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y); 
                                             apply Umult_le_compat_left
 |  |- (Ueq (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_eq_compat_right
 |  |- (Ueq (Umult ?x ?z) (Umult ?y ?z)) =>  apply Umult_eq_compat_left
 |  |- (Ueq (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y); 
                                             apply Umult_eq_compat_left
 |  |- (Ueq (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y); 
                                             apply Umult_eq_compat_left
end.

(** ** Intervals *)

(** *** Definition *)
Record IU : Type := mk_IU {low:U; up:U; proper:low <= up}.

Hint Resolve proper.

(** the all set : [[0,1]] *)
Definition full := mk_IU (Upos 1).
(** singleton : [[x]] *)
Definition singl (x:U) := mk_IU (Ule_refl x).
(** down segment : [[0,x]] *)
Definition inf (x:U) := mk_IU (Upos x).
(** up segment : [[x,1]] *)
Definition sup (x:U) := mk_IU (Unit x).

(** *** Relations *)
Definition Iin (x:U) (I:IU) := low I <= x /\ x <= up I.

Definition Iincl I J := low J <= low I /\ up I <= up J.

Definition Ieq I J := low I == low J /\ up I == up J.
Hint Unfold Iin Iincl Ieq.

(** *** Properties *)
Lemma Iin_low : forall I, Iin (low I) I.
auto.
Qed.

Lemma Iin_up : forall I, Iin (up I) I.
auto.
Qed.

Hint Resolve Iin_low Iin_up.

Lemma Iin_singl_elim : forall x y, Iin x (singl y) -> x == y.
unfold Iin; intuition (simpl; auto).
Qed.


Lemma Iin_inf_elim : forall x y, Iin x (inf y) -> x <= y.
unfold Iin; intuition (simpl; auto).
Qed.

Lemma Iin_sup_elim : forall x y, Iin x (sup y) -> y <= x.
unfold Iin; intuition (simpl; auto).
Qed.

Lemma Iin_singl_intro : forall x y, x == y -> Iin x (singl y).
auto.
Qed.

Lemma Iin_inf_intro : forall x y, x <= y -> Iin x (inf y).
auto.
Qed.

Lemma Iin_sup_intro : forall x y, y <= x -> Iin x (sup y).
auto.
Qed.

Hint Immediate Iin_inf_elim Iin_sup_elim Iin_singl_elim.
Hint Resolve Iin_inf_intro Iin_sup_intro Iin_singl_intro.

Lemma Iin_class : forall I x, class (Iin x I).
unfold class, Iin; split.
apply Ule_class; intuition.
apply Ule_class; intuition.
Qed.

Lemma Iincl_class : forall I J, class (Iincl I J).
unfold class, Iincl; split.
apply Ule_class; intuition.
apply Ule_class; intuition.
Qed.

Lemma Ieq_class : forall I J, class (Ieq I J).
unfold class, Ieq; split.
apply Ueq_class; intuition.
apply Ueq_class; intuition.
Qed.
Hint Resolve Iin_class Iincl_class Ieq_class.

Lemma Iincl_in : forall I J, Iincl I J -> forall x, Iin x I -> Iin x J.
unfold Iin,Iincl; intuition.
apply Ule_trans with (low I); auto.
apply Ule_trans with (up I); auto.
Qed.

Lemma Iincl_low : forall I J, Iincl I J -> low J <= low I.
unfold Iincl; intuition.
Qed.

Lemma Iincl_up : forall I J, Iincl I J -> up I <= up J.
unfold Iincl; intuition.
Qed.

Hint Immediate Iincl_low Iincl_up.

Lemma Iincl_refl : forall I, Iincl I I.
unfold Iincl; intuition.
Qed.
Hint Resolve Iincl_refl.

Lemma Iincl_trans : forall I J K, Iincl I J -> Iincl J K -> Iincl I K.
unfold Iincl; intuition.
apply Ule_trans with (low J); auto.
apply Ule_trans with (up J); auto.
Qed.

Lemma Ieq_incl : forall I J, Ieq I J -> Iincl I J.
unfold Ieq,Iincl; intuition.
Qed.

Lemma Ieq_incl_sym : forall I J, Ieq I J -> Iincl J I.
unfold Ieq,Iincl; intuition.
Qed.
Hint Immediate Ieq_incl Ieq_incl_sym.

Lemma lincl_eq_compat : forall I J K L,
     Ieq I J -> Iincl J K -> Ieq K L -> Iincl I L.
intros; apply Iincl_trans with J; auto.
intros; apply Iincl_trans with K; auto.
Qed.

Lemma lincl_eq_trans : forall I J K,
     Iincl I J -> Ieq J K -> Iincl I K.
intros; apply lincl_eq_compat with I J; auto.
Qed.

Lemma Ieq_incl_trans : forall I J K,
     Ieq I J -> Iincl J K -> Iincl I K.
intros; apply lincl_eq_compat with J K; auto.
Qed.

Lemma Iincl_antisym : forall I J, Iincl I J -> Iincl J I -> Ieq I J.
unfold Iincl; intuition.
Qed.
Hint Immediate Iincl_antisym.

Lemma Ieq_refl : forall I, Ieq I I.
unfold Ieq; auto.
Qed.
Hint Resolve Ieq_refl.

Lemma Ieq_sym : forall I J, Ieq I J -> Ieq J I.
unfold Ieq; intuition.
Qed.
Hint Immediate Ieq_sym.

Lemma Ieq_trans : forall I J K, Ieq I J -> Ieq J K -> Ieq I K.
unfold Ieq; intuition.
apply Ueq_trans with (low J); auto.
apply Ueq_trans with (up J); auto.
Qed.

Lemma Isingl_eq : forall x y, Iincl (singl x) (singl y) -> x==y.
unfold Iincl, singl; intuition.
Qed.
Hint Immediate Isingl_eq.

Lemma Iincl_full : forall I, Iincl I full.
unfold Iincl, full; intuition.
Qed.
Hint Resolve Iincl_full.

(** *** Operations on intervals *)

Definition Iplus I J := mk_IU (Uplus_le_compat (proper I) (proper J)).

Lemma low_Iplus : forall I J, low (Iplus I J)=low I + low J.
trivial.
Qed.

Lemma up_Iplus : forall I J, up (Iplus I J)=up I + up J.
trivial.
Qed.

Lemma Iplus_in : forall I J x y, Iin x I -> Iin y J -> Iin (x+y) (Iplus I J).
unfold Iin,Iplus; intuition (simpl; auto).
Qed.

Lemma lplus_in_elim : 
forall I J z, low I <= [1-]up J -> Iin z (Iplus I J) 
                -> exc (fun x => Iin x I /\
                                                   exc (fun y => Iin y J /\ z==x+y)).
intros I J z H (H1,H2); simpl in H1,H2; intros.
assert (low I <= z).
apply Ule_trans with (low I + low J); auto.
apply (Ule_total (z-low I)  (up J)); intros.
apply class_exc.
(* case [z-low I <= up j] *)
apply exc_intro with (low I); split; auto.
apply exc_intro with (z-low I); split; auto.
assert (low I <= [1-]low J).
apply Ule_trans with ([1-]up J); auto.
split; auto.
apply Uplus_le_perm_right; auto.
rewrite Uplus_sym; auto.
(* case [up j <= z-low I] *)
assert (up J <= z); auto.
apply Ule_trans with (z - low I); auto.
apply exc_intro with (z-up J); split; auto.
split; auto.
apply Uplus_le_perm_left; auto.
rewrite Uplus_sym; auto.
apply exc_intro with (up J); auto.
Qed.

Definition Imult I J := mk_IU (Umult_le_compat (proper I) (proper J)).

Lemma low_Imult : forall I J, low (Imult I J) = low I * low J.
trivial.
Qed.

Lemma up_Imult : forall I J, up (Imult I J) = up I * up J.
trivial.
Qed.


Definition Imultk p I := mk_IU (Umult_le_compat_right p (proper I)).

Lemma low_Imultk : forall p I, low (Imultk p I) = p * low I.
trivial.
Qed.

Lemma up_Imultk : forall p I, up (Imultk p I) = p * up I.
trivial.
Qed.

Lemma Imult_in : forall I J x y, Iin x I -> Iin y J -> Iin (x*y) (Imult I J).
unfold Iin; intuition (simpl; auto).
Qed.

Lemma Imultk_in : forall p I x , Iin x I -> Iin (p*x) (Imultk p I).
unfold Iin; intuition (simpl; auto).
Qed.

(** *** limits *)

Definition lim : forall I:nat->IU, (forall n, Iincl (I (S n)) (I n)) -> IU.
intros; exists (lub (fun n => low (I n))) (glb (fun n => up (I n))).
unfold glb; apply lub_inv; intros; auto.
Defined.

Lemma low_lim : forall (I:nat->IU) (Idec : forall n, Iincl (I (S n)) (I n)),
             low (lim I Idec) = lub (fun n => low (I n)).
trivial.
Qed.

Lemma up_lim : forall (I:nat->IU) (Idec : forall n, Iincl (I (S n)) (I n)),
             up (lim I Idec) = glb (fun n => up (I n)).
trivial.
Qed.

Lemma lim_Iincl :  forall (I:nat->IU) (Idec : forall n, Iincl (I (S n)) (I n)),
             forall n, Iincl (lim I Idec) (I n).
unfold lim,Iincl; simpl; split.
apply le_lub with (f:=fun n0 : nat => low (I n0)).
apply glb_le with (f:=fun n0 : nat => up (I n0)).
Qed.
Hint Resolve lim_Iincl.

Lemma Iincl_lim :  forall J (I:nat->IU) (Idec : forall n, Iincl (I (S n)) (I n)),
             (forall n, Iincl J (I n)) -> Iincl J (lim I Idec).
unfold lim,Iincl; simpl; split.
apply lub_le with (f:=fun n0 : nat => low (I n0)); intro.
case (H n); auto.
apply le_glb with (f:=fun n0 : nat => up (I n0)); intro.
case (H n); auto.
Qed.

Lemma Iim_incl_stable : forall I J (Idec : forall n, Iincl (I (S n)) (I n)) 
               (Jdec : forall n, Iincl (J (S n)) (J n)), 
               (forall n, Iincl (I n) (J n)) -> Iincl (lim I Idec) (lim J Jdec).
intros; apply Iincl_lim. 
intros; apply Iincl_trans with (I n); auto.
Qed.
Hint Resolve Iim_incl_stable.

(** *** Fixpoints *)
Section Ifixpoint.
Variable A : Type.
Variable F : (A -> IU) -> A -> IU.
Hypothesis Fmon : forall I J, (forall x, Iincl (I x) (J x)) -> forall x, Iincl (F I x) (F J x).

Fixpoint Iiter (n:nat) : A -> IU := 
     match n with O => fun x => full | S m => F (Iiter  m) end.

Lemma Iiter_decr : forall x n, Iincl (Iiter (S n) x) (Iiter n x).
intros x n; generalize x; induction n; simpl; auto.
Qed.
Hint Resolve Iiter_decr.

Definition Ifix (x:A) := lim (fun n => Iiter n x) (Iiter_decr x).

Lemma Iincl_fix : forall (x:A), Iincl (F Ifix x) (Ifix x).
unfold Ifix at 2; intros.
apply Iincl_lim.
destruct n; simpl; auto.
apply Fmon.
unfold Ifix; intros.
apply (lim_Iincl (fun n0 : nat => Iiter n0 x0)).
Qed.

Lemma Iincl_inv : forall f, (forall x, Iincl (f x) (F f x)) -> forall x, Iincl (f x) (Ifix x).
unfold Ifix; intros; apply Iincl_lim.
intro n; generalize x; induction n; simpl; intros; auto.
apply Iincl_trans with (F f x0); auto.
Qed.

End Ifixpoint.
End Univ_prop.


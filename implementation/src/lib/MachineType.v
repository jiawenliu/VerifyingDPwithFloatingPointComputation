(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.String Coq.Lists.List 
      Coq.Arith.Arith Coq.Arith.EqNat Ascii Coq.Bool.Bool
      Coq.ZArith.ZArith.

From Gappa Require Import Gappa_tactic.

From Snapv.distr Require Import Extra Prob.

From Flocq Require Import Core Bracket Round Operations Div Sqrt  Plus_error.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype rat ssrint.
From mathcomp Require Import seq choice ssralg ssrnum Rstruct reals order.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.

Delimit Scope R_scope with coq_R.
Delimit Scope Z_scope with coq_Z.
Local Open Scope ring_scope.
Bind Scope ring_scope with R.

(* The fixed Floating Point number of 64 bits, with 52 bits mantissa and 11 bits
of exponents

TODO: Add precision constraints.

*)
Record float64 : Set := F64 { Num : R }.
Canonical float64_subType := [newType for Num].
Variable beta : radix.

Declare Scope float_scope.
Delimit Scope float_scope with F64.
Bind Scope float_scope with float64.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Variable prec : Z.
Context (Hprec : (0 < prec)%coq_Z).
Hypothesis fexp_prec : forall e, (e - prec <= fexp e)%coq_Z.

Variable rndR2Z : R -> Z.
Context { valid_rnd : Valid_rnd rndR2Z }.

Definition rnd := rounding_float rndZR 53 (-1074).
Definition rndFR (r : R) := rnd (r).
Definition R2F (r : R) := F64 (r).
Definition R2F64 (r : R) : float64 := F64 (rnd r).
Definition F2R (f : float64) : R := Num f.

Definition SI2R (x : int) : R :=
  match x with
  | Posz n => INR n
  | Negz n => - INR n
  end.

Definition Q2F (x : rat) : float64 := (R2F (Rdiv ( SI2R (numq x)) (SI2R (denq x)))).

Definition format :=
  generic_format radix2 (FLT_exp (-1074) 53).

Lemma R_ordAxioms : Ord.axioms Rleb.
Proof.
split.
- exact: Order.POrderTheory.le_refl.
- exact: Order.POrderTheory.le_trans.
- exact: Order.POrderTheory.le_anti.
- exact: Order.TotalTheory.le_total.
Qed.

Definition R_ordMixin := OrdMixin R_ordAxioms.
Canonical R_ordType := OrdType R R_ordMixin.

Definition F_eqMixin := [eqMixin of float64 by <:].
Canonical F_eqType := EqType float64 F_eqMixin.
Definition F_choiceMixin := [choiceMixin of float64 by <:].
Canonical F_choiceType := Eval hnf in ChoiceType float64 F_choiceMixin.
Definition F_ordMixin := [ordMixin of float64 by <:].
Canonical F_ordType := Eval hnf in OrdType float64 F_ordMixin.
Definition F_porderMixin := [porderMixin of float64 by <:].
Canonical F_porderType := Eval hnf in POrderType tt float64 F_porderMixin.
Definition F_orderMixin := [totalOrderMixin of float64 by <:].
Canonical F_latticeType := Eval hnf in LatticeType float64 F_orderMixin.
Canonical F_distrLatticeType := Eval hnf in DistrLatticeType float64 F_orderMixin.
Canonical F_orderType := Eval hnf in OrderType float64 F_orderMixin.

(*Operations on Real Type *)

Definition Rclamp  (b v : R) : R :=
  if b <= v
  then  ( b)
  else if v <= - b
       then (Ropp( b))
       else  ( v).

Definition Rround (lam v : R) :=
  let v1 := (IZR(rndR2Z(v /lam ))) * lam in
  let v2 := `|v - v1| in
    if v2 <= 0.5%coq_R
  then v1
    else
      match Rcase_abs v1 with
      | left _ =>  v1 - 1
      | right _ => v1 + 1
      end.


(* Operations on Real Type in Precision of Float 64 *)

Definition Fdiv (x y : R) : R := rndFR (rndFR x / rndFR y).
Definition Fplus  (x y : R) : R := rndFR (rndFR x + rndFR y).
Definition Fsub  (x y : R) : R := rndFR (rndFR x - rndFR y).
Definition Fmult  (x y : R) : R := rndFR (rndFR x * rndFR y).
Definition Fneg (v : R) := rndFR (- (rndFR v)).
Definition Fln (v : R) := rndFR (ln (rndFR v)).                                       

Definition Fround  (lam v : R) :=
  let v1 := (IZR(rndR2Z((rndFR v) / (rndFR lam)))) * lam in
  let v2 := Rabs (v - v1) in
    if v2 <= 0.5%coq_R
  then v1
    else
      match Rcase_abs v1 with
      | left _ =>  rndFR (rndFR v1 - 1)
      | right _ =>  rndFR (rndFR v1 + 1)
      end.

Definition Fclamp  (b v : R) : R :=
  if rndFR b <= rndFR v
  then  (rndFR b)
  else if rndFR v <= - rndFR b
       then - rndFR b
       else  (rndFR v).


(* Operations on Float 64 Type in Precision of fixed 64 bits Float-point *)

Definition f64exp (x: float64) :=  (R2F (exp (Num x))).
Definition fln (x: float64) :=  (R2F (ln (Num x))).
Definition fneg (x : float64) : float64 :=(R2F (- (F2R x))).

Definition fdiv (x y : float64) : float64 :=  (R2F (Num x / Num y)).
Definition fplus  (x y : float64) : float64 :=  (R2F (Num x + Num y)).
Definition fsub  (x y : float64) : float64 :=  (R2F (Num x - Num y)).
Definition fmult  (x y : float64) : float64 := (R2F (Num x * Num y)).

Notation "x / y" := (fdiv x y) : float_scope.
Notation "x + y" := (fplus x y) : float_scope.
Notation "x - y" := (fsub x y) : float_scope.
Notation "x * y" := (fmult x y) : float_scope.
Notation "- x" := (fneg x) : float_scope.

Definition fround  (lam v : float64) : float64 :=
  let v1 := IZR (rndR2Z((Num v) / (Num lam))) * Num lam in
  let v2 := `|Num v - v1| in
    if v2 <= 0.5%coq_R
  then (R2F64 v1)
    else
      match Rcase_abs v1 with
      | left _ =>  R2F64 (v1 - 1)
      | right _ =>  R2F64 (v1 + 1)
      end.

Definition fclamp  (b v : float64) : float64 :=
  if Num b <= Num v
  then  b
  else if Num v <= -Num b
       then (R2F (- (F2R b)))
       else  v.

Local Import GRing.Theory.

(* Definitions  on Triple with Error bounds*)
Definition err : Type :=  (R * R).
Definition bfloat64' := {v : float64 * err | v.2.1 <= (F2R v.1) <= v.2.2}%R.
Definition bfloat64 :Type := float64 * err.

Definition bval : bfloat64' -> float64 := fun v => (sval v).1.
Definition lb : bfloat64' -> R := fun v => (sval v).2.1.
Definition ub : bfloat64' -> R := fun v => (sval v).2.2.

Inductive ptbdir : Type := Down | Up.

Definition perturb (eta : R) (e: R) (dir: ptbdir) :  R :=
  match dir with
  (* the upper bound of the relative error for Fixed-point computation,
   computed in terms of real number*)
  |Up =>  (e * (1 + eta))
  (* the lower bound of the relative error for Fixed-point computation, 
   computed in terms of real number*)
  |Down => ( e / (1 + eta))
  end.


(* Operations on Float 64 Type in Precision of fixed 64 bits Float-point *)

Definition eta := 0.00001%coq_R.

Definition  Tln (v: bfloat64) : bfloat64 :=
  (fln v.1, 
    (perturb eta (ln v.2.1)  Down, 
     perturb eta (ln v.2.2)  Up)).

Definition  Tneg (v: bfloat64) : bfloat64 :=
  (fneg v.1, 
    (perturb eta (- v.2.1)  Down,
     perturb eta (- v.2.2)  Up)).

Definition  Tplus (v1 v2: bfloat64) : bfloat64 :=
  (fplus v1.1 v2.1, 
    (perturb eta (v1.2.1 + v2.2.1)  Down,
     perturb eta (v1.2.2 + v2.2.2)  Up)).

Definition  Tdiv (v1 v2: bfloat64) : bfloat64 :=
  ((fdiv v1.1 v2.1), 
    (perturb eta (v1.2.1 / v2.2.1)  Down,
     perturb eta (v1.2.2 / v2.2.2)  Up)).


Definition  Tsub (v1 v2: bfloat64) : bfloat64 :=
  ((fsub v1.1 v2.1), 
    (perturb eta (v1.2.1 - v2.2.1)  Down,
     perturb eta (v1.2.2 - v2.2.2)  Up)).


Definition  Tmult (v1 v2: bfloat64) : bfloat64 :=
  ((fmult v1.1 v2.1), 
    (perturb eta (v1.2.1 * v2.2.1)  Down,
     perturb eta (v1.2.2 * v2.2.2)  Up)).


Definition Tround  (v1 v2 : bfloat64) : bfloat64 :=
   ((fround v1.1 v2.1), 
    (perturb eta (Rround v1.2.1 v2.2.1)  Down, 
     perturb eta (Rround v1.2.2 v2.2.2)  Up)).

Definition Tclamp  (b v : bfloat64) : bfloat64 :=
   ((fclamp b.1 v.1), 
    (perturb eta (Rclamp b.2.1 v.2.1)  Down, 
     perturb eta (Rclamp b.2.2 v.2.2)  Up)).

Local Open Scope ring_scope.

(** Lemmas about Reals *)

Implicit Types a b c : R.

(* Compatibility with mathcomp *)
Lemma exp_plus : forall a b, exp (a + b) = (exp a) * (exp b).
Proof. exact: exp_plus. Qed.
Lemma exp_pos : forall r, 0 < exp r.
Proof. move=> r; apply/RltP; exact: exp_pos. Qed.

Local Import Order.POrderTheory.
Local Import Order.TotalTheory.

Lemma Rexp_ln_le : forall a b, 0 < b -> (a <= ln b) = (exp a <= b).
Proof.
move=> a b b_pos; apply/(sameP idP)/(iffP idP).
- apply: contra_le; rewrite -{1}[a]ln_exp => /RltP /ln_lt_inv lb_a.
  apply/RltP; apply: lb_a; apply/RltP => //; exact/exp_pos.
- apply: contra_le; rewrite -{1}[b]exp_ln; last exact/RltP.
  by move=> /RltP /exp_lt_inv /RltP.
Qed.

Lemma Rln_exp_le : forall a b, 0 < a -> (ln a <= b) = (a <= exp b).
Proof.
move=> a b a_pos; apply/(sameP idP)/(iffP idP).
- apply: contra_le; rewrite -{1}[b]ln_exp => /RltP /ln_lt_inv eb_a.
  apply/RltP; apply: eb_a; apply/RltP => //; exact/exp_pos.
- apply: contra_le; rewrite -{1}[a]exp_ln; last exact/RltP.
  by move=> /RltP /exp_lt_inv /RltP.
Qed.

Axiom Rmult_div_inv_le : forall a b c,
  0 < b -> a <= b * c <-> a / b <= c.

Axiom Rdiv_gt0 : forall a,
    0 < a <-> 0 < 1/a.
Axiom Rinv_inv_simpl : forall a,
    1 / (1 / a) =  a^-1^-1.

Axiom Rdiv_inv_mult_assoc : forall a v,
    a / (1 / v) = a * (v^-1^-1).

Axiom Rmult_div_inv_le_l : forall a b c,
    0 < b -> b * a  <= c <-> a <= c / b.

Axiom Rmult_div_inv_le_r : forall a b c,
    0 < a -> b * a  <= c <-> b <= 1/a * c.


Axiom Rdiv_mult_inv_le : forall a b c,
    0 < c -> a <= b * c <-> 1/c * a  <= b.



(***** Axioms about Floats ****)

Axiom round_eqV : forall y v Lam,
    (v - Lam / 2%coq_R) <= y <= (v + Lam / 2%coq_R)  <-> F2R (fround (F64 Lam) (F64 y)) = v.

Axiom clamp_eqV : forall v e B,
    
 F2R e = v <-> F2R (fclamp (F64 B) e) = v .


Axiom qle_fle  : forall (x : rat), le_rat zeroq x ->
  (F64 0 <= Q2F x)%ord.

Axiom f0_eq : (R2F64 0) = (F64 0).

Section WithNotation.

Local Open Scope order_scope.

Axiom f0_le_exp: forall x, F64 0 <= f64exp x.

Axiom fexp_mult :
  forall e1 e2, fmult (f64exp (R2F64 (e1))) (f64exp (R2F64 (e2))) = (f64exp (R2F64 (e1 + e2))).

Axiom fle_mult: forall (v r : float64),
  F64 0 <= v -> F64 0 <= r -> fsub v (fmult r v) <= F64 0.


Axiom fle_mult_left : forall (x f1 f2 : float64),
    f1 <= f2 -> fmult f1 x <= fmult f2 x.

Axiom fle_sub: forall (x v r : float64),
    v <= r -> fsub x v <= F64 0 -> fsub x r <= F64 0.

Axiom rle_fle: forall (r1 r2 : R),
    r1 <= r2 -> R2F64 r1 <= R2F64 r2.

Axiom fle_exp : forall (f1 f2: float64),
    f1 <= f2 -> f64exp f1 <= f64exp f2.

Axiom fle_mult_le : forall (a b c d : rat) (e1 e2: float64),
 fsub (Q2F a) (fmult e1 (Q2F b)) <= {| MachineType.Num := 0 |}
 -> fsub (Q2F c) (fmult e2 (Q2F d)) <= {| MachineType.Num := 0 |}
 -> fsub (Q2F (mulq a c)) (fmult (fmult e1 e2) (Q2F (mulq b d))) <= {| MachineType.Num := 0 |}.

Axiom fle_sum:
  forall (T S : ordType) (eL eR: {prob T*T}) (drawR drawL: (T* T) -> {prob  S * S}) x (a : float64),
    (forall x0, x0 \in (supp eL :|: supp eR)%fset ->
      fsub (Q2F (eL x0 * drawL x0 x)) (fmult a (Q2F (eR x0 * drawR x0 x)))
      <= {| MachineType.Num := 0 |})
    -> fsub (Q2F (\sum_(x0 <- supp eL) eL x0 * drawL x0 x))
            (fmult a (Q2F (\sum_(x0 <- supp eR) eR x0 * drawR x0 x))) <=
    {| MachineType.Num := 0 |}.

End WithNotation.

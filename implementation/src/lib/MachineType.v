(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
      Coq.Arith.Arith Coq.Arith.EqNat Ascii Coq.Bool.Bool
      Coq.Sets.Ensembles
      Coq.Lists.ListSet
      Coq.Reals.Rpower
      Coq.Reals.Rdefinitions.
Require Import Omega.

From Gappa Require Import Gappa_tactic.

From Snapv.distr Require Import Extra Prob.

From Flocq Require Import Core Bracket Round Operations Div Sqrt  Plus_error.


From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype rat ssrint.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.

Open Scope R_scope.

(*The fixed Floating Point number of 64 bits, with 52 bits mantissa and 11 bits of exponents*)
Record float64 : Set := F64 { Num : R }.
Variable beta : radix.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Variable prec : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis fexp_prec :
  forall e, (e - prec <= fexp e)%Z.

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


Definition rle x y : bool := Rle_dec x y.


(*Operations on Real Type *)

Definition Rclamp  (b v : R) : R :=
  if rle ( b) ( v)
  then  ( b)
  else if rle ( v) (Ropp( b))
       then (Ropp( b))
       else  ( v).

Definition Rround
            (lam v : R) :=
  let v1 := (Rmult (IZR(rndR2Z(v /lam )))  lam) in
  let v2 := Rabs (v - v1) in
    if rle v2 0.5
  then v1
    else
      match Rcase_abs v1 with
      | left _ =>  (Rminus ( v1) 1)
      | right _ => (Rplus ( v1) 1)
      end.


(* Operations on Real Type in Precision of Float 64 *)

Definition Fdiv (x y : R) : R := rndFR (Rdiv (rndFR x) (rndFR y)).
Definition Fplus  (x y : R) : R := rndFR (Rplus (rndFR x) (rndFR y)).
Definition Fsub  (x y : R) : R := rndFR (Rminus (rndFR x) (rndFR y)).
Definition Fmult  (x y : R) : R := rndFR (Rmult (rndFR x) (rndFR y)).
Definition Fneg (v : R) := rndFR (Ropp (rndFR v)).
Definition Fln (v : R) := rndFR (ln (rndFR v)).                                       

Definition Fround  (lam v : R) :=
  let v1 := (Rmult (IZR(rndR2Z((rndFR v) / (rndFR lam))))  lam) in
  let v2 := Rabs (v - v1) in
    if rle v2 0.5
  then v1
    else
      match Rcase_abs v1 with
      | left _ =>  rndFR (Rminus (rndFR v1) 1)
      | right _ =>  rndFR (Rplus (rndFR v1) 1)
      end.

Definition Fclamp  (b v : R) : R :=
  if rle (rndFR b) (rndFR v)
  then  (rndFR b)
  else if rle (rndFR v) (Ropp(rndFR b))
       then (Ropp(rndFR b))
       else  (rndFR v).


(* Operations on Float 64 Type in Precision of fixed 64 bits Float-point *)
Definition fle (x y : float64) : bool := rle (Num x) (Num y).

Definition f64exp (x: float64) :=  (R2F (exp (Num x))).
Definition fln (x: float64) :=  (R2F (ln (Num x))).
Definition fneg (x : float64) : float64 :=(R2F (Ropp(F2R x))).

Definition fdiv (x y : float64) : float64 :=  (R2F (Rdiv (Num x) (Num y))).
Definition fplus  (x y : float64) : float64 :=  (R2F (Rplus (Num x) (Num y))).
Definition fsub  (x y : float64) : float64 :=  (R2F (Rminus (Num x) (Num y))).
Definition fmult  (x y : float64) : float64 := (R2F (Rmult (Num x) (Num y))).

Definition fround  (lam v : float64) : float64 :=
  let v1 := (Rmult (IZR(rndR2Z((Num v) / (Num lam)))) ( Num lam)) in
  let v2 := Rabs ((Num v) - v1) in
    if rle v2 0.5
  then (R2F64 v1)
    else
      match Rcase_abs v1 with
      | left _ =>  R2F64 (Rminus (v1) 1)
      | right _ =>  R2F64 (Rplus (v1) 1)
      end.

Definition fclamp  (b v : float64) : float64 :=
  if rle (Num b) (Num v)
  then  b
  else if rle (Num v) (Ropp(Num b))
       then (R2F (Ropp(F2R b)))
       else  v.



         


(* Definitions  on Triple with Error bounds*)
Definition err : Type :=  (R * R).
Definition bfloat64' := {v : float64 * err | v.2.1 <= (F2R v.1) <= v.2.2}.
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

Definition eta := 0.00001%R.

Definition  Tln (v: bfloat64) : bfloat64 :=
  (fln v.1, 
    (perturb eta (ln v.2.1)  Down, 
     perturb eta (ln v.2.2)  Up)).

Definition  Tneg (v: bfloat64) : bfloat64 :=
  (fneg v.1, 
    (perturb eta (Ropp v.2.1)  Down, 
     perturb eta (Ropp v.2.2)  Up)).


Definition  Tplus (v1 v2: bfloat64) : bfloat64 :=
  (fplus v1.1 v2.1, 
    (perturb eta (Rplus v1.2.1 v2.2.1)  Down, 
     perturb eta (Rplus v1.2.2 v2.2.2)  Up)).

Definition  Tdiv (v1 v2: bfloat64) : bfloat64 :=
  ((fdiv v1.1 v2.1), 
    (perturb eta (Rdiv v1.2.1 v2.2.1)  Down, 
     perturb eta (Rdiv v1.2.2 v2.2.2)  Up)).


Definition  Tsub (v1 v2: bfloat64) : bfloat64 :=
  ((fsub v1.1 v2.1), 
    (perturb eta (Rminus v1.2.1 v2.2.1)  Down, 
     perturb eta (Rminus v1.2.2 v2.2.2)  Up)).


Definition  Tmult (v1 v2: bfloat64) : bfloat64 :=
  ((fmult v1.1 v2.1), 
    (perturb eta (Rmult v1.2.1 v2.2.1)  Down, 
     perturb eta (Rmult v1.2.2 v2.2.2)  Up)).


Definition Tround  (v1 v2 : bfloat64) : bfloat64 :=
   ((fround v1.1 v2.1), 
    (perturb eta (Rround v1.2.1 v2.2.1)  Down, 
     perturb eta (Rround v1.2.2 v2.2.2)  Up)).



Definition Tclamp  (b v : bfloat64) : bfloat64 :=
   ((fclamp b.1 v.1), 
    (perturb eta (Rclamp b.2.1 v.2.1)  Down, 
     perturb eta (Rclamp b.2.2 v.2.2)  Up)).



Local Open Scope ring_scope.


(**Axioms about Reals*)
Axiom Rplus_minusopp : forall a b, a - b = a + (-b).
Axiom Rexp_plus : forall a b, exp (a + b) = (exp a) * (exp b).
Axiom Rmult_div : forall a b, a / b = a * / b.
Axiom Rexp_ge0 : forall r, 0 < exp r .

Axiom Rexp_ln_le : forall a b, a <= ln b <-> exp a <= b.

Axiom Rln_exp_le : forall a b, ln a <= b <-> a <= exp b.

Axiom Rmult_div_inv_le : forall a b c,
    0 < b -> a <= b * c <-> a / b <= c.
Axiom Rdiv_gt0 : forall v,
    0 < v <-> 0 < 1/v.
Axiom Rinv_inv_simpl : forall v,
    1 / (1 / v) =  / /v.

Axiom Rdiv_inv_mult_assoc : forall a v,
    a / (1 / v) = a * (/ / v).

Axiom Rmult_div_inv_le_l : forall a b c,
    0 < b -> b * a  <= c <-> a <= c / b.





(***** Axioms about Floats ****)

Axiom round_eqV : forall y v Lam,
    (v - Lam / 2) <= y <= (v + Lam / 2)  <-> F2R (fround (F64 Lam) (F64 y)) = v.

Axiom clamp_eqV : forall v e B,
    
 F2R e = v <-> F2R (fclamp (F64 B) e) = v .


Axiom qle_fle  : forall (x : rat), le_rat zeroq x ->
  fle (F64 0) (Q2F x).

Axiom f0_eq : (R2F64 0) = (F64 0).

Axiom f0_le_exp: forall x, fle (F64 0) (f64exp x).

Axiom fle_ref : forall (x : float64), fle x x.  

Axiom feq_req: forall x y, x = y <-> (Num x) = (Num y).

Axiom fexp_mult :
  forall e1 e2, fmult (f64exp (R2F64 (e1))) (f64exp (R2F64 (e2))) = (f64exp (R2F64 (Rplus e1 e2))).

Axiom fle_mult: forall (v r : float64),
fle (F64 0) v -> fle (F64 0) r -> fle (fsub v (fmult r v))  (F64 0).


Axiom fle_mult_left : forall (x f1 f2 : float64),
fle f1 f2 -> fle (fmult f1 x) (fmult f2 x).



Axiom fle_sub: forall (x v r : float64),
  fle v r -> fle (fsub x v) (F64 0) -> fle (fsub x r) (F64 0).

Axiom rle_fle: forall (r1 r2 : R),
rle r1 r2 -> fle (R2F64 r1) (R2F64 r2).

Axiom fle_exp : forall (f1 f2: float64),
fle f1 f2 -> fle (f64exp f1) (f64exp f2).

 

Lemma fle_mult_le  a b c d e1 e2:
 fle (fsub (Q2F a) (fmult e1 (Q2F b))) {| MachineType.Num := 0 |}
 -> fle (fsub (Q2F c) (fmult e2 (Q2F d))) {| MachineType.Num := 0 |}
 -> fle (fsub (Q2F (mulq a c)) (fmult (fmult e1 e2) (Q2F (mulq b d)))) {| MachineType.Num := 0 |}.
Proof.
Admitted.


From mathcomp Require Import ssralg.
  Import GRing.

  
Lemma fle_sum:
  forall (T S : ordType) (eL eR: {prob T*T}) (drawR drawL: (T* T) -> {prob  S * S}) x a,
    (forall x0, x0 \in (supp eL :|: supp eR)%fset -> fle (fsub (Q2F (eL x0 * drawL x0 x))
              (fmult a (Q2F (eR x0 * drawR x0 x)))) {| MachineType.Num := 0 |})
    ->fle
    (fsub (Q2F (\sum_(x0 <- supp eL) eL x0 * drawL x0 x))
       (fmult a (Q2F (\sum_(x0 <- supp eR) eR x0 * drawR x0 x))))
    {| MachineType.Num := 0 |}.
Proof.

Admitted.

Axiom Rle_rle : forall r1 r2 , Rle r1 r2 <-> rle r1 r2.




Close Scope R_scope.

Close Scope ring_scope.


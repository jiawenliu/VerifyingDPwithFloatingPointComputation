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


From Flocq Require Import Core Bracket Round Operations Div Sqrt  Plus_error.


From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype rat ssrint.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.


(*The fixed Floating Point number of 64 bits, with 
52 bits mantissa and 11 bits of exponents*)
Record float64 : Set := F64 { Num : R }.


Variable beta : radix.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Variable prec : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis fexp_prec :
  forall e, (e - prec <= fexp e)%Z.

(* Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.
 *)
Variable rndR2Z : R -> Z.
Context { valid_rnd : Valid_rnd rndR2Z }.

Definition rnd := rounding_float rndZR 53 (-1074).


Definition R2F (r : R) := rnd (r).


Definition R2F64 (r : R) : float64 := F64 (rnd r).


Definition F2R (f : float64) : R := Num f.

Definition SI2R (x : int) : R :=
  match x with
  | Posz n => INR n
  | Negz n => - INR n
  end.

Definition Q2F (x : rat) : float64 :=  F64( R2F (Rdiv ( SI2R (numq x)) (SI2R (denq x)))).

Definition format :=
  generic_format radix2 (FLT_exp (-1074) 53).


Definition rle x y : bool := Rle_dec x y.



Definition Fdiv (x y : R) : R := R2F (Rdiv (R2F x) (R2F y)).

Definition Fplus  (x y : R) : R := R2F (Rplus (R2F x) (R2F y)).
Definition Fsub  (x y : R) : R := R2F (Rminus (R2F x) (R2F y)).
Definition Fmult  (x y : R) : R := R2F (Rmult (R2F x) (R2F y)).
                                         

Definition Fround  (lam v : R) :=
  let v1 := (Rmult (IZR(rndR2Z((R2F v) / (R2F lam))))  lam) in
  let v2 := Rabs (v - v1) in
    if rle v2 0.5
  then v1
    else
      match Rcase_abs v1 with
      | left _ =>  R2F (Rminus (R2F v1) 1)
      | right _ =>  R2F (Rplus (R2F v1) 1)
      end.





Definition Fclamp  (b v : R) : R :=
  if rle (R2F b) (R2F v)
  then  (R2F b)
  else if rle (R2F v) (Ropp(R2F b))
       then (Ropp(R2F b))
       else  (R2F v).



Definition f64exp (x: float64) := F64 (R2F (exp (Num x))).
Definition fln (x: float64) := F64 (R2F (ln (Num x))).


Definition fdiv (x y : float64) : float64 := F64 (R2F (Rdiv (Num x) (Num y))).

Definition fplus  (x y : float64) : float64 := F64 (R2F (Rplus (Num x) (Num y))).
Definition fsub  (x y : float64) : float64 := F64 (R2F (Rminus (Num x) (Num y))).
Definition fmult  (x y : float64) : float64 := F64 (R2F (Rmult (Num x) (Num y))).
                                         

Definition fle (x y : float64) : bool := rle (Num x) (Num y).

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
       then (R2F64 (Ropp(F2R b)))
       else  v.

Definition  fneg (x : float64) : float64 :=(R2F64 (Ropp(F2R x)))
  .


         
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

Local Open Scope ring_scope.



Lemma qle_fle (x : rat) :
  le_rat zeroq x ->
  fle (F64 0) (Q2F x).
 Proof.
 Admitted.
 
 
Lemma fle_mult (v r : float64) :
fle (F64 0) v -> fle (F64 0) r -> fle (fsub v (fmult r v))  (F64 0).
Proof.
Admitted.


Lemma fle_mult_left (x f1 f2 : float64) :
fle f1 f2 -> fle (fmult f1 x) (fmult f2 x).
Proof.
  Admitted.

Lemma fle_ref (x : float64):
  fle x x.
Proof.
Admitted.
  
  Lemma f0_eq :
    (R2F64 0) = (F64 0).
Proof.
Admitted.

Lemma f0_le_exp:
  forall x,
    fle (F64 0) (f64exp x).
Proof.
Admitted.

Definition Fneg (v : R) := R2F (Ropp (R2F v))
  .


Definition Fln (v : R) := R2F (ln (R2F v))
  .

Lemma fle_sub (x v r : float64) :
  fle v r -> fle (fsub x v) (F64 0) -> fle (fsub x r) (F64 0).
Proof.
  Admitted.

Lemma rle_fle (r1 r2 : R) :
rle r1 r2 -> fle (R2F64 r1) (R2F64 r2).
Proof.
  Admitted.

Lemma fle_exp (f1 f2: float64): 
fle f1 f2 -> fle (f64exp f1) (f64exp f2).
Proof.
  Admitted.
  
(*Open Scope ring_scope.

Lemma fle_mult_le  a b c d e1 e2:
 fle (fsub (Q2F a) (fmult e1 (Q2F b))) {| MachineType.Num := 0 |}
 -> fle (fsub (Q2F c) (fmult e2 (Q2F d))) {| MachineType.Num := 0 |}
 -> fle (fsub (Q2F (a * c)) (fmult (fmult e1 e2) (Q2F (b * d)))) {| MachineType.Num := 0 |}.
Proof.
Admitted.


Lemma fle_sum:
  forall (T S : ordType) (eL eR: {prob T*T}) (drawR drawL: (T* T) -> {prob  S * S}) x0 x a,
    fle (fsub (Q2F (eL x0 * drawL x0 x))
              (fmult a (Q2F (eR x0 * drawR x0 x)))) {| MachineType.Num := 0 |}
    ->fle
    (fsub (Q2F (\sum_(x0 <- supp eL) eL x0 * drawL x0 x))
       (fmult a (Q2F (\sum_(x0 <- supp eR) eR x0 * drawR x0 x))))
    {| MachineType.Num := 0 |}.
Proof.
Admitted.


Lemma fexp_mult :
  forall e1 e2, fmult (f64exp (R2F64 (e1))) (f64exp (R2F64 (e2))) = (f64exp (R2F64 (e1 + e2))).
Proof.
Admitted.

Close Scope ring_scope.
*)


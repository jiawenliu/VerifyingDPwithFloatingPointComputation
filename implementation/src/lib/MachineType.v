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


From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.


(*The fixed Floating Point number of 64 bits, with 
52 bits mantissa and 11 bits of exponents*)
Record FFP : Set := FFP64 { Num : R }.

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


Definition R2FFP (r : R) := rnd (r).

Definition format :=
  generic_format radix2 (FLT_exp (-1074) 53).


Definition rle x y : bool := Rle_dec x y.



Definition Fdiv (x y : R) : R := R2FFP (Rdiv (R2FFP x) (R2FFP y)).

Definition Fplus  (x y : R) : R := R2FFP (Rplus (R2FFP x) (R2FFP y)).
Definition Fsub  (x y : R) : R := R2FFP (Rminus (R2FFP x) (R2FFP y)).
Definition Fmult  (x y : R) : R := R2FFP (Rmult (R2FFP x) (R2FFP y)).
                                         

Definition Fround  (lam v : R) :=
  let v1 := (Rmult (IZR(rndR2Z((R2FFP v) / (R2FFP lam))))  lam) in
  let v2 := Rabs (v - v1) in
    if rle v2 0.5
  then v1
    else
      match Rcase_abs v1 with
      | left _ =>  R2FFP (Rminus (R2FFP v1) 1)
      | right _ =>  R2FFP (Rplus (R2FFP v1) 1)
      end.



Definition Fclamp  (b v : R) : R :=
  if rle (R2FFP b) (R2FFP v)
  then  (R2FFP b)
  else if rle (R2FFP v) (Ropp(R2FFP b))
       then (Ropp(R2FFP b))
       else  (R2FFP v).


         
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




Definition Fneg (v : R) := R2FFP (Ropp (R2FFP v))
  .


Definition Fln (v : R) := R2FFP (ln (R2FFP v))
  .







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

From Flocq Require Import Core Bracket Round Operations Div Sqrt  Plus_error.


From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.


(*The fixed Floating Point number of 64 bits, with 
53 bits mentassa and 11 bits of exponents*)
Record FFP : Set := FFP64 { Num : R }.

Variable beta : radix.

Variable fexp : Z -> Z.
Context { valid_exp : Valid_exp fexp }.

Variable prec : Z.
Hypothesis Hprec : (0 < prec)%Z.
Hypothesis fexp_prec :
  forall e, (e - prec <= fexp e)%Z.

Variable rnd : R -> Z.
Context { valid_rnd : Valid_rnd rnd }.

Variable choice : bool -> Z -> location -> Z.
Hypothesis rnd_choice :
  forall x m l,
  inbetween_int m (Rabs x) l ->
  rnd x = cond_Zopp (Rlt_bool x 0) (choice (Rlt_bool x 0) m l).


Definition R2FFP (r : R) := round beta fexp rnd (r).



Definition Fdiv (x y : R) : R := R2FFP (Rdiv (R2FFP x) (R2FFP y)).

Definition Fplus  (x y : R) : R := R2FFP (Rplus (R2FFP x) (R2FFP y)).
Definition Fsub  (x y : R) : R := R2FFP (Rminus (R2FFP x) (R2FFP y)).
Definition Fmult  (x y : R) : R := R2FFP (Rmult (R2FFP x) (R2FFP y)).
                                         

Definition Fround  (v : R) :=
  round beta fexp rnd (v).


Definition rle x y : bool := Rle_dec x y.

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



Definition Rround (v1:R) (v2:R) := v1.



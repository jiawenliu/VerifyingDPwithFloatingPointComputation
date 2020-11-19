(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
      Coq.Arith.Arith Coq.Arith.EqNat Ascii Coq.Bool.Bool
      Coq.Sets.Ensembles
      Coq.Lists.ListSet
      Coq.Reals.Rpower
      Coq.Reals.Rdefinitions.

Require Import Reals Psatz.
From Flocq Require Import Core Plus_error.




Import ListNotations.

From Coq
     Require Import  Structures.Orders Recdef.


From Coq
     Require Import QArith.QArith Structures.Orders Recdef.

From Coq.QArith
     Require Export Qreals.

Require Import Omega.

From Flocq Require Import Core Bracket Round Operations Div Sqrt  Plus_error.


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



Definition div (x y : float beta) :=
  if Zeq_bool (Fnum x) 0 then Float beta 0 0
  else
    let '(m, e, l) := truncate beta fexp (Fdiv fexp (Fabs x) (Fabs y)) in
    let s := xorb (Zlt_bool (Fnum x) 0) (Zlt_bool (Fnum y) 0) in
    Float beta (cond_Zopp s (choice s m l)) e.


Definition FRound  (v : float beta) :=
  round beta fexp rnd (F2R v).

(*Definition evalFBinop (o:binop) (v1: float beta) (v2: float beta) :=
  match o with
  | Plus => F2R(Fplus v1 v2)
  | Sub => F2R(Fminus v1 v2)
  | Mult => F2R(Fmult v1 v2)
  | Div => F2R(div v1 v2)
  | Clamp =>  F2R(v2)
  | Round => (FRound v2)                 
  end.
*)

Definition R2FFP (r : R) := round beta fexp rnd (r).




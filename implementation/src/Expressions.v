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

From Snapv
     Require Export MachineType.

Require Import Omega.

(*Module Type OrderType := Coq.Structures.Orders.OrderedType.

Module ExprOrderedType (V_ordered:OrderType) <: OrderType.
Module V_orderedFacts := OrdersFacts.OrderedTypeFacts (V_ordered).
*)(*
  Definition V := V_ordered.t.
 *)


(**
  Expressions will use binary operators.
  Define them first
 **)


From Flocq Require Import Core Bracket Round Operations Div Sqrt  Plus_error.


Variable beta : radix.



Definition eq_nat_dec : forall (n m : nat), {n =  m} + {n <> m}.
Proof.
  intros.
  Admitted.


Inductive binop : Type := Plus | Sub | Mult | Div | Round | Clamp.

Definition binopEq (b1 : binop) (b2 : binop) :=
  match b1, b2 with
  | Plus, Plus => true
  | Sub,  Sub  => true
  | Mult, Mult => true
  | Div,  Div  => true
  | Round, Round => true
  | Clamp, Clamp => true
  | _,_ => false
end.

(**
  Next define an evaluation function for binary operators on reals.
  Errors are added on the exprression evaluation level later.
 **)


Definition RClamp (v: R) (B: R) : R := v
(*  if (B <? v)
       then B else v.
  match V_ordered.compare B v with
  | Lt => B
  | Eq => B
  | Gt => match (V_ordered.compare v (B)%R) with
  		| Lt =>  (Ropp B)
  		| Eq =>  (Ropp B)
  		| Gt => v
  		end
  end
*)
.
  
              
Definition RRound (v1:R) (v2:R) := v1.



Definition evalBinop (o:binop) (v1:R) (v2:R) :=
  match o with
  | Plus => Rplus v1 v2
  | Sub => Rminus v1 v2
  | Mult => Rmult v1 v2
  | Div => Rdiv v1 v2
  | Clamp => RClamp v1 v2
  | Round => RRound v1 v2                   
  end.


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

Definition evalFBinop (o:binop) (v1: float beta) (v2: float beta) :=
  match o with
  | Plus => F2R(Fplus v1 v2)
  | Sub => F2R(Fminus v1 v2)
  | Mult => F2R(Fmult v1 v2)
  | Div => F2R(div v1 v2)
  | Clamp =>  F2R(v2)
  | Round => (FRound v2)                 
  end.


Lemma binopEq_refl b:
  binopEq b b = true.
Proof.
  case b; auto.
Qed.

Lemma binopEq_compat_eq b1 b2:
  binopEq b1 b2 = true <-> b1 = b2.
Proof.
  split; case b1; case b2; intros; simpl in *; congruence.
Qed.

Lemma binopEq_compat_eq_false b1 b2:
  binopEq b1 b2 = false <-> ~ (b1 = b2).
Proof.
  split; intros neq.
  - hnf; intros; subst. rewrite binopEq_refl in neq.
    congruence.
  - destruct b1; destruct b2; cbv; congruence.
Qed.

(**
   Expressions will use unary operators.
   Define them first
 **)
Inductive unop: Type := Neg | Ln .

Definition unopEq (o1:unop) (o2:unop) :=
  match o1, o2 with
  | Neg, Neg => true
  | Ln, Ln => true
                
  | _ , _ => false
  end.

Lemma unopEq_refl b:
  unopEq b b = true.
Proof.
  case b; auto.
Qed.

Lemma unopEq_sym u1 u2:
  unopEq u1 u2 = unopEq u2 u1.
Proof.
  destruct u1,u2; compute; auto.
Qed.

Lemma unopEq_compat_eq b1 b2:
  unopEq b1 b2 = true <-> b1 = b2.
Proof.
  split; case b1; case b2; intros; simpl in *; congruence.
Qed.

(**
   Define evaluation for unary operators on reals.
   Errors are added in the exprression evaluation level later.
 **)
Definition evalUnop (o:unop) (v:R):=
  match o with
  |Neg => (- v)%R
  |Ln => (ln v)
  (* TODO *)
  end .

(*Definition evalFma (v1:R) (v2:R) (v3:R):=
  evalBinop Plus (evalBinop Mult v1 v2) v3.
*)
(**
  Define exprressions parametric over some value type V.
  Will ease reasoning about different instantiations later.
**)
Inductive expr (V: Type): Type :=
  Var: nat -> expr V
| Const: mType -> V -> expr V
| Unop: unop -> expr V -> expr V
| Binop: binop -> expr V-> expr V-> expr  V                         
.

Fixpoint freeVars (V:Type) (e:expr V) :=
  match e with
  | Var _ x => (set_add  eq_nat_dec x [])
  | Const _ _ => (empty_set nat)
  | Unop u e1 => freeVars e1
  | Binop b e1 e2 => set_union eq_nat_dec (freeVars e1) (freeVars e2)
  end.
 

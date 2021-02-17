(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
      Coq.Arith.Arith Coq.Arith.EqNat Ascii Coq.Bool.Bool
      Coq.Sets.Ensembles
      Coq.Lists.ListSet
      Coq.Reals.Rpower
      Coq.Reals.Rdefinitions.
Import ListNotations.
From Coq.QArith
     Require Export Qreals.

From Snapv.lib
     Require Export MachineType.


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



Definition eq_nat_dec : forall (n m : nat), {n =  m} + {n <> m}.
Proof.
  intros.
  Admitted.

(* The binary operations are mostly regular, except Round and Clamp
Round lam v: do rounding for v in terms of lam.
Clamp B v: do clamping for v, by truncating v to -B and B, if v falls outside of [-B, B]*)
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
  
              



Definition evalBinop (o:binop) (v1:R) (v2:R) :=
  match o with
  | Plus => Rplus v1 v2
  | Sub => Rminus v1 v2
  | Mult => Rmult v1 v2
  | Div => Rdiv v1 v2
  | Clamp => Rclamp v1 v2
  | Round => Rround v1 v2                   
  end.


Definition evalRBinop (o:binop) (v1:R) (v2:R) :=
  match o with
  | Plus => Rplus v1 v2
  | Sub => Rminus v1 v2
  | Mult => Rmult v1 v2
  | Div => Rdiv v1 v2
  | Clamp => Rclamp v1 v2
  | Round => Rround v1 v2                   
  end.

Definition evalFBinop (o:binop) (v1: R) (v2: R) :=
  match o with
  | Plus => (Fplus v1 v2)
  | Sub => (Fsub v1 v2)
  | Mult =>(Fmult v1 v2)
  | Div => (Fdiv v1 v2)
  | Clamp =>  Fclamp v1 v2
  | Round => (Fround v1 v2)                 
  end.

Definition evalfBinop (o:binop) (v1: float64) (v2: float64) :=
  match o with
  | Plus => (fplus v1 v2)
  | Sub => (fsub v1 v2)
  | Mult =>(fmult v1 v2)
  | Div => (fdiv v1 v2)
  | Clamp =>  fclamp v1 v2
  | Round => (fround v1 v2)                 
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
  end .


Definition evalFUnop (o:unop) (v:R):=
  match o with
  |Neg => Fneg v
  |Ln => Fln v
  end .

Definition evalRUnop (o:unop) (v:R):=
  match o with
  |Neg => (Ropp v)
  |Ln => (ln v)
  end .

Definition evalfUnop (o:unop) (v: float64):=
  match o with
  |Neg => fneg v
  |Ln => fln v
  end .

(*Definition evalFma (v1:R) (v2:R) (v3:R):=
  evalBinop Plus (evalBinop Mult v1 v2) v3.
*)
(**
  Define exprressions parametric over some value type V.
  Will ease reasoning about different instantiations later.
**)
Inductive expr : Type :=
  Var: nat -> expr
| Const: R -> expr
| Unop: unop -> expr -> expr
| Binop: binop -> expr -> expr -> expr                         
.

Fixpoint freeVars  (e:expr) :=
  match e with
  | Var x => (set_add  eq_nat_dec x [])
  | Const _  => (empty_set nat)
  | Unop u e1 => freeVars e1
  | Binop b e1 e2 => set_union eq_nat_dec (freeVars e1) (freeVars e2)
  end.
 

(**
  Formalization of the base exprression language for the flover framework
 **)
Require Import Coq.Strings.String Coq.Lists.List Coq.omega.Omega 
      Coq.Arith.Arith Coq.Arith.EqNat Ascii Coq.Bool.Bool.


Import ListNotations.

From Coq
     Require Import  Structures.Orders Recdef.


From Coq
     Require Import QArith.QArith Structures.Orders Recdef.

From Snapv.Infra
     Require Import RealRationalProps RationalSimps Ltacs.

From Snapv.Infra
     Require Export Abbrevs NatSet MachineType.

Require Import Omega.

(**
  Expressions will use binary operators.
  Define them first
**)
Inductive binop : Type := Plus | Sub | Mult | Div | Round | Clamp.

Definition binopEq (b1:binop) (b2:binop) :=
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
  | _ => Rplus v1 v2
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
  |Ln => (/ v)%R
  end .

Definition evalFma (v1:R) (v2:R) (v3:R):=
  evalBinop Plus (evalBinop Mult v1 v2) v3.

(**
  Define exprressions parametric over some value type V.
  Will ease reasoning about different instantiations later.
**)
Inductive expr (V:Type): Type :=
  Var: nat -> expr V
| Const: mType -> V -> expr V
| Unop: unop -> expr V -> expr V
| Binop: binop -> expr V -> expr V -> expr V                                
.

Fixpoint toRExp (e:expr Q) :=
  match e with
  | Var _ v => Var R v
  | Const m n => Const m (Q2R n)
  | Unop o e1 => Unop o (toRExp e1)
  | Binop o e1 e2 => Binop o (toRExp e1) (toRExp e2)
   (* | Cond e1 e2 e3 => Cond (toRExp e1) (toRExp e2) (toRExp e3)*)
  end.

Fixpoint toREval (e:expr R) :=
  match e with
  | Var _ v => Var R v
  | Const _ n => Const REAL n
  | Unop o e1 => Unop o (toREval e1)
  | Binop o e1 e2 => Binop o (toREval e1) (toREval e2)
 (* | Cond e1 e2 e3 => Cond (toREval e1) (toREval e2) (toREval e3) *)
  end.

Definition toRMap (d:expr R -> option mType) (e: expr R) :=
  match d e with
  | Some m => Some REAL
  | None => None
  end.

Arguments toRMap _ _/.

(**
  Define the set of "used" variables of an expression to be the set of variables
  occuring in it
**)
(*
Fixpoint usedVars (V:Type) (e:expr V) :NatSet.t :=
  match e with
  | Var _ x => NatSet.singleton x
  | Const _ _ => NatSet.empty
  | Unop u e1 => usedVars e1
  | Binop b e1 e2 => NatSet.union (usedVars e1) (usedVars e2)
  | Fma e1 e2 e3 => NatSet.union (usedVars e1) (NatSet.union (usedVars e2) (usedVars e3))
  | Downcast _ e1 => usedVars e1
  | Let _ x e1 e2 => NatSet.union (NatSet.singleton x) (NatSet.union (usedVars e1) (usedVars e2))
  | Cond e1 e2 e3 => usedVars e1 ∪ usedVars e2 ∪ usedVars e3
  end.
*)

Fixpoint freeVars (V:Type) (e:expr V) :NatSet.t :=
  match e with
  | Var _ x => NatSet.singleton x
  | Const _ _ => NatSet.empty
  | Unop u e1 => freeVars e1
  | Binop b e1 e2 => NatSet.union (freeVars e1) (freeVars e2)
 (*  | Cond e1 e2 e3 => freeVars e1 ∪ freeVars e2 ∪ freeVars e3 *)
  end.

Module Type OrderType := Coq.Structures.Orders.OrderedType.

Module ExprOrderedType (V_ordered:OrderType) <: OrderType.
  Module V_orderedFacts := OrdersFacts.OrderedTypeFacts (V_ordered).

  Definition V := V_ordered.t.
  Definition t := expr V.

  Open Scope positive_scope.

  Fixpoint exprCompare (e1:expr V) (e2:expr V) :=
    match e1, e2 with
    |Var _ n1, Var _ n2 => Nat.compare n1 n2
    |Var _ n1, _ => Lt
    | Const m1 v1, Const m2 v2 =>
      if mTypeEq m1 m2
      then V_ordered.compare v1 v2
      else
        match m1, m2 with
        | F w1 f1, F w2 f2 =>
          match w1 ?= w2 with
          |Eq => (f1 ?= f2)%N
          | c => c
          end
        | F w f, _ => Lt
        | _, F w f => Gt
        | _, _ => (if morePrecise m1 m2 then Lt else Gt)
        end
    | Const _ _, Var _ _ => Gt
    | Const _ _, _ => Lt
    | Unop u1 e1, Unop u2 e2 =>
      if unopEq u1 u2
     then  exprCompare e1 e2
     else (if unopEq u1 Neg then Lt else  Gt)
    | Unop _ _, Var _ _ => Gt
    | Unop _ _, Const _ _ => Gt
    | Unop _ _, _ => Lt
    | Binop b1 e11 e12, Binop b2 e21 e22 =>
      let res := match b1, b2 with
                 | Plus, Plus => Eq
                 | Plus, _ => Lt
                 | Sub, Sub => Eq
                 | Sub, Plus => Gt
                 | Sub, _ => Lt
                 | Mult, Mult => Eq
                 | Mult, Plus => Gt
                 |Mult, Sub => Gt
                 | Mult, _ => Lt
                 | Div, Div => Eq
                 | Div, Round => Lt
                 |Div, Clamp => Lt
                 | Div, _ => Gt
                 | Round, Round => Eq
                 | Round, Clamp => Lt                                    
                 | Round, _ => Gt
                 | Clamp, Clamp => Eq
                 | Clamp, _ => Gt                               
                 end
      in
      match res with
      | Eq =>
        match exprCompare e11 e21 with
        | Eq => exprCompare e12 e22
        | Lt => Lt
        | Gt => Gt
        end
      | _ => res
      end
    | Binop _ _ _, Var _ _ => Gt
    | Binop _ _ _, Const _ _ => Gt
    | Binop _ _ _, Unop _ _ => Gt
    (*
    | Let _ _ _ _, _ => Lt
    | Cond e11 e12 e13, Cond e21 e22 e23 =>
      match exprCompare e11 e21 with
      | Eq => match exprCompare e12 e22 with
             | Eq => exprCompare e13 e23
             | r => r
             end
      | r => r
      end
    | Cond _ _ _, _ => Gt
     *)
    end.

  Lemma exprCompare_refl e: exprCompare e e = Eq.
  Proof.
    induction e; simpl.
    - apply Nat.compare_refl.
    - rewrite mTypeEq_refl. apply V_orderedFacts.compare_refl.
    - rewrite unopEq_refl; auto.
    - rewrite IHe1, IHe2. destruct b; auto.
   (* - now rewrite IHe1, IHe2, IHe3.
    - rewrite mTypeEq_refl; auto.
    - now rewrite mTypeEq_refl, Nat.compare_refl, IHe1, IHe2.
    (* - now rewrite IHe1, IHe2, IHe3. *) *)
  Qed.

  Lemma exprCompare_eq_trans e1 :
    forall e2 e3,
      exprCompare e1 e2 = Eq ->
      exprCompare e2 e3 = Eq ->
      exprCompare e1 e3 = Eq.
  Proof.
    induction e1; intros * eq12 eq23;
      destruct e2; destruct e3; simpl in *; try congruence.
    - rewrite Nat.compare_eq_iff in *; subst; auto.
    - destruct (mTypeEq m m0) eqn:?;
               [ destruct (mTypeEq m0 m1) eqn:?; type_conv | ].
      + rewrite mTypeEq_refl.
        rewrite V_orderedFacts.compare_eq_iff in *;
          eapply V_orderedFacts.eq_trans; eauto.
      + rewrite <- mTypeEq_compat_eq_false in Heqb0; rewrite Heqb0.
        destruct m0; destruct m1; auto.
      + destruct (mTypeEq m m1) eqn:?; type_conv;
          destruct m0; destruct m1; simpl in *; try congruence.
        * destruct (w0 ?= w) eqn:?; destruct (f0 ?= f)%N eqn:?;
                   try congruence.
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct m; try congruence.
          destruct (w1 ?= w) eqn:?; destruct (f1 ?= f)%N eqn:?;
                   try congruence.
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
    - destruct (unopEq u u0) eqn:?;
               destruct (unopEq u0 u1) eqn:?;
               try rewrite unopEq_compat_eq in *; subst;
        try rewrite unopEq_refl;
        try congruence.
      + eapply IHe1; eauto.
      +auto. destruct (unopEq u0 Neg); congruence.
      + destruct (unopEq u Neg); congruence.
      + destruct (unopEq u Neg); congruence.
    - destruct b; destruct b0; try congruence;
        destruct b1; try congruence;
          destruct (exprCompare e1_1 e2_1) eqn:?;
                   destruct (exprCompare e2_1 e3_1) eqn:?;
                   try congruence; try erewrite IHe1_1; eauto.      
   (*  - destruct (exprCompare e1_1 e2_1) eqn:?;
        destruct (exprCompare e2_1 e3_1) eqn:?;
      destruct (exprCompare e1_2 e2_2) eqn:?;
        destruct (exprCompare e2_2 e3_2) eqn:?;
      try congruence; try erewrite IHe1_1, IHe1_2; eauto.
    - destruct (mTypeEq m m0) eqn:?;
               destruct (mTypeEq m0 m1) eqn:?;
               type_conv;
        try rewrite mTypeEq_refl.
      + eapply IHe1; eauto.
      + destruct (mTypeEq m0 m1) eqn:?; type_conv; congruence.
      + destruct (mTypeEq m m1) eqn:?; type_conv; congruence.
      + destruct (mTypeEq m m1) eqn:?; type_conv; try congruence;
          destruct (morePrecise _ m0); try congruence;
            destruct m0,m1;
            cbn in *; try congruence.
        * destruct (w0 ?= w) eqn:?; destruct (f0 ?= f)%N eqn:?; try congruence.
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct (w0 ?= w) eqn:?; destruct (f0 ?= f)%N eqn:?; try congruence.
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct m; try congruence.
          destruct (w1 ?= w) eqn:?; destruct (f1 ?= f)%N eqn:?; try congruence.
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct m; try congruence.
          destruct (w1 ?= w) eqn:?; destruct (f1 ?= f)%N eqn:?; try congruence.
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
    - destruct (mTypeEq m m0) eqn:?;
               destruct (mTypeEq m0 m1) eqn:?;
               type_conv;
        try rewrite mTypeEq_refl.
      + destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        apply nat_compare_eq in Hn. subst.
        destruct (n0 ?= n1)%nat eqn:?;
          destruct (exprCompare e1_1 e2_1) eqn:?;
          destruct (exprCompare e2_1 e3_1) eqn:?; try discriminate.
        erewrite IHe1_1; eauto.
      + destruct (mTypeEq m0 m1) eqn:?; type_conv; try congruence.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        apply nat_compare_eq in Hn. subst.
        destruct (n0 ?= n1)%nat eqn:?;
          destruct (exprCompare e1_1 e2_1) eqn:?;
          destruct (exprCompare e2_1 e3_1) eqn:?; congruence.
      + destruct (mTypeEq m m1) eqn:?; type_conv; try congruence.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        apply nat_compare_eq in Hn. subst.
        destruct (n0 ?= n1)%nat eqn:?; congruence.
      + destruct (mTypeEq m m1) eqn:?; type_conv;
          destruct (n ?= n0)%nat eqn:Hn; try discriminate;
          apply nat_compare_eq in Hn; subst;
          destruct (n0 ?= n1)%nat eqn:?; try congruence;
          destruct m0,m1;
          cbn in *; try congruence.
        * destruct (w0 ?= w) eqn:?; destruct (f0 ?= f)%N eqn:?; try congruence.
          apply Ndec.Pcompare_Peqb in Heqc0;
            apply N.compare_eq in Heqc1.
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct m; try congruence.
          destruct (w1 ?= w) eqn:?; destruct (f1 ?= f)%N eqn:?; try congruence.
          apply Ndec.Pcompare_Peqb in Heqc0;
            apply N.compare_eq in Heqc1.
            rewrite Pos.eqb_eq in *; subst; congruence.
            (*
    - destruct (exprCompare e1_1 e2_1) eqn:?;
        destruct (exprCompare e2_1 e3_1) eqn:?;
      destruct (exprCompare e1_2 e2_2) eqn:?;
        destruct (exprCompare e2_2 e3_2) eqn:?;
      try congruence; try erewrite IHe1_1, IHe1_2; eauto.
*)
*)
  Qed.

  Lemma exprCompare_antisym e1:
    forall e2,
      exprCompare e1 e2 = CompOpp
                            (exprCompare e2 e1).
  Proof.
    induction e1; destruct e2; simpl; try auto.
    - apply Nat.compare_antisym.
    - rewrite mTypeEq_sym.
      destruct (mTypeEq m0 m) eqn:?;
               type_conv; try congruence; try rewrite mTypeEq_refl.
      + apply V_orderedFacts.compare_antisym.
      + destruct (morePrecise m m0) eqn:?;
                 destruct (morePrecise m0 m) eqn:?;
                 try (split; auto; fail).
        * destruct m, m0; cbn in *; try congruence.
          rewrite N.compare_antisym.
          rewrite Pos.compare_antisym.
          rewrite Pos.leb_compare in *.
          destruct (w0 ?= w); simpl in *; try congruence.
        * destruct m, m0; unfold morePrecise in *; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
   - (*rewrite IHe1_1, IHe1_2.*) rewrite unopEq_sym.
      destruct (unopEq u0 u) eqn:?;
               try rewrite unopEq_compat_eq in *; subst;
        try rewrite unopEq_refl, IHe1; try (apply IHe1).
      destruct (unopEq u Neg) eqn:?; try rewrite unopEq_compat_eq in *;
        destruct (unopEq u0 Neg) eqn:?; try rewrite unopEq_compat_eq in *;
        subst; simpl in *; try congruence.
      destruct u, u0; simpl in *; congruence.
    - destruct b, b0; simpl; try (split; auto; fail);
      destruct (exprCompare e1_1 e2_1) eqn:first_comp;
      rewrite IHe1_1 in *; simpl in *;
        rewrite CompOpp_iff in first_comp;
        rewrite first_comp; simpl; try auto.
  Qed. 
 (*    - destruct (exprCompare e1_1 e2_1) eqn:first_comp;
      destruct (exprCompare e1_2 e2_2) eqn:second_comp;
      rewrite IHe1_1, IHe1_2 in *; simpl in *;
        rewrite CompOpp_iff in first_comp;
        rewrite CompOpp_iff in second_comp;
        rewrite first_comp, second_comp; simpl; try auto.
    - rewrite mTypeEq_sym.
      destruct (mTypeEq m0 m) eqn:?;
               type_conv; try auto.
      + destruct (morePrecise m m0) eqn:?;
                 destruct (morePrecise m0 m) eqn:?;
                 try (split; auto; fail).
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                  destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
    - rewrite mTypeEq_sym.
      destruct (mTypeEq m0 m) eqn:?;
               type_conv; try auto.
      + rewrite Nat.compare_antisym.
        destruct (n0 ?= n)%nat; cbn; auto.
        destruct (exprCompare e1_1 e2_1) eqn:first_comp;
          destruct (exprCompare e1_2 e2_2) eqn:second_comp;
          rewrite IHe1_1, IHe1_2 in *;
          rewrite CompOpp_iff in first_comp;
          rewrite CompOpp_iff in second_comp;
          rewrite first_comp, second_comp; cbn; auto.
      + rewrite Nat.compare_antisym.
        destruct (n0 ?= n)%nat; cbn; auto.
        destruct (morePrecise m m0) eqn:?;
                 destruct (morePrecise m0 m) eqn:?;
                 try (split; auto; fail).
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
        * destruct m, m0; simpl in *; try congruence.
          setoid_rewrite N.compare_antisym at 2.
          setoid_rewrite Pos.compare_antisym at 2.
          destruct (w ?= w0) eqn:?;
                   destruct (f ?= f0)%N eqn:?; simpl; auto.
          (*
    - destruct (exprCompare e1_1 e2_1) eqn:first_comp;
      destruct (exprCompare e1_2 e2_2) eqn:second_comp;
      rewrite IHe1_1, IHe1_2 in *; simpl in *;
        rewrite CompOpp_iff in first_comp;
        rewrite CompOpp_iff in second_comp;
        rewrite first_comp, second_comp; simpl; try auto.
*)
  Qed.*)

  Lemma exprCompare_eq_sym e1 e2:
      exprCompare e1 e2 = Eq <-> exprCompare e2 e1 = Eq.
  Proof.
    now split; intros H; rewrite exprCompare_antisym; rewrite H.
  Qed.

  Lemma exprCompare_lt_eq_is_lt e1:
    forall e2 e3,
      exprCompare e1 e2 = Lt -> exprCompare e2 e3 = Eq -> exprCompare e1 e3 = Lt.
  Proof.
    induction e1; intros * compare_lt compare_eq; destruct e2; simpl in *;
      destruct e3; try congruence.
    - rewrite Nat.compare_eq_iff in compare_eq; subst; auto.
    - destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq  m0 m1) eqn:?.
      + pose proof (V_orderedFacts.compare_compat). unfold Proper in H.
        apply V_orderedFacts.compare_eq_iff in compare_eq.
        specialize (H v v (V_orderedFacts.eq_refl v) v0 v1 compare_eq).
        type_conv; rewrite mTypeEq_refl, <- H; auto.
      + rewrite mTypeEq_compat_eq in Heqb; subst.
        rewrite Heqb0. type_conv; subst. destruct m0, m1; try congruence;
        try destruct (morePrecise _ _) eqn:?; try congruence.
        destruct (w ?= w0) eqn:?; destruct (f ?= f0)%N eqn:?; try congruence.
        apply Ndec.Pcompare_Peqb in Heqc;
          apply N.compare_eq in Heqc0;
          rewrite Pos.eqb_eq in *; subst; congruence.
      + rewrite mTypeEq_compat_eq in Heqb0; subst.
        rewrite Heqb; destruct (morePrecise m m1) eqn:?; congruence.
      + destruct (mTypeEq m m1); type_conv.
        * destruct (morePrecise m0 m1);  destruct m, m0, m1; try congruence;
          destruct (w0 ?= w1) eqn:?; try congruence;
            apply Ndec.Pcompare_Peqb in Heqc;
              apply N.compare_eq in compare_eq;
              rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct (morePrecise m m1); destruct (morePrecise m0 m1);
            destruct m, m0, m1; try congruence;
          destruct (w0 ?= w1) eqn:?; try congruence;
            apply Ndec.Pcompare_Peqb in Heqc;
              apply N.compare_eq in compare_eq;
              rewrite Pos.eqb_eq in *; subst; congruence.
    - destruct (unopEq u u0) eqn:?; destruct (unopEq u0 u1) eqn:?;
               try rewrite unopEq_compat_eq in *; subst;
        try rewrite unopEq_refl; try auto; try congruence.
      + eapply IHe1; eauto.
      + destruct (unopEq u0 Neg); congruence.
      + destruct (unopEq u Neg); try congruence.
        destruct (unopEq u u1); congruence.
      + destruct (unopEq u0 Neg); congruence.
    - destruct b; destruct b0; try congruence;
        destruct b1; try congruence;
          destruct (exprCompare e1_1 e2_1) eqn:?;
               destruct (exprCompare e2_1 e3_1) eqn:?;
               try congruence;
          try (erewrite IHe1_1; eauto; fail "");
          try erewrite exprCompare_eq_trans; eauto.
  Qed.

(*  - destruct (exprCompare e1_1 e2_1) eqn:?;
        destruct (exprCompare e2_1 e3_1) eqn:?;
        try congruence;
        try (erewrite IHe1_1; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
      destruct (exprCompare e1_2 e2_2) eqn:?;
        destruct (exprCompare e2_2 e3_2) eqn:?;
        try congruence;
        try (erewrite IHe1_2; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
    - destruct (mTypeEq m m0) eqn:?;
               destruct (mTypeEq m0 m1) eqn:?.
      + type_conv; subst. rewrite mTypeEq_refl. eapply IHe1; eauto.
      + rewrite mTypeEq_compat_eq in Heqb; subst.
        rewrite Heqb0. type_conv; subst. destruct m0, m1; try congruence;
        try destruct (morePrecise _ _) eqn:?; try congruence.
        destruct (w ?= w0) eqn:?; try congruence;
          apply Ndec.Pcompare_Peqb in Heqc;
          apply N.compare_eq in compare_eq;
          rewrite Pos.eqb_eq in *; subst; congruence.
      + rewrite mTypeEq_compat_eq in Heqb0; subst.
        rewrite Heqb; destruct (morePrecise m m1) eqn:?; congruence.
      + destruct (mTypeEq m m1); type_conv.
        * destruct (morePrecise m0 m1);  destruct m, m0, m1; try congruence;
            destruct (w0 ?= w1) eqn:?; try congruence;
            apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in compare_eq;
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct (morePrecise m m1); destruct (morePrecise m0 m1);
            destruct m, m0, m1; try congruence;
            destruct (w0 ?= w1) eqn:?; try congruence;
            apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in compare_eq;
            rewrite Pos.eqb_eq in *; subst; congruence.
    - destruct (mTypeEq m m0) eqn:?;
               destruct (mTypeEq m0 m1) eqn:?.
      + type_conv; subst. rewrite mTypeEq_refl.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        * apply nat_compare_eq in Hn. subst.
          destruct (n0 ?= n1)%nat eqn:?; try discriminate.
          destruct (exprCompare e1_1 e2_1) eqn:?;
            destruct (exprCompare e2_1 e3_1) eqn:?;
            try congruence;
            try (erewrite IHe1_1; eauto; fail "").
          erewrite (exprCompare_eq_trans e1_1); eauto.
        * destruct (n0 ?= n1)%nat eqn:Hn1; try discriminate.
          apply nat_compare_eq in Hn1. subst.
          now rewrite Hn.
      + rewrite mTypeEq_compat_eq in Heqb; subst.
        rewrite Heqb0. type_conv.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        * apply nat_compare_eq in Hn. subst.
          destruct (n0 ?= n1)%nat eqn:?; try discriminate.
          destruct m0, m1; try discriminate.
          destruct (w ?= w0) eqn:?, (f ?= f0)%N eqn:?; try discriminate.
          apply Ndec.Pcompare_Peqb in Heqc0;
            apply N.compare_eq in Heqc1;
            rewrite Pos.eqb_eq in *; subst; congruence.
        * destruct (n0 ?= n1)%nat eqn:Hn1; try discriminate.
          apply nat_compare_eq in Hn1. subst.
          now rewrite Hn.
      + rewrite mTypeEq_compat_eq in Heqb0; subst.
        rewrite Heqb. type_conv.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        * apply nat_compare_eq in Hn. subst.
          destruct (n0 ?= n1)%nat eqn:?; try discriminate.
          auto.
        * destruct (n0 ?= n1)%nat eqn:Hn1; try discriminate.
          apply nat_compare_eq in Hn1. subst.
          now rewrite Hn.
      + destruct (mTypeEq m m1); type_conv;
          destruct (n ?= n0)%nat eqn:Hn;
          destruct (n0 ?= n1)%nat eqn:Hn1; try discriminate;
          destruct m0, m1; try discriminate;
          destruct (w ?= w0) eqn:?, (f ?= f0)%N eqn:?; try discriminate;
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
        (*
    - destruct (exprCompare e1_1 e2_1) eqn:?;
        destruct (exprCompare e2_1 e3_1) eqn:?;
        try congruence;
        try (erewrite IHe1_1; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
      destruct (exprCompare e1_2 e2_2) eqn:?;
        destruct (exprCompare e2_2 e3_2) eqn:?;
        try congruence;
        try (erewrite IHe1_2; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
*)
  Qed.
  *)
    
  Lemma exprCompare_eq_lt_is_lt e1:
    forall e2 e3,
      exprCompare e1 e2 = Eq -> exprCompare e2 e3 = Lt -> exprCompare e1 e3 = Lt.
  Proof.
    induction e1; intros * compare_eq compare_lt; destruct e2; simpl in *;
      destruct e3; try congruence.
    - rewrite Nat.compare_eq_iff in compare_eq; subst; auto.
    - destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq  m0 m1) eqn:?.
      + pose proof (V_orderedFacts.compare_compat). unfold Proper in H.
        apply V_orderedFacts.compare_eq_iff in compare_eq.
        specialize (H v v0 compare_eq v1 v1 (V_orderedFacts.eq_refl v1)).
        type_conv; rewrite mTypeEq_refl, H; auto.
      + rewrite mTypeEq_compat_eq in Heqb; subst.
        rewrite Heqb0. destruct (morePrecise m0 m1) eqn:?; congruence.
      + rewrite mTypeEq_compat_eq in Heqb0; subst;
        try destruct (morePrecise _ _) eqn:?; try congruence;
        destruct m, m1; try congruence; type_conv;
          destruct (w ?= w0) eqn:case1;
                   destruct (f ?= f0)%N eqn:case2;
                   try congruence;
            apply Ndec.Pcompare_Peqb in case1;
            apply N.compare_eq in case2;
            rewrite Pos.eqb_eq in *; subst; congruence.
      + type_conv; subst.
        destruct (mTypeEq m m1); type_conv; destruct m, m0, m1; try congruence;
          try (repeat destruct (morePrecise _ _)); try congruence;
          destruct (w ?= w0) eqn:case1;
                   destruct (f ?= f0)%N eqn:case2;
                   try congruence;
            apply Ndec.Pcompare_Peqb in case1;
            apply N.compare_eq in case2;
            rewrite Pos.eqb_eq in *; subst; congruence.
    - destruct (unopEq u u0) eqn:?; destruct (unopEq u0 u1) eqn:?;
               try rewrite unopEq_compat_eq in *; subst;
        try rewrite unopEq_refl; try auto; try congruence.
      + eapply IHe1; eauto.
      + rewrite Heqb0. destruct (unopEq u0 Neg); congruence.
      + destruct (unopEq u Neg); congruence.
      + destruct (unopEq u Neg); congruence.
    - destruct b; destruct b0;
        destruct b1; try congruence;
          destruct (exprCompare e1_1 e2_1) eqn:?;
                   destruct (exprCompare e2_1 e3_1) eqn:?;
                   try congruence;
          try (erewrite IHe1_1; eauto; fail "");
          try erewrite exprCompare_eq_trans; eauto.
  Qed.
  (*- destruct (exprCompare e1_1 e2_1) eqn:?;
        destruct (exprCompare e2_1 e3_1) eqn:?;
        try congruence;
        try (erewrite IHe1_1; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
      destruct (exprCompare e1_2 e2_2) eqn:?;
        destruct (exprCompare e2_2 e3_2) eqn:?;
        try congruence;
        try (erewrite IHe1_2; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
    - destruct (mTypeEq m m0) eqn:?;
               destruct (mTypeEq m0 m1) eqn:?.
      + type_conv; subst. rewrite mTypeEq_refl. eapply IHe1; eauto.
      + rewrite mTypeEq_compat_eq in Heqb; subst.
        rewrite Heqb0.
        destruct (morePrecise m0 m1); congruence.
      + rewrite mTypeEq_compat_eq in Heqb0; subst.
        rewrite Heqb; destruct m, m1; try (repeat destruct (morePrecise _ _)); try congruence.
          destruct (w ?= w0) eqn:case1;
                   destruct (f ?= f0)%N eqn:case2;
                   try congruence;
            apply Ndec.Pcompare_Peqb in case1;
            apply N.compare_eq in case2;
            rewrite Pos.eqb_eq in *; subst; cbn in *;
              repeat rewrite Pos.eqb_refl in *; simpl in *; try congruence.
          rewrite N.eqb_neq in *; congruence.
      + type_conv; subst.
        destruct (mTypeEq m m1); type_conv; destruct m, m0, m1; try congruence;
          try (repeat destruct (morePrecise _ _)); try congruence;
          destruct (w ?= w0) eqn:case1;
                   destruct (f ?= f0)%N eqn:case2;
                   try congruence;
            apply Ndec.Pcompare_Peqb in case1;
            apply N.compare_eq in case2;
            rewrite Pos.eqb_eq in *; subst; cbn in *;
              repeat rewrite Pos.eqb_refl in *; simpl in *; congruence.
    - destruct (mTypeEq m m0) eqn:?;
               destruct (mTypeEq m0 m1) eqn:?.
      + type_conv; subst. rewrite mTypeEq_refl.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        * apply nat_compare_eq in Hn. subst.
          destruct (n0 ?= n1)%nat eqn:?; try congruence.
          destruct (exprCompare e1_1 e2_1) eqn:?;
            destruct (exprCompare e2_1 e3_1) eqn:?;
            try congruence;
            try (erewrite IHe1_1; eauto; fail "").
          erewrite (exprCompare_eq_trans e1_1); eauto.
      + rewrite mTypeEq_compat_eq in Heqb; subst.
        rewrite Heqb0. type_conv.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        apply nat_compare_eq in Hn; subst.
          destruct (n0 ?= n1)%nat eqn:?; congruence.
      + rewrite mTypeEq_compat_eq in Heqb0; subst.
        rewrite Heqb. type_conv.
        destruct (n ?= n0)%nat eqn:Hn; try discriminate.
        destruct m, m1; try discriminate.
        destruct (w ?= w0) eqn:?, (f ?= f0)%N eqn:?; try discriminate.
        apply Ndec.Pcompare_Peqb in Heqc;
          apply N.compare_eq in Heqc0;
          rewrite Pos.eqb_eq in *; subst; congruence.
      + destruct (mTypeEq m m1); type_conv;
          destruct (n ?= n0)%nat eqn:Hn;
          (* destruct (n0 ?= n1)%nat eqn:Hn1; try discriminate; *)
          destruct m, m0; try discriminate;
          destruct (w ?= w0) eqn:?, (f ?= f0)%N eqn:?; try discriminate;
          apply Ndec.Pcompare_Peqb in Heqc;
            apply N.compare_eq in Heqc0;
            rewrite Pos.eqb_eq in *; subst; congruence.
        (*
    - destruct (exprCompare e1_1 e2_1) eqn:?;
        destruct (exprCompare e2_1 e3_1) eqn:?;
        try congruence;
        try (erewrite IHe1_1; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
      destruct (exprCompare e1_2 e2_2) eqn:?;
        destruct (exprCompare e2_2 e3_2) eqn:?;
        try congruence;
        try (erewrite IHe1_2; eauto; fail "");
        try erewrite exprCompare_eq_trans; eauto.
*)
  Qed.
*)
  Definition eq e1 e2 :=
    exprCompare e1 e2 = Eq.

  Definition lt (e1:expr V) (e2: expr V):=
    exprCompare e1 e2 = Lt.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - unfold Irreflexive.
      unfold Reflexive.
      intros x; unfold complement.
      intros lt_x.
      induction x; unfold lt in *; simpl in lt_x.
      + rewrite PeanoNat.Nat.compare_refl in lt_x. congruence.
      + rewrite mTypeEq_refl, V_orderedFacts.compare_refl in *;
          congruence.
      + rewrite unopEq_refl in *; simpl in *.
        apply IHx; auto.
      + destruct b;
          destruct (exprCompare x1 x1) eqn:?; try congruence.
(*      + destruct (exprCompare x1 x1) eqn:?; destruct (exprCompare x2 x2) eqn:?; try congruence.
      + rewrite mTypeEq_refl in lt_x.
        apply IHx; auto.
      + rewrite mTypeEq_refl in *.
        rewrite Nat.compare_refl in *.
        destruct (exprCompare x1 x1) eqn:?;
                 destruct (exprCompare x2 x2) eqn:?; congruence.
        (*
      + destruct (exprCompare x1 x1) eqn:?;
                 destruct (exprCompare x2 x2) eqn:?;
                 destruct (exprCompare x3 x3) eqn:?; congruence.
*)*)
    - unfold Transitive.
      intros e1. unfold lt.
      induction e1; intros * lt_e1_e2 lt_e2_e3;
        simpl in *; destruct y; destruct z;
          simpl in *; try auto; try congruence.
      + rewrite <- nat_compare_lt in *. omega.
      + destruct (mTypeEq m m0) eqn:?;
                 destruct (mTypeEq m0 m1) eqn:?.
        * type_conv;
            rewrite mTypeEq_refl, V_orderedFacts.compare_lt_iff in *;
            eapply V_orderedFacts.lt_trans; eauto.
        * rewrite mTypeEq_compat_eq in Heqb; subst.
          rewrite Heqb0. assumption.
        * rewrite mTypeEq_compat_eq in Heqb0; subst.
          rewrite Heqb; assumption.
        * destruct (mTypeEq m m1) eqn:?.
          { rewrite mTypeEq_compat_eq in Heqb1; subst.
            destruct (morePrecise m0 m1) eqn:?;
                     destruct (morePrecise m1 m0) eqn:?;
                     destruct m0, m1;
                     try congruence;
            try pose proof (morePrecise_antisym _ _ Heqb1 Heqb2);
            type_conv; try congruence; unfold morePrecise in *; simpl in *;
              try congruence;
              rewrite Pos.compare_antisym in lt_e2_e3;
              rewrite N.compare_antisym in lt_e2_e3;
              destruct (w0 ?= w) eqn:case1;
                destruct (f0 ?= f)%N eqn:case2;
                cbn in *;
                try congruence. }
          { destruct (morePrecise m m0) eqn:?;
                     destruct (morePrecise m0 m1) eqn:?;
                     try congruence.
            - erewrite morePrecise_trans; eauto;
                type_conv; subst;
                  destruct m, m0, m1; try congruence.
              destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                try (apply Ndec.Pcompare_Peqb in case_w0);
                try (apply Ndec.Pcompare_Peqb in case_w1);
                try rewrite Pos.eqb_eq in *;
                subst;
                try congruence;
                try rewrite case_w0;
                try rewrite case_w1; try auto;
                try rewrite Pos.compare_refl;
                [ rewrite N.compare_lt_iff in *;
                  eapply N.lt_trans; eauto  | ].
              assert (w ?= w1 = Lt).
              { rewrite Pos.compare_lt_iff in *;
                  eapply Pos.lt_trans; eauto. }
              rewrite H; auto.
            - type_conv; subst; destruct m, m0, m1; try congruence.
              destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                try (apply Ndec.Pcompare_Peqb in case_w0);
                try (apply Ndec.Pcompare_Peqb in case_w1);
                try rewrite Pos.eqb_eq in *;
                subst;
                try congruence;
                try rewrite case_w0;
                try rewrite case_w1; try auto;
                try rewrite Pos.compare_refl;
                [ rewrite N.compare_lt_iff in *;
                  eapply N.lt_trans; eauto  | ].
              assert (w ?= w1 = Lt).
              { rewrite Pos.compare_lt_iff in *;
                  eapply Pos.lt_trans; eauto. }
              rewrite H; auto.
            - type_conv; subst; destruct m, m0, m1; try congruence.
              destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                try (apply Ndec.Pcompare_Peqb in case_w0);
                try (apply Ndec.Pcompare_Peqb in case_w1);
                try rewrite Pos.eqb_eq in *;
                subst;
                try congruence;
                try rewrite case_w0;
                try rewrite case_w1; try auto;
                try rewrite Pos.compare_refl;
                [ rewrite N.compare_lt_iff in *;
                  eapply N.lt_trans; eauto  | ].
              assert (w ?= w1 = Lt).
              { rewrite Pos.compare_lt_iff in *;
                  eapply Pos.lt_trans; eauto. }
              rewrite H; auto.
            - type_conv; subst; destruct m, m0, m1; try congruence.
              destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                try (apply Ndec.Pcompare_Peqb in case_w0);
                try (apply Ndec.Pcompare_Peqb in case_w1);
                try rewrite Pos.eqb_eq in *;
                subst;
                try congruence;
                try rewrite case_w0;
                try rewrite case_w1; try auto;
                try rewrite Pos.compare_refl;
                [ rewrite N.compare_lt_iff in *;
                  eapply N.lt_trans; eauto  | ].
              assert (w ?= w1 = Lt).
              { rewrite Pos.compare_lt_iff in *;
                  eapply Pos.lt_trans; eauto. }
              rewrite H; auto. }
      + destruct (unopEq u u0) eqn:?;
                 destruct (unopEq u0 u1) eqn:?;
                 try rewrite unopEq_compat_eq in *; subst;
          [ destruct (exprCompare e1 y) eqn:?; try congruence;
            rewrite unopEq_refl;
            eapply IHe1; eauto
          | destruct (unopEq u0 Neg) eqn:?; try congruence;
            rewrite unopEq_compat_eq in *; subst
          | |].
        * rewrite Heqb0; auto.
        * destruct (unopEq u Neg) eqn:?; try congruence; rewrite unopEq_compat_eq in *; subst.
          rewrite Heqb; auto.
        * destruct (unopEq u u1) eqn:?; try congruence.
          rewrite unopEq_compat_eq in Heqb1; subst.
          destruct (unopEq u1 Neg) eqn:?; try congruence;
            destruct (unopEq u0 Neg) eqn:?; try congruence;
            rewrite unopEq_compat_eq in *; subst.
          simpl in *; congruence.
      + destruct b; destruct b0; destruct b1; try congruence;
          destruct (exprCompare e1_1 y1) eqn:?; try congruence;
          destruct (exprCompare y1 z1) eqn:?; try congruence;
          try (erewrite exprCompare_eq_trans; eauto; fail);
          try (erewrite exprCompare_eq_lt_is_lt; eauto; fail);
          try (erewrite exprCompare_lt_eq_is_lt; eauto; fail);
          try (erewrite IHe1_1; eauto).
  Qed.

  (*+ destruct (exprCompare e1_1 y1) eqn:?; try congruence;
          destruct (exprCompare y1 z1) eqn:?; try congruence;
          try (erewrite exprCompare_eq_lt_is_lt; eauto; fail);
          try (erewrite exprCompare_lt_eq_is_lt; eauto; fail);
          try (erewrite IHe1_1; eauto; fail).
        apply (exprCompare_eq_trans _ _ _ Heqc) in Heqc0;
          rewrite Heqc0.
        destruct (exprCompare e1_2 y2) eqn:?; try congruence;
          destruct (exprCompare y2 z2) eqn:?; try congruence;
          try (erewrite exprCompare_eq_trans; eauto; fail);
          try (erewrite exprCompare_eq_lt_is_lt; eauto; fail);
          try (erewrite exprCompare_lt_eq_is_lt; eauto; fail);
          try (erewrite IHe1_2; eauto).
      + destruct (mTypeEq m m0) eqn:?;
                 destruct (mTypeEq m0 m1) eqn:?;
                 [type_conv; subst; rewrite mTypeEq_refl | | | ].
        * eapply IHe1; eauto.
        * rewrite mTypeEq_compat_eq in Heqb; subst.
          rewrite Heqb0; destruct (morePrecise m0 m1); congruence.
        * rewrite mTypeEq_compat_eq in Heqb0; subst.
          rewrite Heqb. destruct (morePrecise m m1); congruence.
        * destruct (mTypeEq m m1) eqn:?.
          { rewrite mTypeEq_compat_eq in Heqb1; subst.
            destruct (morePrecise m1 m0) eqn:prec1;
                     destruct (morePrecise m0 m1) eqn:prec2;
                     destruct m1, m0;
                     try rewrite mTypeEq_refl in *; try congruence;
                       try pose proof (morePrecise_antisym _ _ prec1 prec2);
                       type_conv; try congruence;
                         simpl in *; try congruence;
            rewrite Pos.compare_antisym in lt_e2_e3;
            rewrite N.compare_antisym in lt_e2_e3;
            destruct (w ?= w0) eqn:?; destruct (f ?= f0)%N eqn:?;
                     cbn in *; try congruence. }
          { type_conv; subst.
            destruct (morePrecise m1 m0) eqn:prec1;
                     destruct (morePrecise m0 m1) eqn:prec2;
                     destruct m, m0, m1; simpl in *; try congruence; try auto;
                       try rewrite prec1 in *; try rewrite prec2 in *; try congruence;
                         destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                try (apply Ndec.Pcompare_Peqb in case_w0);
                try (apply Ndec.Pcompare_Peqb in case_w1);
                try rewrite Pos.eqb_eq in *;
                try rewrite N.eqb_eq in *;
                subst;
                try congruence;
                try rewrite case_w0;
                try rewrite case_w1; try auto;
                try rewrite Pos.compare_refl;
                try (rewrite N.compare_lt_iff in *; eapply N.lt_trans; eauto);
                assert (w ?= w1 = Lt) as G
                    by (rewrite Pos.compare_lt_iff in *;
                        eapply Pos.lt_trans; eauto);
                rewrite G; auto. }
      + destruct (mTypeEq m m0) eqn:?;
                 destruct (mTypeEq m0 m1) eqn:?;
                 [type_conv; subst; rewrite mTypeEq_refl | | | ].
        { destruct (n ?= n0)%nat eqn:c1; destruct (n0 ?= n1)%nat eqn:c2; try congruence.
          - apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
            rewrite Nat.compare_refl.
            destruct (exprCompare e1_1 y1) eqn:?;
                     destruct (exprCompare y1 z1) eqn:?; try congruence.
            + erewrite exprCompare_eq_trans; eauto.
            + erewrite exprCompare_eq_lt_is_lt; eauto.
            + erewrite exprCompare_lt_eq_is_lt; eauto.
            + erewrite IHe1_1; eauto.
          - apply Nat.compare_eq in c1. subst.
            now rewrite c2.
          - apply Nat.compare_eq in c2. subst.
            now rewrite c1.
          - apply nat_compare_lt in c1. apply nat_compare_lt in c2.
            assert (c3: (n ?= n1)%nat = Lt) by (apply nat_compare_lt; omega).
            now rewrite c3. }
        { destruct (n ?= n0)%nat eqn:c1; destruct (n0 ?= n1)%nat eqn:c2; try congruence.
          - apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
            rewrite Nat.compare_refl.
            apply mTypeEq_compat_eq in Heqb. subst.
            rewrite Heqb0. auto.
          - apply Nat.compare_eq in c1. subst.
            rewrite c2. now destruct (mTypeEq m m1).
          - apply Nat.compare_eq in c2. subst.
            rewrite c1. now destruct (mTypeEq m m1).
          - apply nat_compare_lt in c1. apply nat_compare_lt in c2.
            assert (c3: (n ?= n1)%nat = Lt) by (apply nat_compare_lt; omega).
            rewrite c3. now destruct (mTypeEq m m1). }
        { destruct (n ?= n0)%nat eqn:c1; destruct (n0 ?= n1)%nat eqn:c2; try congruence.
          - apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
            rewrite Nat.compare_refl.
            apply mTypeEq_compat_eq in Heqb0. subst.
            rewrite Heqb. auto.
          - apply Nat.compare_eq in c1. subst.
            rewrite c2. now destruct (mTypeEq m m1).
          - apply Nat.compare_eq in c2. subst.
            rewrite c1. now destruct (mTypeEq m m1).
          - apply nat_compare_lt in c1. apply nat_compare_lt in c2.
            assert (c3: (n ?= n1)%nat = Lt) by (apply nat_compare_lt; omega).
            rewrite c3. now destruct (mTypeEq m m1). }
        { destruct (n ?= n0)%nat eqn:c1; destruct (n0 ?= n1)%nat eqn:c2; try congruence.
          - apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
            rewrite Nat.compare_refl.
            destruct (mTypeEq m m1) eqn:?.
            + type_conv.
              destruct (morePrecise m1 m0) eqn:prec1;
                destruct (morePrecise m0 m1) eqn:prec2;
                destruct m0, m1; simpl in *; try congruence; try auto;
                  destruct (w ?= w0) eqn:case_w0; rewrite Pos.compare_antisym in lt_e1_e2;
                    rewrite case_w0 in *; cbn in *; try congruence;
                      rewrite N.compare_antisym, lt_e2_e3 in lt_e1_e2; cbn in *; congruence.
            + type_conv; subst.
              destruct (morePrecise m1 m0) eqn:prec1;
                destruct (morePrecise m0 m1) eqn:prec2;
                destruct m, m0, m1; simpl in *; try congruence; try auto;
                  destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                    try (apply Ndec.Pcompare_Peqb in case_w0);
                    try (apply Ndec.Pcompare_Peqb in case_w1);
                    try rewrite Pos.eqb_eq in *;
                    try rewrite N.eqb_eq in *;
                    subst;
                    try congruence;
                    try rewrite case_w0;
                    try rewrite case_w1; try auto;
                      try rewrite Pos.compare_refl;
                      try (rewrite N.compare_lt_iff in *; eapply N.lt_trans; eauto);
                      assert (w ?= w1 = Lt) as G
                          by (rewrite Pos.compare_lt_iff in *;
                              eapply Pos.lt_trans; eauto);
                      rewrite G; auto.
          - apply Nat.compare_eq in c1. subst.
            rewrite c2. now destruct (mTypeEq m m1).
          - apply Nat.compare_eq in c2. subst.
            rewrite c1. now destruct (mTypeEq m m1).
          - apply nat_compare_lt in c1. apply nat_compare_lt in c2.
            assert (c3: (n ?= n1)%nat = Lt) by (apply nat_compare_lt; omega).
            rewrite c3. now destruct (mTypeEq m m1). }

        (*
         destruct (morePrecise m m0); destruct m, m0; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
        * rewrite mTypeEq_compat_eq in Heqb; subst.
          rewrite Heqb0; destruct (morePrecise m0 m1); congruence.
        * rewrite mTypeEq_compat_eq in Heqb0; subst.
          rewrite Heqb. destruct (morePrecise m m1); congruence.
        * destruct (mTypeEq m m1) eqn:?.
          { rewrite mTypeEq_compat_eq in Heqb1; subst.
            destruct (morePrecise m1 m0) eqn:prec1;
                     destruct (morePrecise m0 m1) eqn:prec2;
                     destruct m1, m0;
                     try rewrite mTypeEq_refl in *; try congruence;
                       try pose proof (morePrecise_antisym _ _ prec1 prec2);
                       type_conv; try congruence;
                         simpl in *; try congruence;
            rewrite Pos.compare_antisym in lt_e2_e3;
            rewrite N.compare_antisym in lt_e2_e3;
            destruct (w ?= w0) eqn:?; destruct (f ?= f0)%N eqn:?;
                     cbn in *; try congruence. }
          { type_conv; subst.
            destruct (morePrecise m1 m0) eqn:prec1;
                     destruct (morePrecise m0 m1) eqn:prec2;
                     destruct m, m0, m1; simpl in *; try congruence; try auto;
                       try rewrite prec1 in *; try rewrite prec2 in *; try congruence;
                         destruct (w ?= w0) eqn:case_w0; destruct (w0 ?= w1) eqn:case_w1;
                try (apply Ndec.Pcompare_Peqb in case_w0);
                try (apply Ndec.Pcompare_Peqb in case_w1);
                try rewrite Pos.eqb_eq in *;
                try rewrite N.eqb_eq in *;
                subst;
                try congruence;
                try rewrite case_w0;
                try rewrite case_w1; try auto;
                try rewrite Pos.compare_refl;
                try (rewrite N.compare_lt_iff in *; eapply N.lt_trans; eauto);
                assert (w ?= w1 = Lt) as G
                    by (rewrite Pos.compare_lt_iff in *;
                        eapply Pos.lt_trans; eauto);
                rewrite G; auto. }
*)
        (* case for Cond
      + destruct (exprCompare e1_1 y1) eqn:?; try congruence;
          destruct (exprCompare y1 z1) eqn:?; try congruence;
          try (erewrite exprCompare_eq_lt_is_lt; eauto; fail);
          try (erewrite exprCompare_lt_eq_is_lt; eauto; fail);
          try (erewrite IHe1_1; eauto; fail).
        apply (exprCompare_eq_trans _ _ _ Heqc) in Heqc0;
          rewrite Heqc0.
        destruct (exprCompare e1_2 y2) eqn:?; try congruence;
          destruct (exprCompare y2 z2) eqn:?; try congruence;
          try (erewrite exprCompare_eq_trans; eauto; fail);
          try (erewrite exprCompare_eq_lt_is_lt; eauto; fail);
          try (erewrite exprCompare_lt_eq_is_lt; eauto; fail);
          try (erewrite IHe1_2; eauto).
*)
  Qed.*)

  Instance eq_compat: Proper (eq ==> eq ==> iff) eq.
  Proof.
    unfold Proper; hnf.
    intros e1; induction e1;
    intros e2 e1_eq_e2; hnf;
    intros e3 e4 e3_eq_e4;
    unfold lt, eq in *;
    destruct e2,e3,e4; simpl in *; try congruence; try (split; auto; fail).
    - repeat rewrite Nat.compare_eq_iff in *; subst. split; try auto.
    - destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq m1 m2) eqn:?;
               [type_conv | | |].
      + rewrite V_orderedFacts.compare_eq_iff in *.
        rewrite (V_orderedFacts.compare_compat e1_eq_e2 e3_eq_e4).
        split; auto.
      + destruct (morePrecise m1 m2); destruct m1, m2; try congruence;
        destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
          apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
        rewrite Pos.eqb_eq in *; subst; rewrite mTypeEq_refl in *; congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
          apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
        rewrite Pos.eqb_eq in *; subst; rewrite mTypeEq_refl in *; congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
          apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
        rewrite Pos.eqb_eq in *; subst; rewrite mTypeEq_refl in *; congruence.
    - destruct (unopEq u u0) eqn:?;
               destruct (unopEq u1 u2) eqn:?;
               try rewrite unopEq_compat_eq in *; subst;
        try (destruct (unopEq u Neg); congruence);
            try (destruct (unopEq u1 Neg); congruence).
      specialize (IHe1 e2 e1_eq_e2 e3 e4 e3_eq_e4).
      simpl in *. destruct (unopEq u0 u2); try rewrite IHe1; split; auto.
    - destruct b; destruct b0; destruct b1; destruct b2; try congruence;
        try (split; auto; fail);
        destruct (exprCompare e1_1 e2_1) eqn:?;
                 destruct (exprCompare e3_1 e4_1) eqn:?;
                 try congruence;
        destruct (exprCompare e1_1 e3_1) eqn:?;
                 destruct (exprCompare e2_1 e4_1) eqn:?;
                 try (split; congruence);
      try (specialize (IHe1_2 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *; rewrite IHe1_2 in *; split; auto; fail);
      try (split; try congruence; intros);
      try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite IHe1_1 in *; congruence);
      try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite <- IHe1_1 in *; congruence).
  Qed.

  
(*
    - try (split; auto; fail);
        destruct (exprCompare e1_1 e2_1) eqn:?;
                 destruct (exprCompare e3_1 e4_1) eqn:?;
                 try congruence;
        destruct (exprCompare e1_1 e3_1) eqn:?;
                 destruct (exprCompare e2_1 e4_1) eqn:?;
                 try (split; congruence);
        try (specialize (IHe1_2 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *; rewrite IHe1_2 in *; split; auto; fail);
        try (split; try congruence; intros);
        try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite IHe1_1 in *; congruence);
        try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite <- IHe1_1 in *; congruence);
        try (split; auto; fail);
        destruct (exprCompare e1_2 e2_2) eqn:?;
                 destruct (exprCompare e3_2 e4_2) eqn:?;
                 try congruence;
        destruct (exprCompare e1_2 e3_2) eqn:?;
                 destruct (exprCompare e2_2 e4_2) eqn:?;
                 try (split; congruence);
        try (split; try congruence; intros);
        try (specialize (IHe1_2 _ Heqc3 _ _ Heqc4); simpl in *; rewrite IHe1_2 in *; congruence);
        try (specialize (IHe1_2 _ Heqc3 _ _ Heqc4); simpl in *; rewrite <- IHe1_2 in *; congruence);
        try congruence;
        erewrite exprCompare_eq_trans; eauto;
        erewrite exprCompare_eq_trans; eauto;
        rewrite exprCompare_antisym;
        now (try rewrite e3_eq_e4; try rewrite e1_eq_e2).
    -  destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq m1 m2) eqn:?;
               [type_conv | | |].
       + specialize (IHe1 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *.
         destruct (mTypeEq m0 m2); try congruence.
         split; auto.
      + destruct (morePrecise m1 m2); destruct m1, m2; try congruence;
        destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
          apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
        rewrite Pos.eqb_eq in *; subst; rewrite mTypeEq_refl in *; congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
          apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
        rewrite Pos.eqb_eq in *; subst; rewrite mTypeEq_refl in *; congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
          apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
        rewrite Pos.eqb_eq in *; subst; rewrite mTypeEq_refl in *; congruence.
    -  destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq m1 m2) eqn:?;
               [type_conv | | |].
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         destruct (mTypeEq m0 m2); try reflexivity; try congruence.
         destruct (exprCompare e1_1 e2_1) eqn:?;
                  destruct (exprCompare e3_1 e4_1) eqn:?;
                  try congruence.
         destruct (n0 ?= n2)%nat; try tauto.
         destruct (exprCompare e1_1 e3_1) eqn:?;
                  destruct (exprCompare e2_1 e4_1) eqn:?;
                  try (split; congruence).
         * now specialize (IHe1_2 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *.
         * split; try congruence. intros H.
           specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite <- Heqc2. tauto.
         * split; try congruence. intros H.
           specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite <- Heqc2. tauto.
         * split; try congruence. intros H.
           specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite <- Heqc1. tauto.
         * split; try congruence. intros H.
           specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite <- Heqc1. tauto.
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         type_conv.
         destruct (morePrecise m1 m2); destruct m1, m2; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         type_conv.
         destruct (morePrecise m m0); destruct m, m0; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         type_conv.
         destruct (morePrecise m m0); destruct m, m0; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
  
  Qed. *)

  Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper; hnf.
    intros e1; induction e1;
    intros e2 e1_eq_e2; hnf;
    intros e3 e4 e3_eq_e4;
    unfold lt, eq in *;
    destruct e2,e3,e4; simpl in *; try congruence; try (split; auto; fail).
    - rewrite Nat.compare_eq_iff in *; subst. split; try auto.
    - destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq m1 m2) eqn:?;
               [type_conv | | |].
      + rewrite V_orderedFacts.compare_eq_iff in *.
        rewrite (V_orderedFacts.compare_compat e1_eq_e2 e3_eq_e4).
        split; auto.
      + destruct (morePrecise m1 m2); destruct m1, m2; try congruence;
        destruct (w ?= w0) eqn:case1; destruct (f ?= f0)%N eqn:case2;
          try congruence;
          apply Ndec.Pcompare_Peqb in case1;
          apply N.compare_eq in case2;
          rewrite Pos.eqb_eq in *; subst; cbn in *;
            repeat rewrite N.eqb_refl, Pos.eqb_refl in *; simpl in *; try congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:case1; destruct (f ?= f0)%N eqn:case2;
          try congruence;
          apply Ndec.Pcompare_Peqb in case1;
          apply N.compare_eq in case2;
          rewrite Pos.eqb_eq in *; subst; cbn in *;
            repeat rewrite Pos.eqb_refl, N.eqb_refl in *; simpl in *; try congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:case1; destruct (f ?= f0)%N eqn:case2;
          try congruence;
          apply Ndec.Pcompare_Peqb in case1;
          apply N.compare_eq in case2;
          rewrite Pos.eqb_eq in *; subst; cbn in *;
            repeat rewrite N.eqb_refl, Pos.eqb_refl in *; simpl in *; try congruence.
    - destruct (unopEq u u0) eqn:?;
               destruct (unopEq u1 u2) eqn:?;
               try rewrite unopEq_compat_eq in *; subst;
        try (destruct (unopEq u Neg); congruence);
            try (destruct (unopEq u1 Neg); congruence).
      specialize (IHe1 e2 e1_eq_e2 e3 e4 e3_eq_e4).
      simpl in *. destruct (unopEq u0 u2); try rewrite IHe1; split; auto.
    - pose proof eq_compat as eq_comp. unfold Proper, eq in eq_comp.
      destruct b, b0, b1, b2; try congruence; try (split; auto; fail);
        destruct (exprCompare e1_1 e2_1) eqn:?;
                 destruct (exprCompare e3_1 e4_1) eqn:?;
                 try congruence;
        destruct (exprCompare e1_1 e3_1) eqn:?;
                 destruct (exprCompare e2_1 e4_1) eqn:?;
                 try (split; congruence);
        try (specialize (IHe1_2 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *; rewrite IHe1_2 in *; split; auto; fail);
        try (split; try congruence; intros);
        try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite IHe1_1 in *; congruence);
        try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite <- IHe1_1 in *; congruence);
        try (rewrite (eq_comp _ _ Heqc _ _ Heqc0) in *; congruence);
        try (rewrite <- (eq_comp _ _ Heqc _ _ Heqc0) in *; congruence).
  Qed.

 (* - pose proof eq_compat as eq_comp. unfold Proper, eq in eq_comp.
      destruct (exprCompare e1_1 e2_1) eqn:?;
               destruct (exprCompare e3_1 e4_1) eqn:?;
               try congruence;
        destruct (exprCompare e1_1 e3_1) eqn:?;
                 destruct (exprCompare e2_1 e4_1) eqn:?;
                 try (split; congruence);
        try (specialize (IHe1_2 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *; rewrite IHe1_2 in *; split; auto; fail);
        try (split; try congruence; intros);
        try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite IHe1_1 in *; congruence);
        try (specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *; rewrite <- IHe1_1 in *; congruence);
        try (rewrite (eq_comp _ _ Heqc _ _ Heqc0) in *; congruence);
        try (rewrite <- (eq_comp _ _ Heqc _ _ Heqc0) in *; congruence);
        destruct (exprCompare e1_2 e2_2) eqn:?;
               destruct (exprCompare e3_2 e4_2) eqn:?;
               try congruence;
        destruct (exprCompare e1_2 e3_2) eqn:?;
                 destruct (exprCompare e2_2 e4_2) eqn:?;
                 try (split; congruence);
        try (specialize (IHe1_3 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *; rewrite IHe1_3 in *; split; auto; fail);
        try (split; try congruence; intros);
        try (specialize (IHe1_2 _ Heqc3 _ _ Heqc4); simpl in *; rewrite IHe1_2 in *; congruence);
        try (specialize (IHe1_2 _ Heqc3 _ _ Heqc4); simpl in *; rewrite <- IHe1_2 in *; congruence);
        try (rewrite (eq_comp _ _ Heqc3 _ _ Heqc4) in *; congruence);
        try (rewrite <- (eq_comp _ _ Heqc3 _ _ Heqc4) in *; congruence);
        try congruence.
      + apply (exprCompare_lt_eq_is_lt _ _ _ H) in e3_eq_e4;
        rewrite exprCompare_eq_sym in e1_eq_e2;
        now apply (exprCompare_eq_lt_is_lt _ _ _ e1_eq_e2).
      + rewrite exprCompare_eq_sym in e3_eq_e4;
        apply (exprCompare_lt_eq_is_lt _ _ _ H) in e3_eq_e4;
        now apply (exprCompare_eq_lt_is_lt _ _ _ e1_eq_e2).
    -  destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq m1 m2) eqn:?;
               [type_conv | | |].
       + specialize (IHe1 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *.
         destruct (mTypeEq m0 m2); try congruence.
         split; auto.
      + destruct (morePrecise m1 m2); destruct m1, m2; try congruence;
        destruct (w ?= w0) eqn:case1; destruct (f ?= f0)%N eqn:case2;
          try congruence;
          apply Ndec.Pcompare_Peqb in case1;
          apply N.compare_eq in case2;
          rewrite Pos.eqb_eq in *; subst; cbn in *;
            repeat rewrite N.eqb_refl, Pos.eqb_refl in *; simpl in *; try congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:case1; destruct (f ?= f0)%N eqn:case2;
          try congruence;
          apply Ndec.Pcompare_Peqb in case1;
          apply N.compare_eq in case2;
          rewrite Pos.eqb_eq in *; subst; cbn in *;
            repeat rewrite Pos.eqb_refl, N.eqb_refl in *; simpl in *; try congruence.
      + destruct (morePrecise m m0); destruct m, m0; try congruence;
        destruct (w ?= w0) eqn:case1; destruct (f ?= f0)%N eqn:case2;
          try congruence;
          apply Ndec.Pcompare_Peqb in case1;
          apply N.compare_eq in case2;
          rewrite Pos.eqb_eq in *; subst; cbn in *;
            repeat rewrite N.eqb_refl, Pos.eqb_refl in *; simpl in *; try congruence.
    - pose proof eq_compat as eq_comp. unfold Proper, eq in eq_comp.
       destruct (mTypeEq m m0) eqn:?; destruct (mTypeEq m1 m2) eqn:?;
               [type_conv | | |].
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         destruct (mTypeEq m0 m2); try reflexivity; try congruence.
         destruct (exprCompare e1_1 e2_1) eqn:?;
                  destruct (exprCompare e3_1 e4_1) eqn:?;
                  try congruence.
         destruct (n0 ?= n2)%nat; try tauto.
         destruct (exprCompare e1_1 e3_1) eqn:?;
                  destruct (exprCompare e2_1 e4_1) eqn:?;
                  try (split; congruence).
         * now specialize (IHe1_2 _ e1_eq_e2 _ _ e3_eq_e4); simpl in *.
         * specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite <- IHe1_1 in *. congruence.
         * pose proof (exprCompare_eq_trans _ _ _ Heqc1 Heqc0).
           apply exprCompare_eq_sym in Heqc.
           pose proof (exprCompare_eq_trans _ _ _ Heqc H).
           congruence.
         * specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite IHe1_1 in *. congruence.
         * specialize (IHe1_1 _ Heqc _ _ Heqc0); simpl in *.
           rewrite IHe1_1 in *. congruence.
         * pose proof (exprCompare_eq_trans _ _ _ Heqc Heqc2).
           apply exprCompare_eq_sym in Heqc0.
           pose proof (exprCompare_eq_trans _ _ _ H Heqc0).
           congruence.
         * pose proof (exprCompare_eq_lt_is_lt _ _ _ Heqc Heqc2).
           apply exprCompare_eq_sym in Heqc0.
           pose proof (exprCompare_lt_eq_is_lt _ _ _ H Heqc0).
           congruence.
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         type_conv.
         destruct (morePrecise m1 m2); destruct m1, m2; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
       + destruct (n ?= n0)%nat; try congruence.
         type_conv.
         destruct (morePrecise m m0); destruct m, m0; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
       + destruct (n ?= n0)%nat eqn:c1; destruct (n1 ?= n2)%nat eqn:c2; try congruence.
         apply Nat.compare_eq in c1. apply Nat.compare_eq in c2. subst.
         type_conv.
         destruct (morePrecise m m0); destruct m, m0; try congruence;
           destruct (w ?= w0) eqn:c1; destruct (f ?= f0)%N eqn:c2; try congruence;
             apply Ndec.Pcompare_Peqb in c1; apply N.compare_eq in c2;
               rewrite Pos.eqb_eq in *; subst; congruence.
  
  Qed. *)

  Lemma compare_spec : forall x y, CompSpec eq lt x y (exprCompare x y).
  Proof.
    intros e1 e2.
    destruct (exprCompare e1 e2) eqn:?.
    - apply CompEq.
      unfold eq; auto.
    - apply CompLt. unfold lt; auto.
    - apply CompGt. unfold lt.
      rewrite exprCompare_antisym in Heqc.
      rewrite CompOpp_iff in Heqc.
      simpl in *; auto.
  Qed.

  Instance eq_equiv: Equivalence eq.
  Proof.
    split; unfold Reflexive, Symmetric, Transitive, eq.
    - apply exprCompare_refl.
    - intros. rewrite exprCompare_antisym in * |-.
      rewrite CompOpp_iff in * |- .
      auto.
    - apply exprCompare_eq_trans.
  Defined.

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    intros. unfold eq. destruct (exprCompare x y) eqn:?; try auto.
    - right; hnf; intros; congruence.
    - right; hnf; intros; congruence.
  Defined.

  Definition eq_refl : forall x, eq x x.
  Proof.
    apply exprCompare_refl.
  Defined.

  Definition eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; intros.
    rewrite exprCompare_antisym in * |-.
    rewrite CompOpp_iff in * |-.
    auto.
  Defined.

  Definition eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    apply exprCompare_eq_trans.
  Defined.

  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    pose proof lt_strorder as [_ Trans].
    apply Trans.
  Defined.

  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros. unfold lt,eq in *. hnf; intros; congruence.
  Defined.

  Definition compare e1 e2:= exprCompare e1 e2.

  Close Scope positive_scope.

End ExprOrderedType.


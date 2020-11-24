  (**
   This file contains the coq implementation of the snapping mechanism.
 **)
From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals
     Strings.Ascii Strings.BinaryString.

From Snapv
     Require Import 
     Expressions Command ExpressionTransitions
     CommandSemantics Maps  apRHL.

(** Error bound validator **)

Open Scope R_scope.


Definition Snap (a: R) (Lam: R) (B: R) (eps: R) :=
	SEQ (UNIF1 (Var R 1)) 
	(SEQ (UNIF2 (Var R 2)) 
		(ASGN (Var R 3) 
			(Binop Clamp (Const REAL B) 
				(Binop Round (Const REAL Lam)
					(Binop Plus (Const REAL a)
						(Binop Mult (Const REAL eps)
							(Binop Mult (Var R 2)
								(Unop Ln (Var R 1)))))))))
.

Definition eta := 0.0000000005%R.

(*
Lemma SnapDP :
                    forall a a' Lam B eps: R,
                      Rle (Rplus a (Ropp a')) 1 ->
                       Rle (Ropp 1) (Rplus a (Ropp a')) ->
                       hoare_rule ATrue (Snap a Lam B eps) (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) (Snap a' Lam B eps)
                                  (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat 3)),(m2 (of_nat 3)) with
                                  | (v1, (er11, er12)),(v2, (er21, er22)) =>
                                      v1 = v2
                                  end
                    end)
  .
*)
Lemma SnapDP :
  forall a a' Lam B eps: R,
    (Rplus a (Ropp a')) = 1 ->
    hoare_rule ATrue (Snap a Lam B eps) (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta)))) (Snap a' Lam B eps)
               (fun (pm : (state * state)) =>
                    match pm with
                    | (m1, m2) => match (m1 (of_nat 3)),(m2 (of_nat 3)) with
                                  | (v1, er1),(v2, er2) =>
                                      v1 = v2
                                  end
                    end)
.

Proof.
  intros.
  unfold Snap.
  apply H_Seq with
      (P := ATrue)  (c1 := (UNIF1 (Var R 1)))
      (c2 := (SEQ (UNIF2 (Var R 2))
                  (ASGN (Var R 3)
                        (Binop Clamp (Const REAL B)
                               (Binop Round (Const REAL Lam)
                                      (Binop Plus (Const REAL a)
                                             (Binop Mult (Const REAL eps)
                                                    (Binop Mult (Var R 2)
                                                           (Unop Ln (Var R 1))))))))))
      (r1 := (Rmult eps (Rplus 1 (Rmult 24%R (Rmult B eta))))) (r2 := (0%R))
      (d1 := (UNIF1 (Var R 1)))
      (d2 := (SEQ (UNIF2 (Var R 2))
                  (ASGN (Var R 3)
                        (Binop Clamp (Const REAL B)
                               (Binop Round (Const REAL Lam)
                                      (Binop Plus (Const REAL a')
                                             (Binop Mult (Const REAL eps)
                                                    (Binop Mult (Var R 2)
                                                           (Unop Ln (Var R 1))))))))))
      (R0 :=  (fun pm : state * state =>
                 let (m1, m2) := pm in
                 let (v1, _) := m1 (of_nat 3) in
                 let (v2, _) := m2 (of_nat 3) in v1 = v2)
      ).



Admitted.
                                             
Close Scope R_scope.

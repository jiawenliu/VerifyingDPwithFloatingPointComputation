 (**
   This file contains the coq implementation of the error bound validator as
   well as its soundness proof. The function validErrorbound is the Error bound
   validator from the certificate checking process. Under the assumption that a
   valid range arithmetic result has been computed, it can validate error bounds
   encoded in the analysis result. The validator is used in the file
   CertificateChecker.v to build the complete checker.
 **)
From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Snapv
     Require Import Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis ErrorBounds
     IntervalArithQ  TypeValidator.

(** Error bound validator **)
Fixpoint validErrorbound (e:expr Q) (* analyzed exprression *)
         (typeMap:SnapvMap.t mType) (* derived types for e *)
         (A:analysisResult) (* encoded result of Snapv *)
         (dVars:NatSet.t) (* let-bound variables encountered previously *):=
  match SnapvMap.find e A, SnapvMap.find e typeMap with
  | Some (intv, err), Some m =>
    if (Qleb 0 err) (* encoding soundness: errors are positive *)
    then
      match e with (* case analysis for the expression *)
      |Var _ v =>
       if (NatSet.mem v dVars)
       then true (* defined variables are checked at definition point *)
       else Qleb (computeErrorQ (maxAbs intv) m) err
      |Const m n =>
       Qleb (computeErrorQ (maxAbs intv) m) err
      |Unop Neg e1 =>
       if (validErrorbound e1 typeMap A dVars)
       then
         match SnapvMap.find e1 A with
         | Some (iv_e1, err1) => Qeq_bool err err1
         | None => false
         end
       else false
      |Unop Inv e1 => false
      |Binop b e1 e2 =>
       if ((validErrorbound e1 typeMap A dVars)
             && (validErrorbound e2 typeMap A dVars))
       then
         match SnapvMap.find e1 A, SnapvMap.find e2 A with
         | Some (ive1, err1), Some (ive2, err2) =>
           let errIve1 := widenIntv ive1 err1 in
           let errIve2 := widenIntv ive2 err2 in
           let upperBoundE1 := maxAbs ive1 in
           let upperBoundE2 := maxAbs ive2 in
           match b with
           | Plus =>
             let mAbs := (maxAbs (addIntv errIve1 errIve2)) in
             Qleb (err1 + err2 + computeErrorQ mAbs m) err
           | Sub =>
             let mAbs := (maxAbs (subtractIntv errIve1 errIve2)) in
             Qleb (err1 + err2 + computeErrorQ mAbs m) err
           | Mult =>
             let mAbs := (maxAbs (multIntv errIve1 errIve2)) in
             let eProp := (upperBoundE1 * err2 + upperBoundE2 * err1 + err1 * err2) in
             Qleb (eProp + computeErrorQ mAbs m) err
           | Div =>
             if (((Qleb (ivhi errIve2) 0) && (negb (Qeq_bool (ivhi errIve2) 0))) ||
                 ((Qleb 0 (ivlo errIve2)) && (negb (Qeq_bool (ivlo errIve2) 0))))
             then
               let upperBoundInvE2 := maxAbs (invertIntv ive2) in
               let minAbsIve2 := minAbs (errIve2) in
               let errInv := (1 / (minAbsIve2 * minAbsIve2)) * err2 in
               let mAbs := (maxAbs (divideIntv errIve1 errIve2)) in
               let eProp :=
                   (upperBoundE1 * errInv + upperBoundInvE2 * err1 + err1 * errInv) in
               Qleb (eProp + computeErrorQ mAbs m) err
             else false
           end
         | _, _ => false
         end
       else false
      | Fma e1 e2 e3 =>
        if ((validErrorbound e1 typeMap A dVars)
              && (validErrorbound e2 typeMap A dVars)
              && (validErrorbound e3 typeMap A dVars))
        then
          match SnapvMap.find e1 A, SnapvMap.find e2 A, SnapvMap.find e3 A with
          | Some (ive1, err1), Some (ive2, err2), Some (ive3, err3) =>
            let errIve1 := widenIntv ive1 err1 in
            let errIve2 := widenIntv ive2 err2 in
            let errIve3 := widenIntv ive3 err3 in
            let upperBoundE1 := maxAbs ive1 in
            let upperBoundE2 := maxAbs ive2 in
            let upperBoundE3 := maxAbs ive3 in
            let errIntv_prod := multIntv errIve1 errIve2 in
            let mult_error_bound := (upperBoundE1 * err2 + upperBoundE2 * err1 + err1 * err2) in
            let mAbs := (maxAbs (addIntv errIntv_prod errIve3)) in
            Qleb (mult_error_bound + err3 + computeErrorQ mAbs m) err
          | _, _, _ => false
          end
        else false
      |Downcast m1 e1 =>
       if validErrorbound e1 typeMap A dVars
       then
         match SnapvMap.find e1 A with
         | Some (ive1, err1) =>
          let errIve1 := widenIntv ive1 err1 in
          let mAbs := maxAbs errIve1 in
          Qleb (err1 + computeErrorQ mAbs m1) err
         | None => false
         end
       else
         false
      | Let m x e1 e2 =>
        (* TODO: What do we map how here? *)
        if (validErrorbound e1 typeMap A dVars)
             && validErrorbound e2 typeMap A (NatSet.add x dVars)
        then
          match SnapvMap.find e1 A, SnapvMap.find (Var Q x) A with
          | Some (iv_e, err_e), Some (iv_x, err_x) =>
            if (Qeq_bool err_e err_x)
                 then
                   match SnapvMap.find e2 A with
                   | Some (iv_e2, err_e2) => Qeq_bool err_e2 err
                   | _ => false
                   end
            else false
          | _,_ => false
          end
        else false
      (* | Cond e1 e2 e3 => false *)
      end
    else false
  | _, _ => false
  end.

(*
(** Error bound command validator **)
Fixpoint validErrorboundCmd (f:cmd Q) (* analyzed cmd with let's *)
         typeMap (* inferred types *)
         (A:analysisResult) (* Snapv's encoded result *)
         (dVars:NatSet.t) (* defined variables *)
         : bool :=
  match f with
  |Let m x e g =>
   match SnapvMap.find e A, SnapvMap.find (Var Q x) A with
     | Some (iv_e, err_e), Some (iv_x, err_x) =>
       if ((validErrorbound e typeMap A dVars) && (Qeq_bool err_e err_x))
       then validErrorboundCmd g typeMap A (NatSet.add x dVars)
       else false
     | _,_ => false
   end
  |Ret e => validErrorbound e typeMap A dVars
  end.
*)

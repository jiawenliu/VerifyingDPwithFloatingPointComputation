 (**
   This file contains the coq implementation of the .
 **)
From Coq
     Require Import QArith.QArith QArith.Qminmax QArith.Qabs QArith.Qreals
     micromega.Psatz Reals.Reals.

From Snapv
     Require Export Infra.Abbrevs Infra.RationalSimps Infra.RealRationalProps
     Infra.RealSimps Infra.Ltacs Environments ErrorAnalysis ErrorBounds
     IntervalArithQ  TypeValidator
     Expressions Command ExpressionSemantics ExpressionTransitions
     CommandTransitions Maps Imp Hoare SnapMech.

(** Error bound validator **)
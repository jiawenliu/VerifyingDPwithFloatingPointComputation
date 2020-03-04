(*
  This file contains some type abbreviations, to ease writing.
 **)
Require Import Coq.Reals.Reals Coq.QArith.QArith Coq.QArith.Qreals.
Require Import Snapv.Infra.MachineType.

(**
We define Intervals twice.
First we define intervals of reals and fractions.
We need both of them since the analysis argues about intervals of fractions
and the proofs should argue about real valued exections.

Intervals are defined as a type, consisting of a pair of two real numbers or fractions.
Additionally add some constructing and destructing definitions for encapsulation and
define them to automatically unfold upon simplification.
 **)
Definition interval:Type := R * R.
Definition err:Type := R.
Definition mkInterval (ivlo:R) (ivhi:R) := (ivlo,ivhi).
Definition IVlo (intv:interval) := fst intv.
Definition IVhi (intv:interval) := snd intv.

Arguments mkInterval _ _/.
Arguments IVlo _ /.
Arguments IVhi _ /.

Definition intv:Type := Q * Q.
Definition error :Type := Q.

Definition mkIntv (ivlo:Q) (ivhi:Q) := (ivlo,ivhi).
Definition ivlo (intv:intv) := fst intv.
Definition ivhi (intv:intv) := snd intv.

Arguments mkIntv _ _/.
Arguments ivlo _ /.
Arguments ivhi _ /.

(**
  Abbreviation for the type of a variable environment, which should be a partial function
 **)
Definition env := nat -> option R.

(**
  The empty environment must return NONE for every variable
**)
Definition emptyEnv:env := fun _ => None.

(**
  Define environment update function as abbreviation, for variable environments
**)
Definition updEnv (x:nat) (v: R) (E:env) (y:nat) :=
  if (y =? x)
  then Some v
  else E y.

Definition updDefVars (x:nat) (m:mType) (defVars:nat -> option mType) (y:nat) :=
  if (y =? x) then Some m else defVars y.

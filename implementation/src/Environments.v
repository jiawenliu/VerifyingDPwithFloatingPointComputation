From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import seq choice.
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
From Snapv.lib Require Import MachineType.
Require Import Coq.micromega.Lra Coq.micromega.Lia.

(** With all these definitions in place, we can define states as finite
    functions, and Coq will be able to figure out that they form an ordered type
    (because their keys and values are ordered).

    If [f : T -> S], the type [ffun f] contains functions that are equal to [f]
    in all but finitely many inputs. When [f] is a constant function [fun _ =>
    y], this means that almost all outputs of a finite function are equal to [y]

 *)

Notation state := (ffun (fun v : string => ((F64 0%R), (0%R, 0%R)))).



  Section mathcomp.

  From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
  From mathcomp Require Import choice fintype tuple finfun bigop ssralg poly.
  From mathcomp Require Import polydiv finset fingroup morphism quotient perm.
  From mathcomp Require Import action zmodp cyclic matrix mxalgebra vector.
  From mathcomp Require Import falgebra fieldext separable.
  Import GroupScope GRing.Theory.
  Import GRing.
  Check {vspace _}.
  (* Context (F : fieldType). *)
  Variables (F : fieldType) (L : splittingFieldType F).
  Context {K E : {vspace L}}.

  (* Context (F : {vspace T}). *)
  Check @galois F L K E.
  Context (T : galois K E).

  Check col.
  (* Definition MixColumnsMat : 'M[F]_(4, 4) := \matrix_ (i, j) _. *)

  End mathcomp.

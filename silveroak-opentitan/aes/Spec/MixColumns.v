
(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Coq.Vectors.Fin.
Import Vector.
Import VectorNotations.
Require Import Lia.
Require Import Psatz.


Section Spec.
  Context {byte : Type}
          (add : byte -> byte -> byte)
          (mul : nat -> byte -> byte).


  Open Scope vector_scope.
  
  Ltac nat_to_fin x :=
    match goal with
    | |- Fin.t ?k => apply (@Fin.of_nat_lt x k); lia
    end.
  
  Infix "⊕" := (add)(left associativity, at level 45).
  Infix "∙" := (mul)(at level 43, left associativity).
  (* Notation "\[[ x \]]" := (@Fin.of_nat_lt _ x ltac:(lia)). *)

  Notation "\[ x \]" := (ltac:(nat_to_fin x))(only parsing).
  Notation "\[ x \]" := (@Fin.of_nat_lt x _ _)(only printing).
  Definition col := (byte * byte * byte * byte)%type.
  (* Definition col := Vector.t byte 4. *)


  Check @Fin.of_nat_lt.
  
  Check ( \[ 3 \] : Fin.t 7).
  Check nth.
  
  Definition MixColumns (c : col) : col :=
    match c with
    | (c0,c1,c2,c3) => 
      (2 ∙ c0 ⊕ 3 ∙ c1 ⊕ 1 ∙ c2 ⊕ 1 ∙ c3,
       1 ∙ c0 ⊕ 2 ∙ c1 ⊕ 3 ∙ c2 ⊕ 1 ∙ c3,
       1 ∙ c0 ⊕ 1 ∙ c1 ⊕ 2 ∙ c2 ⊕ 3 ∙ c3,
       3 ∙ c0 ⊕ 1 ∙ c1 ⊕ 1 ∙ c2 ⊕ 2 ∙ c3)
    end.

  
  Definition InvMixColumns (c : col) : col :=
    match c with
    | (c0,c1,c2,c3) => 
      (14 ∙ c0 ⊕ 11 ∙ c1 ⊕ 13 ∙ c2 ⊕  9 ∙ c3,
        9 ∙ c0 ⊕ 14 ∙ c1 ⊕ 11 ∙ c2 ⊕ 13 ∙ c3,
       13 ∙ c0 ⊕  9 ∙ c1 ⊕ 14 ∙ c2 ⊕ 11 ∙ c3,
       11 ∙ c0 ⊕ 13 ∙ c1 ⊕  9 ∙ c2 ⊕ 14 ∙ c3)
    end.

  Context (Hdistrib : forall x y z, x ∙ (y ⊕ z) = x ∙ y ⊕ x ∙ z).
  Context (Hfoo : forall x y z, x ∙ (y ∙ z) = (x * y) ∙ z).
  
  Hint Rewrite @Hdistrib : foo.
  Hint Rewrite @Hfoo : foo.
  
  
  Lemma InvMixColumns_MixColumns (c : col) :
    InvMixColumns (MixColumns c) = c.
  Proof.
    destruct c as [ [[c0 c1] c2] c3 ].
    simpl. repeat f_equal.
    all: autorewrite with foo.
    all: simpl.

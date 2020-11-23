
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
Require Import Cava.VectorUtils.
Require Import Cava.Tactics.
Require Import Coq.Vectors.Fin.
Require Import Coq.Setoids.Setoid.
Import Vector.
Import VectorNotations.
Require Import Lia.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Wf.

From mathcomp Require Import field.galois.
From mathcomp Require Import field.finfield.
From mathcomp Require Import algebra.matrix.

Set Implicit Arguments.

Section Spec.
  Context {byte : Type}
          (zero one : byte)
          (add smul sub div : byte -> byte -> byte)
          (opp inv : byte -> byte)
          (* (mul : nat -> byte -> byte) *)
          (lift : nat -> byte).

  Require Import Coq.Bool.Bool.

  Search( _ =? _).
  Check reflect.

  Print iff_reflect.
  Print Nat.eqb_spec.
  Check Nat.eqb.

  Fixpoint xor' n (x y : nat) : nat :=
    match n with
    | 0 => 0
    | (S n') =>
      if x =? 0
      then y
      else ((x + y) mod 2) + 2*(xor' n' (x / 2) (y / 2))
    end .

  Definition xor (x y : nat) : nat := xor' (x+y) x y.

  (* Program Fixpoint xor (x y : nat) {measure x} : nat := *)
  (*   match Nat.eqb_spec x 0 with *)
  (*   | ReflectT H => y *)
  (*   | ReflectF H => *)
  (*     ((x + y) mod 2) + 2*(xor (x / 2) (y / 2)) *)
  (*   end . *)
  (* Next Obligation. *)
  (*   assert (H' := Nat.divmod_spec x 1 0 1 ltac:(reflexivity)). *)
  (*   destruct (Nat.divmod x 1 0 1) as [a b]. *)
  (*   destruct H' as [H0 H1]. *)
  (*   simpl in *. lia. *)
  (* Qed. *)

  (* Print xor. *)

  Definition mul (i : nat) (b : byte) : byte :=
    smul (lift i) b.

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

  Open Scope ring_scope.
  Check \matrix_ (i, i) _.

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
  Context (Hassoc : forall x y z, x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z).

  Lemma Hdistrib' : forall x y z, (xor y z) ∙ x = y ∙ x ⊕ z ∙ x.
    Admitted.

  Lemma Hdistrib'' : forall x y z k, k ⊕ (xor y z) ∙ x = k ⊕ y ∙ x ⊕ z ∙ x.
    Admitted.

  Import ListNotations.
  Local Open Scope list_scope.

  Fixpoint poly (xs : list (nat * byte)%type) : byte :=
    match xs with
    | ([])%list => zero
    | ((x, k):: xs) => x ∙ k ⊕ poly xs
    end.

  Lemma poly_mk x y :
    x ∙ y = poly [(x, y)].
  Admitted.

  Lemma poly_app xs ys :
    poly xs ⊕ poly ys = poly (xs ++ ys).
  Admitted.

  Variables
    Hlift : forall x y, mul x y = smul (lift x) y.

  Hint Rewrite @Hdistrib : foo.
  Hint Rewrite @Hfoo : foo.
  Hint Rewrite @Hassoc : foo.
  (* Hint Rewrite @poly_mk : bar. *)
  (* Hint Rewrite @poly_app : bar. *)
  (* Hint Rewrite @Hlift : foo_bar. *)

  (* Ltac  *)

  Ltac poly_swap x y :=
    match goal with
    | |- context [ poly ?a ] =>
      match a with
      | ((?a, x) :: (?b, y) :: ?xs)%list =>
        assert (H : poly ((x :: y :: xs)) = poly ((y :: x :: xs)) )
      | _ => fail "bar"
      end
    end.

  Require Import Ring Field.

  Check ring_theory zero one add smul sub opp eq.

  Variables foo : field_theory zero one add smul sub opp div inv eq.
  (* Variables foo : ring_theory zero one add smul sub opp eq. *)

  Context (Hcomm : forall x y, x ⊕ y = y ⊕ x).

  Add Field byte : foo.

  Lemma Hcomm' x y k : k ⊕ x ⊕ y = k ⊕ y ⊕ x.
    Admitted.

  Ltac foo c :=
    match goal with
    | |- context f [ ?a ∙ c ⊕ ?b ∙ c ] => rewrite <- (Hdistrib' c a b)
    | |- context f [ ?k ⊕ ?a ∙ c ⊕ ?b ∙ c ] => rewrite <- (Hdistrib'' c a b k)
    | |- context f [ ?a ∙ ?x ⊕ ?b ∙ c ] => rewrite (Hcomm (a ∙ x) (b ∙ c))
    | |- context f [ ?k ⊕ ?a ∙ ?x ⊕ ?b ∙ c ] => rewrite (Hcomm' (a ∙ x) (b ∙ c) k)
    end.

  Ltac eval_mul :=
    repeat (
    let k := fresh "k" in
    let Hk := fresh "Hk" in
    match goal with
    | |- context [ ?x * ?y ] =>
      remember (x * y) as k eqn:Hk;
      compute in Hk; subst k
    | |- context [ xor ?x ?y ] =>
      remember (xor x y) as k eqn:Hk;
      vm_compute in Hk; subst k
    end).

  Search xor.


  Lemma InvMixColumns_MixColumns (c : col) :
    InvMixColumns (MixColumns c) = c.
  Proof.
    destruct c as [ [[c0 c1] c2] c3 ].
    simpl. repeat f_equal.
    all: autorewrite with foo.

    all: repeat foo c0.
    all: repeat foo c1.
    all: repeat foo c2.
    all: repeat foo c3.
      (* simpl. *)
    all: eval_mul.

    compute.

    Eval compute in 2^8 + 2^4 + 2^3 + 1.

Qed.

    foo c1.
    foo c1.
    foo c1.
    foo c1.
    foo c1.

    all: autorewrite with foo_bar.
    (* all: unfold app. *)

    (* poly_swap c0 c1. *)

    all: simpl.
    ring_simplify c0.
    field. ring.

    ring_simplify.

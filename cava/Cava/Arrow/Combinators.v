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

From Coq Require Import Strings.String Bool.Bvector Lists.List NArith.NArith
     Init.Nat micromega.Lia Arith.Plus.
From Cava.Arrow Require Import ArrowKind CavaNotation ExprSyntax.

Import ListNotations.
Import EqNotations.

Import KappaNotation.
Local Open Scope category_scope.
Local Open Scope string_scope.
Local Open Scope kind_scope.

Definition split_pow2 A n
  : Kappa << Vector A (2^(S n)), Unit >> <<Vector A (2^n), Vector A (2^n)>> :=
  <[\ x =>
    let '(l,r) : <<Vector A _, Vector A _>> = split_at (2^n) x in
    (l, typecast r)
  ]>.

(* *************************** *)
(* Misc *)

Definition uncurry {A B C args}
  (f: << <<A, B>>, args >> ~> C)
  : Kappa <<A, B, args>> C :=
  <[ \a b => !f (a, b) ]>.

Definition curry {A B C}
  (f:  << A, B, Unit >> ~> C)
  : Kappa << <<A, B>>, Unit >> C :=
  <[ \ab => let '(a, b) : <<A,B>> = ab in !f a b ]>.

Fixpoint reshape {n m A}
  : Kappa << Vector A (n * m), Unit >> << Vector (Vector A m) n >> :=
match n with
| 0 => <[\_ => [] ]>
| S n' =>
  <[ \vec =>
    let '(x, xs) = split_at m vec in
    x :: !(@reshape n' m A) xs
    ]>
end.

Fixpoint flatten {n m A}
  : Kappa << Vector (Vector A m) n, Unit >> << Vector A (n*m) >> :=
match n with
| 0 => <[\_ => [] ]>
| S n' =>
  <[ \vec =>
    let '(x, xs) = uncons vec in
    concat x (!(@flatten n' m A) xs)
    ]>
end.

Fixpoint reverse {n A}
  : Kappa << Vector A n, Unit >> << Vector A n >> :=
match n with
| 0 => <[\_ => [] ]>
| S n' =>
  <[ \vec =>
    let '(x, xs) = uncons vec in
    snoc (!reverse xs) x
    ]>
end.

Fixpoint seq {n bitsize}
  (offset: N)
  : Kappa << Unit >> << Vector (Vector Bit bitsize) n >> :=
match n with
| 0 => <[ [] ]>
| S n' => <[ #offset :: !(seq (offset + 1)) ]>
end.

(* *************************** *)
(* Tree folds, expecting a vector of input size pow2 *)

Fixpoint tree (A: Kind) (n: nat)
  (f: << A, A, Unit >> ~> A) {struct n}
  : Kappa << Vector A (2^n), Unit >> A :=
match n with
| O => <[ \ vec => let '(x,_) = uncons vec in x ]>
| S n' =>
  <[\ x =>
      let '(left,right) : <<Vector A _, Vector A _>> = !(split_pow2 A n') x in
      let a = !(tree A n' f) left in
      let b = !(tree A n' f) right in
      !f a b
  ]>
end.

Fixpoint dt_tree_fold'
  (n k: nat)
  (T: nat -> Kind)
  (f: forall n,  << T n, T n, Unit >> ~> (T (S n))) {struct n}
  : Kappa << Vector (T k) (2^n), Unit >> (T (n + k)) :=
match n with
| O => <[ \ vec => let '(x,_) = uncons vec in x ]>
| S n' =>
  <[\ x =>
      let '(left,right) : <<Vector _ _, Vector _ _>> = !(split_pow2 (T k) n') x in
      let a = !(dt_tree_fold' n' k T f) left in
      let b = !(dt_tree_fold' n' k T f) right in
      !(f _) a b
  ]>
end.

Lemma inj_succ_in_kind: forall n (T: nat -> Kind), T (n + 0) = T n.
Proof. auto. Qed.

Definition dt_tree_fold
  (n: nat)
  (T: nat -> Kind)
  (f: forall n,  << T n, T n, Unit >> ~> T (S n))
  : Kappa << Vector (T 0) (2^n), Unit >> (T n) :=
  <[ \vec => typecast (!(dt_tree_fold' n 0 T f) vec) ]>.

(* *************************** *)
(* element mapping *)

Fixpoint foldl {n A B}
  (f: <<B, A, Unit>> ~> B)
  {struct n}
  : Kappa <<B, Vector A n, Unit >> <<B>> :=
match n with
| 0 => <[ \initial _ => initial ]>
| S n' =>
  <[ \initial xs =>
      let '(x, xs') = uncons xs in
      !(foldl f) (!f initial x) xs'
  ]>
end.

Fixpoint foldr {n A B}
  (f: <<A, B, Unit>> ~> B)
  {struct n}
  : Kappa <<B, Vector A n, Unit >> <<B>> :=
match n with
| 0 => <[ \initial _ => initial ]>
| S n' =>
  <[ \initial xs =>
      let '(xs', x) = unsnoc xs in
      !f x (!(foldr f) initial xs')
  ]>
end.

(* non-empty version, doesn't require a default *)
Fixpoint foldr1 {n T}
  (f:  <<T, T, Unit>> ~> T)
  {struct n}
  : Kappa << Vector T (S n), Unit >> <<T>> :=
match n with
| 0 => <[ \x => x[#0] ]>
| S n' =>
  <[ \xs =>
      let '(x, xs') = uncons xs in
      !f x (!(foldr1 f) xs')
  ]>
end.

Fixpoint map {n A B}
  (f :  <<A, Unit>> ~> B)
  : Kappa << Vector A n, Unit >> <<Vector B n>> :=
match n with
| 0 => <[\_ => [] ]>
| S n' =>
  <[ \xs =>
      let '(x, xs') = uncons xs in
      !f x :: (!(map f) xs')
  ]>
end.

Fixpoint map2 {n A B C}
  (f :  <<A, B, Unit>> ~> C)
  : Kappa << Vector A n, Vector B n, Unit >> <<Vector C n>> :=
match n with
| 0 => <[ \x y => [] ]>
| S n' =>
  <[ \xs ys =>
      let '(x, xs') = uncons xs in
      let '(y, ys') = uncons ys in
      !f x y :: (!(map2 f) xs' ys')
  ]>
end.

Fixpoint map3 {n A B C D}
  (f :  <<A, B, C, Unit>> ~> D)
  : Kappa << Vector A n, Vector B n, Vector C n, Unit >> <<Vector D n>> :=
match n with
| 0 => <[ \x y z => [] ]>
| S n' =>
  <[ \xs ys zs =>
      let '(x, xs') = uncons xs in
      let '(y, ys') = uncons ys in
      let '(z, zs') = uncons zs in
      !f x y z :: (!(map3 f) xs' ys' zs')
  ]>
end.

Definition zipper {n A B}
  : Kappa << Vector A n, Vector B n, Unit >> <<Vector <<A,B>> n>> :=
  map2 <[\x y => (x,y) ]>.

Fixpoint equality {T}
  : Kappa << T, T, Unit >> <<Bit>> :=
match T return Kappa << T, T, Unit >> <<Bit>> with
| Unit => <[ \_ _ => true' ]>
| Bit => <[ \x y => xnor x y ]> (* bit equality is the xnor function *)
| Tuple l r => <[
    \x y =>
      let '(a,b) = x in
      let '(c,d) = y in
      and (!equality a c) (!equality b d)
  ]>
| Vector ty n =>
  <[\ x y =>
    let item_equality = !(map2 equality) x y in
    !(foldl <[\x y => and x y]>) true' item_equality
  ]>
end.

Fixpoint replicate {n T}
  : Kappa <<T, Unit>> (Vector T n) :=
match n with
| 0 => <[ \_ => [] ]>
| S n' =>
  <[ \x => x :: !(replicate (n:=n')) x ]>
end.

(* if the enable input is 1 then the vector is return as is,
otherwise a vector of corresponding size is returned with all elements masked out to 0. *)
Definition enable_vec {n}
  : Kappa << Bit, Vector Bit n, Unit >> <<Vector Bit n>> :=
  <[\ enable xs => !(map2 <[\x y => and x y]>) (!replicate enable) xs ]>.

Fixpoint enable {T}
  : Kappa << Bit, T, Unit >> <<T>> :=
match T return Kappa << Bit, T, Unit >> <<T>> with
| Unit => <[ \_ x => x ]>
| Bit => <[ \en x => and en x ]>
| Tuple l r => <[ \en x => let '(a,b) = x in
                  (!enable en a, !enable en b)
                ]>
| Vector ty n => <[\ en x => !(map2 enable) (!replicate en) x ]>
end.

Fixpoint bitwise {T}
  (f:  << Bit, Bit, Unit >> ~> <<Bit>>)
  : Kappa << T, T, Unit >> <<T>> :=
match T return Kappa << T, T, Unit >> <<T>> with
| Unit => <[ \x _ => x ]>
| Bit => <[\x y => !f x y ]>
| Tuple l r => <[ \x y =>
  let '(a,b) = x in
  let '(c,d) = y in
  (!(bitwise f) a c, !(bitwise f) b d)
  ]>
| Vector ty n => <[\x y => !(map2 (bitwise f)) x y ]>
end.

Definition mux_bitvec {n}
  : Kappa << Bit, Vector Bit n, Vector Bit n, Unit >> <<Vector Bit n>> :=
  <[\ switch xs ys =>
      let not_switch = not switch
      in !(map2 <[\x y => or x y ]>) (!enable_vec switch xs) (!enable_vec not_switch ys)
  ]>.

Definition mux_item {T}
  : Kappa << Bit, T, T, Unit >> <<T>> :=
  <[\ switch xs ys => !(bitwise <[or]>) (!enable switch xs) (!enable (not switch) ys) ]>.

(* *************************** *)
(* Combinators *)

Definition below {A B C D E F G: Kind}
  (r:  << A, B, Unit >> ~> << G, D >>)
  (s:  << G, C, Unit >> ~> << F, E >>)
  : Kappa << A, <<B, C>>, Unit >> << F, <<D, E>> >> :=
<[ \ a bc =>
  let '(b, c) = bc in
  let '(g, d) = !r a b in
  let '(f, e) = !s g c in
  (f, (d, e))
]>.

(* Replicate a kind by a right imbalanced tupling of the kind *)
Fixpoint replicateKind A n : Kind :=
  match n with
  | O => Unit
  | S O => A
  | S n => <<A, replicateKind A n>>
  end.

Fixpoint col' {A B C: Kind} n
  (circuit:  << A, B, Unit >> ~> <<A, C>>)
  {struct n}: Kappa
    << A, replicateKind B (S n), Unit >>
    << A, replicateKind C (S n)>> :=
  match n with
  | O => <[ \a b => !circuit a b ]>
  | S n' =>
    let column_below := (col' n' circuit) in
    below circuit column_below
  end.

Lemma col_cons: forall {A B C}
  (circuit: << A, B, Unit >> ~> <<A, C>>),
  forall n, col' (S n) circuit = below circuit (col' n circuit).
Proof. auto. Qed.

Fixpoint productToVec {n T}
  : Kappa << replicateKind T (S n), Unit >> << Vector T (S n) >> :=
  match n with
  | 0 => <[\ x => x :: [] ]>
  | S n' =>
      <[\ xs =>
        let '(x, xs') = xs in
        x :: !productToVec xs'
      ]>
  end.

Fixpoint vecToProduct {n T}
  : Kappa << Vector T (S n), Unit >> << replicateKind T (S n) >> :=
match n with
| 0 => <[\ xs => let '(x,_) = uncons xs in x ]>
| S n' =>
    <[\ xs =>
      let '(x, xs') = uncons xs in
      (x, !vecToProduct xs')
    ]>
end.

Fixpoint interleaveVectors n
  : Kappa
    << Vector Bit (S n), Vector Bit (S n), Unit >>
    << Vector <<Bit, Bit>> (S n) >> :=
match n with
| 0 => <[\ x y => (x[#0], y[#0]) :: [] ]>
| S n =>
    <[\ xs ys =>
    let '(x, xs') = uncons xs in
    let '(y, ys') = uncons ys in
    (x, y) :: (!(interleaveVectors n) xs' ys')
  ]>
end.

Definition col {A B C: Kind} n
  (circuit: << A, B, Unit >> ~> <<A, C>>)
  : Kappa
    << A, Vector B (S n), Unit >>
    << A, Vector C (S n)>> :=
  <[ \a b =>
    let prod_b = !vecToProduct b in
    let '(a, c) = !(col' n circuit) a prod_b in
    (a, !productToVec c)
  ]>.

Definition mealy_machine {s i o}
  (f: <<s, i, Unit>> ~> <<s, o>> )
  : Kappa <<i, Unit>> << o >>
  := <[\i =>
    letrec state_and_output = !f (delay (fst state_and_output)) i
    in (snd state_and_output) ]>.

Definition mealy_machine1 {s i o}
  (fs: <<s, i, Unit>> ~> <<s>> )
  (fo: <<s, i, Unit>> ~> <<o>> )
  : Kappa <<i, Unit>> << o >>
  := <[\i =>
    letrec state = !fs (delay state) i
    in !fo state i ]>.

Section regression_tests.
  Definition halfAdder
  : Kappa << Bit, Bit, Unit >> <<Bit, Bit>> :=
  <[ \ a b =>
    let part_sum = xor a b in
    let carry = and a b in
    (part_sum, carry)
  ]>.

  Definition fullAdder
  : Kappa << Bit, << Bit, Bit >>, Unit >> <<Bit, Bit>> :=
  <[ \ cin ab =>
    let '(a,b) = ab in
    let '(abl, abh) = !halfAdder a b in
    let '(abcl, abch) = !halfAdder abl cin in
    let cout = xor abh abch in
    (abcl, cout)
  ]>.

  Definition rippleCarryAdder' (width: nat)
    : Kappa
      << Bit, Vector <<Bit, Bit>> (S width), Unit >>
      << Bit, Vector Bit (S width) >> :=
  <[ !(col width fullAdder) ]>.

  Definition rippleCarryAdder (width: nat)
    : Kappa
      << Bit, <<Vector Bit (S width), Vector Bit (S width)>>, Unit >>
      << Bit, Vector Bit (S width) >> :=
  <[ \b xy =>
    let '(x,y) = xy in
    let merged = !(interleaveVectors _) x y in
    let '(carry, result) = !(rippleCarryAdder' _) b merged in
    (carry, result)
    ]>.
End regression_tests.

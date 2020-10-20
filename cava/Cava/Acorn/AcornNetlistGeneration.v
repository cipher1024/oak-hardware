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

Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.StateMonad.

From Cava Require Import Acorn.AcornSignal.
From Cava Require Import Acorn.AcornCavaClass.
From Cava Require Import Acorn.AcornNetlist.
From Cava Require Import Acorn.AcornState.

Import MonadNotation.
Local Open Scope monad_scope.

Definition invNet (i : Signal BitType) : state AcornState (Signal BitType) :=
  o <- newWire ;;
  addInstance (Inv i o) ;;
  ret o.

Definition binaryGate (gate : Signal BitType -> Signal BitType -> Signal BitType -> AcornInstance)
                      (i : Signal BitType * Signal BitType)
                      : state AcornState (Signal BitType) :=
  let (i0, i1) := i in
  o <- newWire ;;
  addInstance (gate i0 i1 o) ;;
  ret o.

Instance AcornNetlist : Cava (state AcornState) denoteSignal :=
{ one := Const1;
  zero := Const0;
  inv :=  invNet;
  and2 := binaryGate And2;
  or2 := binaryGate Or2;
  xor2 := binaryGate Xor2;
  pair _ _ a b := Pair a b;
  fsT _ _  := Fst;
  snD _ _ := Snd;
}.

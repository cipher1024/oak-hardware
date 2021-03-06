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

From Coq Require Import Lists.List.
Require Import ExtLib.Structures.Monads.

From Cava Require Import Acorn.AcornSignal.

Inductive AcornInstance : Type :=
  | Inv : Signal Bit -> Signal Bit -> AcornInstance
  | And2 : Signal Bit -> Signal Bit -> Signal Bit -> AcornInstance
  | Or2 : Signal Bit -> Signal Bit -> Signal Bit -> AcornInstance
  | Xor2 : Signal Bit -> Signal Bit -> Signal Bit -> AcornInstance.

Notation AcornNetlist := (list AcornInstance).


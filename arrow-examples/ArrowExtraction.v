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

From Coq Require Import extraction.Extraction.
From Coq Require Import extraction.ExtrHaskellZInteger.
From Coq Require Import extraction.ExtrHaskellString.
From Coq Require Import extraction.ExtrHaskellBasic.
From Coq Require Import extraction.ExtrHaskellNatInteger.

Require Import coqutil.Z.HexNotation.

Set Extraction Optimize.

Extraction Language Haskell.

Require Import Cava.Arrow.Combinators.
Require Import ArrowExamples.SyntaxExamples.
Require Import ArrowExamples.Mux2_1.
Require Import ArrowExamples.UnsignedAdder.
Require Import ArrowExamples.Counter.
Require Import ArrowExamples.Fir.

Require Import ArrowExamples.ArrowAdderTutorial.

Extraction Library Combinators.
Extraction Library SyntaxExamples.
Extraction Library Mux2_1.
Extraction Library UnsignedAdder.
Extraction Library Counter.
Extraction Library Fir.

Extraction Library ArrowAdderTutorial.

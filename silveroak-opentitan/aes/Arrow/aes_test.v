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

Require Import Coq.Arith.Arith Coq.Logic.Eqdep_dec Coq.Vectors.Vector Coq.micromega.Lia
     Coq.NArith.NArith Coq.ZArith.ZArith Coq.Strings.String Coq.NArith.Ndigits.
Require Import Cava.Arrow.ArrowExport Cava.BitArithmetic Cava.VectorUtils.

Require Import AesSpec.Tests.CipherTest AesSpec.Tests.Common.
Require Import Aes.pkg Aes.mix_columns Aes.sbox Aes.sub_bytes Aes.shift_rows Aes.cipher_round.

Require Import coqutil.Z.HexNotation.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

Definition test_key := byte_reverse (n:=32) (N2Bv_sized 256 (Z.to_N (Ox "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"))).
Definition test_data := byte_reverse (n:=16) (N2Bv_sized 128 (Z.to_N (Ox "00112233445566778899aabbccddeeff"))).
Definition test_encrypted := byte_reverse (n:=16) (N2Bv_sized 128 (Z.to_N (Ox "8ea2b7ca516745bfeafc49904b496089"))).

(* Vector.eqb is extracted under a different namespace, so we redefine
* boolean vector equality here *)
Definition vector_equality {n} (v1: Vector.t bool n) (v2: Vector.t bool n) :=
  Vector.fold_left andb true (Vector.map2 Bool.eqb v1 v2).

Definition print_cipher_fwd (cipher: bool -> Vector.t bool 256 -> Vector.t bool 128 -> Vector.t bool 128): Z
  := Z.of_N (Bv2N (byte_reverse (n:=16) (cipher false test_key test_data))).
Definition print_cipher_rev (cipher: bool -> Vector.t bool 256 -> Vector.t bool 128 -> Vector.t bool 128): Z
  := Z.of_N (Bv2N (byte_reverse (n:=16) (cipher true test_key test_encrypted))).

Definition test_cipher_fwd (cipher: bool -> Vector.t bool 256 -> Vector.t bool 128 -> Vector.t bool 128): bool
  := vector_equality (cipher false test_key test_data) test_encrypted.

Definition test_cipher_rev (cipher: bool -> Vector.t bool 256 -> Vector.t bool 128 -> Vector.t bool 128): bool
  := vector_equality (cipher true test_key test_encrypted) test_data.

(* AES-256 expanded empty key *)
(*
0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00 = k0
0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00 = k1
0x62, 0x63, 0x63, 0x63, ~ 0x62, 0x63, 0x63, 0x63, ~ 0x62, 0x63, 0x63, 0x63, ~ 0x62, 0x63, 0x63, 0x63 = k2
0xaa, 0xfb, 0xfb, 0xfb, ~ 0xaa, 0xfb, 0xfb, 0xfb, ~ 0xaa, 0xfb, 0xfb, 0xfb, ~ 0xaa, 0xfb, 0xfb, 0xfb = k3
0x6f, 0x6c, 0x6c, 0xcf, ~ 0x0d, 0x0f, 0x0f, 0xac, ~ 0x6f, 0x6c, 0x6c, 0xcf, ~ 0x0d, 0x0f, 0x0f, 0xac = k4
0x7d, 0x8d, 0x8d, 0x6a, ~ 0xd7, 0x76, 0x76, 0x91, ~ 0x7d, 0x8d, 0x8d, 0x6a, ~ 0xd7, 0x76, 0x76, 0x91 = k5
0x53, 0x54, 0xed, 0xc1, ~ 0x5e, 0x5b, 0xe2, 0x6d, ~ 0x31, 0x37, 0x8e, 0xa2, ~ 0x3c, 0x38, 0x81, 0x0e = k6
0x96, 0x8a, 0x81, 0xc1, ~ 0x41, 0xfc, 0xf7, 0x50, ~ 0x3c, 0x71, 0x7a, 0x3a, ~ 0xeb, 0x07, 0x0c, 0xab = k7
0x9e, 0xaa, 0x8f, 0x28, ~ 0xc0, 0xf1, 0x6d, 0x45, ~ 0xf1, 0xc6, 0xe3, 0xe7, ~ 0xcd, 0xfe, 0x62, 0xe9 = k8
0x2b, 0x31, 0x2b, 0xdf, ~ 0x6a, 0xcd, 0xdc, 0x8f, ~ 0x56, 0xbc, 0xa6, 0xb5, ~ 0xbd, 0xbb, 0xaa, 0x1e = k9
0x64, 0x06, 0xfd, 0x52, ~ 0xa4, 0xf7, 0x90, 0x17, ~ 0x55, 0x31, 0x73, 0xf0, ~ 0x98, 0xcf, 0x11, 0x19 = k10
0x6d, 0xbb, 0xa9, 0x0b, ~ 0x07, 0x76, 0x75, 0x84, ~ 0x51, 0xca, 0xd3, 0x31, ~ 0xec, 0x71, 0x79, 0x2f = k11
0xe7, 0xb0, 0xe8, 0x9c, ~ 0x43, 0x47, 0x78, 0x8b, ~ 0x16, 0x76, 0x0b, 0x7b, ~ 0x8e, 0xb9, 0x1a, 0x62 = k12
0x74, 0xed, 0x0b, 0xa1, ~ 0x73, 0x9b, 0x7e, 0x25, ~ 0x22, 0x51, 0xad, 0x14, ~ 0xce, 0x20, 0xd4, 0x3b = k13
0x10, 0xf8, 0x0a, 0x17, ~ 0x53, 0xbf, 0x72, 0x9c, ~ 0x45, 0xc9, 0x79, 0xe7, ~ 0xcb, 0x70, 0x63, 0x85 = k14
*)

(* Plug aes subroutines into testing infrastructure *)
Definition aes_impl_for_tests
           (step : AESStep) (k st : Vector.t bool 128) : Vector.t bool 128 :=
  (* forward vs inverse direction flag *)
  let FWD := kinterp CIPH_FWD tt in
  let INV := kinterp CIPH_INV tt in
  (* convert between flat-vector representation and state type *)
  (* Note: implementation uses row-major state *)
  let from_flat : Vector.t bool 128 ->
                  denote_kind << Vector (Vector (Vector Bit 8) 4) 4 >> :=
      fun st => Vector.map (Vector.map (fun r => byte_to_bitvec r)) (to_rows st) in
  let to_flat : denote_kind << Vector (Vector (Vector Bit 8) 4) 4 >> ->
                Vector.t bool 128 :=
      fun st => from_rows (Vector.map (Vector.map (fun r => bitvec_to_byte r)) st) in
  match step with
  | AddRoundKey =>
    (* no specific definition for the xor; use spec version *)
    aes_impl step k st
  | SubBytes =>
    to_flat (kinterp (aes_sub_bytes SboxCanright) (FWD, (from_flat st, tt)))
  | InvSubBytes =>
    to_flat (kinterp (aes_sub_bytes SboxCanright) (INV, (from_flat st, tt)))
  | ShiftRows =>
    to_flat (kinterp aes_shift_rows (FWD, (from_flat st, tt)))
  | InvShiftRows =>
    to_flat (kinterp aes_shift_rows (INV, (from_flat st, tt)))
  | MixColumns =>
    to_flat (kinterp aes_mix_columns (FWD, (from_flat st, tt)))
  | InvMixColumns =>
    to_flat (kinterp aes_mix_columns (INV, (from_flat st, tt)))
  end.

(* TODO: native_compute is faster here, but fails on CI because "ocaml compiler
   is not installed" *)
(* Run full encryption test from FIPS *)
Goal (aes_test_encrypt Matrix aes_impl_for_tests = Success).
Proof. vm_compute. reflexivity. Qed.
(* Run full decryption test from FIPS *)
Goal (aes_test_decrypt Matrix aes_impl_for_tests = Success).
Proof. vm_compute. reflexivity. Qed.


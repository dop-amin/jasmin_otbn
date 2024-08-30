(* OpenTitan Big Number architecture. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import strings.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* -------------------------------------------------------------------------- *)
(* OTBN has 30 general purpose registers: x2, ..., x31.
   Register x0 always reads zero.
   Register x1 reads the top of the call stack, so we don't include it. *)

Variant register : Type :=
  | X00 (* TODO_OTBN: x0 is unallocatable. *)
  | X01 (* TODO_OTBN: x1 should not be a register. *)
  | X02 (* Stack pointer. *)
  | X03 | X04 | X05 | X06 | X07 | X08 | X09 | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28
  | X29 | X30 | X31
.

Definition string_of_register (r : register) : string :=
  match r with
  | X00 => "x0"
  | X01 => "x1"
  | X02 => "x2"
  | X03 => "x3"
  | X04 => "x4"
  | X05 => "x5"
  | X06 => "x6"
  | X07 => "x7"
  | X08 => "x8"
  | X09 => "x9"
  | X10 => "x10"
  | X11 => "x11"
  | X12 => "x12"
  | X13 => "x13"
  | X14 => "x14"
  | X15 => "x15"
  | X16 => "x16"
  | X17 => "x17"
  | X18 => "x18"
  | X19 => "x19"
  | X20 => "x20"
  | X21 => "x21"
  | X22 => "x22"
  | X23 => "x23"
  | X24 => "x24"
  | X25 => "x25"
  | X26 => "x26"
  | X27 => "x27"
  | X28 => "x28"
  | X29 => "x29"
  | X30 => "x30"
  | X31 => "x31"
  end.


(* -------------------------------------------------------------------------- *)
(* OTBN has 32 general purpose wide registers: w0, ..., w31. *)

Variant wide_register : Type :=
  | W00 | W01 | W02 | W03 | W04 | W05 | W06 | W07 | W08 | W09 | W10 | W11 | W12
  | W13 | W14 | W15 | W16 | W17 | W18 | W19 | W20 | W21 | W22 | W23 | W24 | W25
  | W26 | W27 | W28 | W29 | W30 | W31

  (* TODO_OTBN: These two shold be extended extra registers. *)
  | ACC | MOD | RND
.

Definition string_of_wide_register (w : wide_register) : string :=
  match w with
  | W00 => "w0"
  | W01 => "w1"
  | W02 => "w2"
  | W03 => "w3"
  | W04 => "w4"
  | W05 => "w5"
  | W06 => "w6"
  | W07 => "w7"
  | W08 => "w8"
  | W09 => "w9"
  | W10 => "w10"
  | W11 => "w11"
  | W12 => "w12"
  | W13 => "w13"
  | W14 => "w14"
  | W15 => "w15"
  | W16 => "w16"
  | W17 => "w17"
  | W18 => "w18"
  | W19 => "w19"
  | W20 => "w20"
  | W21 => "w21"
  | W22 => "w22"
  | W23 => "w23"
  | W24 => "w24"
  | W25 => "w25"
  | W26 => "w26"
  | W27 => "w27"
  | W28 => "w28"
  | W29 => "w29"
  | W30 => "w30"
  | W31 => "w31"
  | ACC => "acc"
  | MOD => "mod"
  | RND => "rnd"
  end.


(* -------------------------------------------------------------------------- *)
(* Flags.
   OTBN has two flag groups, [FG0] and [FG1]. *)

Variant flag : Type :=
  | CF0 | CF1    (* Carry condition flag (overflow). *)
  | MF0 | MF1    (* Most significant bit. *)
  | LF0 | LF1    (* Least significant bit. *)
  | ZF0 | ZF1    (* Zero flag. *)
.

Definition string_of_flag (f : flag) : string :=
  match f with
 | CF0 => "CF0"
 | MF0 => "MF0"
 | LF0 => "LF0"
 | ZF0 => "ZF0"
 | CF1 => "CF1"
 | MF1 => "MF1"
 | LF1 => "LF1"
 | ZF1 => "ZF1"
  end.

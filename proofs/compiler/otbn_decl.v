(* OpenTitan Big Number architecture. *)

From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  expr
  flag_combination
  type
  strings
  utils.
Require Import
  arch_decl
  arch_utils.
Require Export otbn_decl_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Axiom TODO_OTBN : forall {A}, string -> A.
Definition TODO_OTBN_PROOF {A : Prop} : A := TODO_OTBN "proof".

(* -------------------------------------------------------------------------- *)

Scheme Equality for register.

Lemma register_eq_axiom : Equality.axiom register_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_register_dec_bl internal_register_dec_lb).
Qed.

#[export]
Instance eqTC_register : eqTypeC register :=
  {
    ceqP := register_eq_axiom;
  }.

Canonical register_eqType := @ceqT_eqType _ eqTC_register.

Definition registers : seq register :=
  [:: X00; X01; X02; X03; X04; X05; X06; X07; X08; X09; X10; X11; X12; X13; X14
    ; X15 ; X16; X17; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29
    ; X30 ; X31
  ].

Lemma register_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

#[export]
Instance finTC_register : finTypeC register :=
  {
    cenumP := register_fin_axiom;
  }.

Canonical register_finType := @cfinT_finType _ finTC_register.

#[export]
Instance register_toS : ToString sword32 register :=
  {
    category := "register";
    to_string := string_of_register;
  }.


(* -------------------------------------------------------------------------- *)

Scheme Equality for wide_register.

Lemma wide_register_eq_axiom : Equality.axiom wide_register_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_wide_register_dec_bl
       internal_wide_register_dec_lb).
Qed.

#[export]
Instance eqTC_wide_register : eqTypeC wide_register :=
  {
    ceqP := wide_register_eq_axiom;
  }.

Canonical wide_register_eqType := @ceqT_eqType _ eqTC_wide_register.

Definition wide_registers : seq wide_register :=
  [:: W00; W01; W02; W03; W04; W05; W06; W07; W08; W09; W10; W11; W12; W13; W14
    ; W15; W16; W17; W18; W19; W20; W21; W22; W23; W24; W25; W26; W27; W28; W29
    ; W30; W31
    ; ACC; MOD; RND; KEY_S0_L; KEY_S0_H; KEY_S1_L; KEY_S1_H
  ].

Lemma wide_register_fin_axiom : Finite.axiom wide_registers.
Proof. by case. Qed.

#[export]
Instance finTC_wide_register : finTypeC wide_register :=
  {
    cenumP := wide_register_fin_axiom;
  }.

Canonical wide_register_finType := @cfinT_finType _ finTC_wide_register.

#[export]
Instance wide_register_toS : ToString sword256 wide_register :=
  {
    category := "wide register";
    to_string := string_of_wide_register;
  }.


(* -------------------------------------------------------------------------- *)

Scheme Equality for flag.

Lemma flag_eq_axiom : Equality.axiom flag_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_flag_dec_bl internal_flag_dec_lb).
Qed.

#[export]
Instance eqTC_flag : eqTypeC flag :=
  {
    ceqP := flag_eq_axiom;
  }.

Canonical flag_eqType := @ceqT_eqType _ eqTC_flag.

Definition flags : seq flag :=
  [:: CF0; CF1; MF0; MF1; LF0; LF1; ZF0; ZF1 ].

Lemma flag_fin_axiom : Finite.axiom flags.
Proof. by case. Qed.

#[export]
Instance finTC_flag : finTypeC flag :=
  {
    cenumP := flag_fin_axiom;
  }.

Canonical flag_finType := @cfinT_finType _ finTC_flag.

#[export]
Instance flag_toS : ToString sbool flag :=
  {
    category := "rflag";
    to_string := string_of_flag;
  }.


(* -------------------------------------------------------------------------- *)
(* Conditions. *)

Variant condition :=
  | RVcond of bool & register & register
  | BNcond of flag
.

Scheme Equality for condition.

Lemma condition_eq_axiom : Equality.axiom condition_beq.
Proof.
  exact:
    (eq_axiom_of_scheme internal_condition_dec_bl internal_condition_dec_lb).
Qed.

#[export]
Instance eqTC_condition : eqTypeC condition :=
  {
    ceqP := condition_eq_axiom;
  }.


(* -------------------------------------------------------------------- *)
(* Flag combinations. *)

Definition fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  let vcf := FCVar0 in
  let vmf := FCVar1 in
  let vzf := FCVar3 in
  let less := FCVar0 in
  match cfc with
  | CFC_B => vcf
  | CFC_E => vzf
  | CFC_L => FCNot (FCEq vmf vcf)
  | CFC_BE => FCOr vzf vcf
  | CFC_LE => FCOr vzf less
  end.

#[global]
Instance otbn_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := fc_of_cfc;
  }.


(* -------------------------------------------------------------------------- *)
(* Architecture declaration. *)

Definition register_ext := empty.

#[export]
Instance otbn_decl :
  arch_decl register register_ext wide_register flag condition :=
  {
    reg_size := U32;
    xreg_size := U256;
    cond_eqC := eqTC_condition;
    toS_r := register_toS;
    toS_rx := empty_toS sword32;
    toS_x := wide_register_toS;
    toS_f := flag_toS;
    reg_size_neq_xreg_size := refl_equal;
    ad_rsp := X02;
    ad_fcp := otbn_fcp;
  }.

(* TODO_OTBN: Check. *)
Definition otbn_call_conv : calling_convention :=
  let callee_saved_registers :=
    [:: X02; X08; X09; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27 ]
  in
  {|
    callee_saved := map ARReg callee_saved_registers;
    callee_saved_not_bool := refl_equal;
    call_reg_args := [:: X10; X11; X12; X13; X14; X15; X16; X17 ];
    call_xreg_args := [:: W00; W01; W02; W03; W04; W05; W06; W07 ];
    call_reg_ret := [:: X10; X11 ];
    call_xreg_ret:= [:: W00; W01 ];
    call_reg_ret_uniq := refl_equal;
  |}.

(* RISC-V immediate operands must fit in 12 bits. *)
Definition is_w12 (z : Z) : bool := (-2048 <=? z)%Z && (z <=? 2047)%Z.

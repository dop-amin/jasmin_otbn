From mathcomp Require Import
  all_ssreflect
  all_algebra
  word_ssrZ.

Require Import
  otbn_options
  sem_type
  sopn
  strings
  type
  utils
  word
  wsize.
Require Import
  arch_decl
  arch_utils.
Require Import otbn_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local]
Open Scope Z.

Section ASCII.
  Import Ascii.

  #[local]
  Open Scope char_scope.

  Fixpoint replace_dot (s : string) : string :=
    match s with
    | EmptyString => EmptyString
    | String c s =>
        let c' := if c == "." then "_" else c in
        String c' (replace_dot s)
    end.

End ASCII.

Module E.

  Definition no_semantics : error := ErrType.

End E.

(* -------------------------------------------------------------------------- *)
(* OTBN ISA declaration. *)
(* -------------------------------------------------------------------------- *)

(* 32-bit operations. *)
Variant rv_mnemonic :=
  | ADD  (* Addition. *)
  | ADDI (* Addition (immediate). *)
  | SUB  (* Subtraction. *)

  | AND  (* Bitwise AND. *)
  | ANDI (* Bitwise AND (immediate). *)
  | OR   (* Bitwise OR. *)
  | ORI  (* Bitwise OR (immediate). *)
  | XOR  (* Bitwise XOR. *)
  | XORI (* Bitwise XOR (immediate). *)

  | SLL  (* Logical left shift. *)
  | SLLI (* Logical left shift (immediate). *)
  | SRL  (* Logical right shift. *)
  | SRLI (* Logical right shift (immediate). *)
  | SRA  (* Arithmetic right shift. *)
  | SRAI (* Arithmetic right shift (immediate). *)

  | LUI  (* Load upper immediate. *)

  | LW  (* Load word. *)
  | SW  (* Store word. *)

  | LI  (* Load 32 bit immediate. *)
  | LA  (* Load address. *)

  (* TODO_OTBN: Move to otbn_extra. *)
  | MOV  (* Printed as [ADD x, y, x0]. *)
  | NEG  (* Printed as [SUB x, x0, y]. *)

  | NOP (* No operation. *)
.

Scheme Equality for rv_mnemonic.

Lemma rv_mnemonic_eq_axiom : Equality.axiom rv_mnemonic_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_rv_mnemonic_dec_bl
       internal_rv_mnemonic_dec_lb).
Qed.

#[export]
Instance eqTC_rv_mnemonic : eqTypeC rv_mnemonic :=
  {
    ceqP := rv_mnemonic_eq_axiom;
  }.

Canonical rv_mnemonic_eqType := ceqT_eqType (ceqT := eqTC_rv_mnemonic).

Definition rv_mnemonics : seq rv_mnemonic :=
  [:: ADD; ADDI; SUB; AND; ANDI; OR; ORI; XOR; XORI; SLL; SLLI; SRL; SRLI; SRA
    ; SRAI; LUI; LW; SW; LI; LA; MOV; NEG; NOP
  ].

Lemma rv_mnemonic_fin_axiom : Finite.axiom rv_mnemonics.
Proof. by case. Qed.

#[export]
Instance finTC_rv_mnemonic : finTypeC rv_mnemonic :=
  {
    cenumP := rv_mnemonic_fin_axiom;
  }.

Definition string_of_rv_mnemonic (mn : rv_mnemonic) : string :=
  match mn with
  | ADD => "ADD"
  | ADDI => "ADDI"
  | SUB => "SUB"
  | AND => "AND"
  | ANDI => "ANDI"
  | OR => "OR"
  | ORI => "ORI"
  | XOR => "XOR"
  | XORI => "XORI"
  | SLL => "SLL"
  | SLLI => "SLLI"
  | SRL => "SRL"
  | SRLI => "SRLI"
  | SRA => "SRA"
  | SRAI => "SRAI"
  | LUI => "LUI"
  | LW => "LW"
  | SW => "SW"
  | LI => "LI"
  | LA => "LA"
  | MOV => "MOV"
  | NEG => "NEG"
  | NOP => "NOP"
  end.

(* Basic big number arithmetic.
   All these set one of the flag groups and take an optional shift. *)
Variant bn_basic_mnemonic :=
  | BN_ADD   (* Add. *)
  | BN_ADDC  (* Add with carry. *)
  | BN_SUB   (* Subtract. *)
  | BN_SUBB  (* Subtract with borrow. *)

  | BN_AND  (* Bitwise AND. *)
  | BN_OR   (* Bitwise OR. *)
  | BN_NOT  (* Bitwise NOT. *)
  | BN_XOR  (* Bitwise XOR. *)

  | BN_CMP   (* Compare. *)
  | BN_CMPB  (* Compare with borrow. *)
.

Scheme Equality for bn_basic_mnemonic.

Lemma bn_basic_mnemonic_eq_axiom : Equality.axiom bn_basic_mnemonic_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_bn_basic_mnemonic_dec_bl
       internal_bn_basic_mnemonic_dec_lb).
Qed.

#[export]
Instance eqTC_bn_basic_mnemonic : eqTypeC bn_basic_mnemonic :=
  {
    ceqP := bn_basic_mnemonic_eq_axiom;
  }.

Canonical bn_basic_mnemonic_eqType :=
  ceqT_eqType (ceqT := eqTC_bn_basic_mnemonic).

Definition bn_basic_mnemonics : seq bn_basic_mnemonic :=
  [:: BN_ADD; BN_ADDC; BN_SUB; BN_SUBB; BN_AND; BN_OR; BN_NOT; BN_XOR; BN_CMP
    ; BN_CMPB
  ].

Lemma bn_basic_mnemonic_fin_axiom : Finite.axiom bn_basic_mnemonics.
Proof. by case. Qed.

#[export]
Instance finTC_bn_basic_mnemonic : finTypeC bn_basic_mnemonic :=
  {
    cenumP := bn_basic_mnemonic_fin_axiom;
  }.

Definition string_of_bn_basic_mnemonic (mn : bn_basic_mnemonic) : string :=
  match mn with
  | BN_ADD => "BN.ADD"
  | BN_ADDC => "BN.ADDC"
  | BN_SUB => "BN.SUB"
  | BN_SUBB => "BN.SUBB"
  | BN_AND => "BN.AND"
  | BN_OR => "BN.OR"
  | BN_NOT => "BN.NOT"
  | BN_XOR => "BN.XOR"
  | BN_CMP => "BN.CMP"
  | BN_CMPB => "BN.CMPB"
  end.

Variant otbn_op :=
  | RV32 of rv_mnemonic
  | BN_basic of bn_basic_mnemonic & bn_flag_group
  | BN_basic_shift of bn_basic_mnemonic & bn_flag_group & bn_register_shift

  | BN_ADDI of bn_flag_group  (* Add immediate. *)
  | BN_SUBI of bn_flag_group  (* Subtract immediate. *)

  | BN_MOV                   (* Copy content between wide registers. *)
  | BN_RSHI                  (* Concatenate and right shift immediate. *)
  | BN_SEL of bn_flag_group  (* Flag Select. *)

  | BN_ADDM  (* Pseudo-modulo add. *)
  | BN_SUBM  (* Pseudo-modulo subtraction. *)

  (* Quarter-word multiply and accumulate. *)
  | BN_MULQACC
  | BN_MULQACC_Z (* Zero the accumulator first. *)

  (* Quarter-word multiply and accumulate with full-word writeback. *)
  | BN_MULQACC_WO of bn_flag_group
  | BN_MULQACC_WO_Z of bn_flag_group

  (* Quarter-word multiply and accumulate with half-word writeback. *)
  | BN_MULQACC_SO of bn_flag_group & bn_halfword_writeback
  | BN_MULQACC_SO_Z of bn_flag_group & bn_halfword_writeback

  (* Pseudo-instructions. *)
  (* | FGRS of bn_flag_group (* Atomic read and set bits in flag group. *)
  | FGRW of bn_flag_group (* Atomic read and write in flag group. *) *)
  | BN_ACCR  (* Read from ACC register to wide register. *)
  | BN_ACCW  (* Write from wide register to ACC register. *)
  | BN_MODR  (* Read from MOD register to wide register. *)
  | BN_MODW  (* Write from wide register to MOD register. *)
  | BN_RNDR  (* Read from RND register to wide register. *)
  | BN_RNDW  (* Write from wide register to RND register (ignored). *)
  | BN_KEY_S0_L_R  (* Read from KEY_S0_L register to wide register. *)
  | BN_KEY_S0_L_W  (* Write to KEY_S0_L register is ignored. *)
  | BN_KEY_S0_H_R  (* Read from KEY_S0_H register to wide register. *)
  | BN_KEY_S0_H_W  (* Write to KEY_S0_H register is ignored. *)
  | BN_KEY_S1_L_R  (* Read from KEY_S1_L register to wide register. *)
  | BN_KEY_S1_L_W  (* Write to KEY_S1_L register is ignored. *)
  | BN_KEY_S1_H_R  (* Read from KEY_S1_H register to wide register. *)
  | BN_KEY_S1_H_W  (* Write to KEY_S1_H register is ignored. *)

  | BN_LID
  | BN_SID
.

Scheme Equality for otbn_op.

Lemma otbn_op_eq_axiom : Equality.axiom otbn_op_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_otbn_op_dec_bl internal_otbn_op_dec_lb).
Qed.

#[export]
Instance eqTC_otbn_op : eqTypeC otbn_op :=
  {
    ceqP := otbn_op_eq_axiom;
  }.

Canonical otbn_op_eqType := ceqT_eqType (ceqT := eqTC_otbn_op).

Definition string_of_otbn_op (op : otbn_op) : string :=
  match op with
  | RV32 mn => string_of_rv_mnemonic mn
  | BN_basic mn _ => string_of_bn_basic_mnemonic mn
  | BN_basic_shift mn _ _ => string_of_bn_basic_mnemonic mn
  | BN_ADDI _ => "BN.ADDI"
  | BN_SUBI _ => "BN.SUBI"
  | BN_MOV => "BN.MOV"
  | BN_RSHI => "BN.RSHI"
  | BN_SEL _ => "BN.SEL"
  | BN_ADDM => "BN.ADDM"
  | BN_SUBM => "BN.SUBM"
  | BN_MULQACC => "BN.MULQACC"
  | BN_MULQACC_Z => "BN.MULQACC.Z"
  | BN_MULQACC_WO _ => "BN.MULQACC.WO"
  | BN_MULQACC_WO_Z _ => "BN.MULQACC.WO.Z"
  | BN_MULQACC_SO _ _ => "BN.MULQACC.SO"
  | BN_MULQACC_SO_Z _ _ => "BN.MULQACC.SO.Z"
  (*| FGRS _ => "FGRS"
  | FGRW _ => "FGRW"*)
  | BN_ACCR => "BN.ACCR"
  | BN_ACCW => "BN.ACCW"
  | BN_MODR => "BN.MODR"
  | BN_MODW => "BN.MODW"
  | BN_RNDR => "BN.RNDR"
  | BN_RNDW => "BN.RNDW"
  | BN_KEY_S0_L_R => "BN.KEY_S0_L_R"
  | BN_KEY_S0_L_W => "BN.KEY_S0_L_W"
  | BN_KEY_S0_H_R => "BN.KEY_S0_H_R"
  | BN_KEY_S0_H_W => "BN.KEY_S0_H_W"
  | BN_KEY_S1_L_R => "BN.KEY_S1_L_R"
  | BN_KEY_S1_L_W => "BN.KEY_S1_L_W"
  | BN_KEY_S1_H_R => "BN.KEY_S1_H_R"
  | BN_KEY_S1_H_W => "BN.KEY_S1_H_W"
  | BN_LID => "BN.LID"
  | BN_SID => "BN.SID"
  end.

(* -------------------------------------------------------------------------- *)
(* Instruction descriptions. *)
(* -------------------------------------------------------------------------- *)

(* TODO_OTBN: This must disallow IP relative addresses. *)
Definition E n := ADExplicit AK_mem n None.

Section I_ARGS_KINDS.

  Let xreg := [:: CAxmm ].
  Let imm8 := [:: CAimm U8 ].
  Let imm256 := [:: CAimm U256 ].

  Definition ak_xreg : i_args_kinds :=
    [:: [:: xreg ] ].

  Definition ak_xreg_xreg : i_args_kinds :=
    [:: [:: xreg; xreg ] ].

  Definition ak_xreg_xreg_imm256 : i_args_kinds :=
    [:: [:: xreg; xreg; imm256 ] ].

  Definition ak_xreg_xreg_xreg : i_args_kinds :=
    [:: [:: xreg; xreg; xreg ] ].

  Definition ak_xreg_xreg_xreg_bool : i_args_kinds :=
    [:: [:: xreg; xreg; xreg; [:: CAcond ] ] ].

  Definition ak_xreg_xreg_xreg_imm8 : i_args_kinds :=
    [:: [:: xreg; xreg; xreg; imm8 ] ].

  Definition ak_xreg_imm8_xreg_imm8_imm8 : i_args_kinds :=
    [:: [:: xreg; imm8; xreg; imm8; imm8 ] ].

  Definition ak_xreg_xreg_imm8_xreg_imm8_imm8 : i_args_kinds :=
    [:: [:: xreg; xreg; imm8; xreg; imm8; imm8 ] ].

  Definition ak_xreg_reg_mem : i_args_kinds :=
    [:: [:: [:: CAxmm ]; [:: CAreg ]; [:: CAmem true ] ]].

  Definition ak_mem_reg_xreg : i_args_kinds :=
    [:: [:: [:: CAmem true ]; [:: CAreg ]; [:: CAxmm ] ]].

End I_ARGS_KINDS.


Section PP_ASM_OP.
  (* We need to catch the pseudo-instructions [FGRS], [FGRW], [BN_ACCR],
     [BN_ACCW], [BN_MODR], and [BN_MODW], and print them as csrrs, csrrw,
     bn.wsrr, and bn.wsrw with the appropriate number as an argument.

     TODO_OTBN: We also need to replace on [MOV] and [NEG] until they are extra
     operations. *)

  Let error : pp_asm_op :=
    {|
      pp_aop_name := "ERROR";
      pp_aop_ext := PP_error;
      pp_aop_args := [::];
    |}.

  Let mk (name : string) (args : seq asm_arg) : pp_asm_op :=
    {|
      pp_aop_name := name;
      pp_aop_ext := PP_name;
      pp_aop_args := map (fun a => (reg_size, a)) args;
    |}.

  Let x0 : asm_arg := Reg X00.

  Let wr_number (op : otbn_op) : asm_arg :=
    let err :=
      {| ad_disp := 0%R; ad_base := None; ad_scale := 0; ad_offset := None; |}
    in
    match op with
    | BN_MODR | BN_MODW => Imm (wrepr U8 0x0)
    | BN_RNDR | BN_RNDW => Imm (wrepr U8 0x1)
    | BN_ACCR | BN_ACCW => Imm (wrepr U8 0x3)
    | BN_KEY_S0_L_R | BN_KEY_S0_L_W => Imm (wrepr U8 0x4)
    | BN_KEY_S0_H_R | BN_KEY_S0_H_W => Imm (wrepr U8 0x5)
    | BN_KEY_S1_L_R | BN_KEY_S1_L_W => Imm (wrepr U8 0x6)
    | BN_KEY_S1_H_R | BN_KEY_S1_H_W => Imm (wrepr U8 0x7)
    | _ => Addr (Areg err) (* Never happens, will give an error. *)
    end.

  Definition pp_otbn_op
    (op : otbn_op) (_ : wsize) (args : seq asm_arg) : pp_asm_op :=
    match op with
    | RV32 MOV => mk (string_of_rv_mnemonic ADD) (rcons args x0)
    | RV32 NEG =>
        if ohead args is Some a0
        then mk (string_of_rv_mnemonic SUB) (a0 :: x0 :: behead args)
        else error
    | BN_ACCR | BN_MODR | BN_RNDR | BN_KEY_S0_L_R | BN_KEY_S0_H_R | BN_KEY_S1_L_R | BN_KEY_S1_H_R => mk "bn.wsrr" (rcons args (wr_number op))
    | BN_ACCW | BN_MODW | BN_RNDW | BN_KEY_S0_L_W | BN_KEY_S0_H_W | BN_KEY_S1_L_W | BN_KEY_S1_H_W => mk "bn.wsrw" (wr_number op :: args)
    | _ => mk (string_of_otbn_op op) args
    end.

End PP_ASM_OP.


(* -------------------------------------------------------------------------- *)
(* Instruction descriptions for the 32-bit ISA.
   These instructions are unary or binary word operations, so we define generic
   instruction descriptions [desc_rv_unop] and [desc_rv_binop]. *)

Section RV_DESC.

Context
  (ws : wsize)
  (mn : rv_mnemonic)
.

(* All RV instructions have a register as a first argument.
   Then they may take some more registers, and finally either a register, an
   immediate or an address. *)

Let ak_unary ak := [:: [:: [:: CAreg ]; [:: ak ]]].
Let ak_binary ak := [:: [:: [:: CAreg ]; [:: CAreg ]; [:: ak ]]].

Let pp_rv_op mn args := pp_otbn_op (RV32 mn) reg_size args.

(* Return the kind of the last argument and the check that needs to be performed
   on it (usually only for immediates). *)
Definition rv_chk_args : arg_kind * (word ws -> exec unit) :=
  let no_chk _ := ok tt in
  let ichk interp imin imax x :=
    let i := interp x in
    assert [&& imin <=? i & i <=? imax ] E.no_semantics
  in
  let reg := (CAreg, no_chk) in
  let imm interp imin imax := (CAimm reg_size, ichk interp imin imax) in
  let addr := (CAmem true, no_chk) in
  match mn with
  | ADD | SUB | AND | OR | XOR | SLL | SRL | SRA => reg
  | ADDI | ANDI | ORI | XORI => imm wsigned (-2048) 2047
  | SLLI | SRLI | SRAI => imm wunsigned 0 31
  | LUI => imm wunsigned 0 1048575
  | LW => addr
  | SW => addr
  | LI => imm wunsigned 0 (wbase reg_size)
  | MOV | NEG => reg
  | LA => addr
  | NOP => addr (* Never happens. *)
  end.

Definition _desc_rv_unop
  (ad_in ad_out : arg_desc) (semi : word ws -> word ws) : instr_desc_t :=
  let '(ak, chk) := rv_chk_args in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws ];
    id_in := [:: ad_in ];
    id_tout := [:: sword ws ];
    id_out := [:: ad_out ];
    id_semi := fun x => chk x >> ok (semi x);
    id_nargs := 2;
    id_args_kinds := ak_unary ak;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by case: ad_out);
    id_str_jas := pp_s (string_of_rv_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_rv_op mn;
  |}.

Let desc_rv_unop := _desc_rv_unop (E 1) (E 0).

Definition desc_rv_binop
  (semi : word ws -> word ws -> word ws) : instr_desc_t :=
  let '(ak, chk) := rv_chk_args in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws ];
    id_in := [:: E 1; E 2 ];
    id_tout := [:: sword ws ];
    id_out := [:: E 0 ];
    id_semi := fun x y => chk y >> ok (semi x y);
    id_nargs := 3;
    id_args_kinds := ak_binary ak;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_rv_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_rv_op mn;
  |}.

Definition desc_rv_nop
  : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: ];
    id_in := [:: ];
    id_tout := [:: ];
    id_out := [:: ];
    id_semi := ok tt;
    id_nargs := 0;
    id_args_kinds := [:: [:: ]];
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_rv_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_rv_op mn;
  |}.

Definition _desc_rv_mnemonic : instr_desc_t :=
  let wshl' x y := wshl x (wunsigned y) in
  let wshr' x y := wshr x (wunsigned y) in
  let wsar' x y := wsar x (wunsigned y) in
  match mn with
  | ADD | ADDI => desc_rv_binop wadd
  | SUB => desc_rv_binop wsub
  | AND | ANDI => desc_rv_binop wand
  | OR | ORI => desc_rv_binop wor
  | XOR | XORI => desc_rv_binop wxor
  | SLL | SLLI => desc_rv_binop wshl'
  | SRL | SRLI => desc_rv_binop wshr'
  | SRA | SRAI => desc_rv_binop wsar'
  | LUI => desc_rv_unop (fun x => wshl x 12)
  | LW => desc_rv_unop id
  | SW => _desc_rv_unop (E 0) (E 1) id
  | LI => desc_rv_unop id
  | LA => _desc_rv_unop (Ec 1) (E 0) id
  | MOV => desc_rv_unop id
  | NEG => desc_rv_unop wneg
  | NOP => desc_rv_nop
  end.

End RV_DESC.

(* TODO_OTBN: Right now we only use ws = U32, but we define it generically. *)
Notation desc_rv_mnemonic := (_desc_rv_mnemonic reg_size) (only parsing).


(* -------------------------------------------------------------------------- *)
(* Big Number ISA. *)

(* Check if a number falls in the range from [lo] to [hi] in steps of [step]. *)
Definition is_range_steps (x lo hi step : Z) : bool :=
  [&& lo <=? x, x <=? hi & x mod step == 0 ].

Definition chk_range_steps (x lo hi step : Z) : exec unit :=
  assert (is_range_steps x lo hi step) E.no_semantics.

Definition chk_range (x lo hi : Z) : exec unit := chk_range_steps x lo hi 1.

Definition ty_cmlz : seq stype :=
  [:: sbool; sbool; sbool; sbool ].

Section CURRENT_FLAG_GROUP.

Context (fg : bn_flag_group).

Definition current_cmlz : seq flag :=
  match fg with
  | FG0 => [:: CF0; MF0; LF0; ZF0 ]
  | FG1 => [:: CF1; MF1; LF1; ZF1 ]
  end.

Definition current_CF : flag :=
  match fg with
  | FG0 => CF0
  | FG1 => CF1
  end.

Definition ad_cmlz : seq arg_desc :=
  map F current_cmlz.

End CURRENT_FLAG_GROUP.

#[local]
Ltac t_case_ad_cmlz fg :=
  rewrite /ad_cmlz /current_cmlz;
  case: fg.

Definition CF_of_Z (z : Z) (ws : wsize) : option bool :=
  Some (Z.land (Z.shiftr z (nat_of_wsize ws)) 1 == 0).

Definition MF_of_word {ws : wsize} (res : word ws) : option bool :=
  Some (msb res).

Definition LF_of_word {ws : wsize} (res : word ws) : option bool :=
  Some (lsb res).

Definition ZF_of_word {ws : wsize} (res : word ws) : option bool :=
  Some (res == 0)%R.

Definition with_cmlz
  {ws : wsize}
  (res : word ws)
  (res_unsigned : Z) :
  sem_tuple (ty_cmlz ++ [:: sword ws ]) :=
  (:: CF_of_Z res_unsigned ws
    , MF_of_word res
    , LF_of_word res
    , ZF_of_word res
    & res
  ).

Definition drop_c (idt : instr_desc_t) : instr_desc_t := idt_drop1 idt.

(* -------------------------------------------------------------------------- *)
(* Basic BN mnemonics.
   Several basic BN mnemonics are word operations that shift their last
   argument. Some set flags, and some take the carry flag as input.
   We define generic [instr_desc_t] for these parameterized by the semantics
   (modular and Z semantics for the ones that set flags).
   These are
   - Those that set flags, e.g. [BN_ADD]: [desc_bn_basic_binop_cmlz].
   - Those that don't set the [C] flag, e.g. [BN_AND]:
     [desc_bn_basic_unop_mlz] and [desc_bn_basic_binop_mlz].
   - Those that use the carry flag, e.g. [BN_ADDC]: [desc_bn_basic_carry_binop].
   The instructions [BN_CMP] and [BN_CMPB] are special cases. *)

(* Valid range for [shift_bits] in the reference manual: 0 to 248 in steps of
   8. *)
Definition word_shift_of_reg_shift
  (sh : bn_register_shift)
  {ws : wsize}
  (x : word ws)
  (sham : Z) :
  exec (word ws) :=
  Let _ := chk_range_steps sham 0 248 8 in
  let f :=
    match sh with
    | RS_left => wshl
    | RS_right => wshr
    end
  in
  ok (f ws x sham).

Definition Z_shift_of_reg_shift
 (sh : bn_register_shift) {ws : wsize} (x : word ws) (sham : Z) : Z :=
  let f :=
    match sh with
    | RS_left => Z.shiftl
    | RS_right => Z.shiftr
    end
  in
  f (wunsigned x) sham.

#[local]
Notation rtuple_drop5th xs :=
  (Let: (:: x0, x1, x2, x3 & x4 ) := xs in ok (:: x0, x1, x2 & x3 ))
  (only parsing).

Section BN_BASIC_DESC.

Context
  (ws : wsize)
  (mn : bn_basic_mnemonic)
  (fg : bn_flag_group)
.

Notation current_cmlz := (current_cmlz fg) (only parsing).
Notation current_CF := (current_CF fg) (only parsing).
Notation ad_cmlz := (ad_cmlz fg) (only parsing).
Tactic Notation "t_case_ad_cmlz" := t_case_ad_cmlz fg.

Let pp_bn_basic_op mn args := pp_otbn_op (BN_basic mn fg) xreg_size args.

Let semi_unop_cmlz
  (semi : word ws -> word ws)
  (semiZ : Z -> Z) :
  semi_type [:: sword ws ] (ty_cmlz ++ [:: sword ws ]) :=
  fun x =>
    let res_unsigned := semiZ (wunsigned x) in
    ok (with_cmlz (semi x) res_unsigned).

Let semi_binop_cmlz
  (chk : word ws -> exec unit)
  (semi : word ws -> word ws -> word ws)
  (semiZ : Z -> Z -> Z) :
  semi_type [:: sword ws; sword ws ] (ty_cmlz ++ [:: sword ws ]) :=
  fun x y =>
    Let _ := chk y in
    let res_unsigned := semiZ (wunsigned x) (wunsigned y) in
    ok (with_cmlz (semi x y) res_unsigned).

(* TODO_OTBN: Use [mk_shifted]. *)
Definition shifted_semi_carry_binop_cmlz
  (sh : bn_register_shift)
  (semi : word ws -> word ws -> word ws)
  (semiZ : Z -> Z -> Z) :
  semi_type
    [:: sword ws; sword ws; sbool; sword8 ]
    (ty_cmlz ++ [:: sword ws ]) :=
  fun x y cf wsham =>
    let sham := wunsigned wsham in
    Let y_shifted := word_shift_of_reg_shift sh y sham in
    let c := Z.b2z cf in
    let res := semi (semi x y_shifted) (wrepr ws c) in
    let res_unsigned :=
      semiZ (semiZ (wunsigned x) (Z_shift_of_reg_shift sh y sham)) c
    in
    ok (with_cmlz res res_unsigned).

Let semi_carry_binop_cmlz semi semiZ x y cf :=
  shifted_semi_carry_binop_cmlz RS_left semi semiZ x y cf 0%R.

Definition desc_bn_basic_unop
  (semi : word ws -> word ws) (semiZ : Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws ];
    id_in := [:: E 1 ];
    id_tout := ty_cmlz ++ [:: sword ws ];
    id_out := ad_cmlz ++ [:: E 0 ];
    id_semi := semi_unop_cmlz semi semiZ;
    id_nargs := 2;
    id_args_kinds := ak_xreg_xreg;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_bn_basic_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_bn_basic_op mn;
  |}.

Let desc_un_mlz semi semiZ := drop_c (@desc_bn_basic_unop semi semiZ).

Definition desc_bn_basic_binop
  (semi : word ws -> word ws -> word ws) (semiZ : Z -> Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws ];
    id_in := [:: E 1; E 2 ];
    id_tout := ty_cmlz ++ [:: sword ws ];
    id_out := ad_cmlz ++ [:: E 0 ];
    id_semi := semi_binop_cmlz (fun _ => ok tt) semi semiZ;
    id_nargs := 3;
    id_args_kinds := ak_xreg_xreg_xreg;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_bn_basic_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_bn_basic_op mn;
  |}.

Let desc_bin_mlz semi semiZ := idt_drop1 (desc_bn_basic_binop semi semiZ).

Definition desc_bn_basic_carry_binop
  (semi : word ws -> word ws -> word ws) (semiZ : Z -> Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws; sbool ];
    id_in := [:: E 1; E 2; F current_CF ];
    id_tout := ty_cmlz ++ [:: sword ws ];
    id_out := ad_cmlz ++ [:: E 0 ];
    id_semi := semi_carry_binop_cmlz semi semiZ;
    id_nargs := 3;
    id_args_kinds := ak_xreg_xreg_xreg;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_bn_basic_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_bn_basic_op mn;
  |}.

Definition desc_BN_CMP : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws ];
    id_in := [:: E 0; E 1 ];
    id_tout := ty_cmlz;
    id_out := ad_cmlz;
    id_semi :=
      fun x y =>
        rtuple_drop5th (semi_binop_cmlz (fun _ => ok tt) wsub Z.sub x y);
    id_nargs := 2;
    id_args_kinds := ak_xreg_xreg;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_bn_basic_mnemonic BN_CMP);
    id_safe := [::];
    id_pp_asm := pp_bn_basic_op BN_CMP;
  |}.

Definition desc_BN_CMPB : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws; sbool ];
    id_in := [:: E 0; E 1; F current_CF ];
    id_tout := ty_cmlz;
    id_out := ad_cmlz;
    id_semi :=
      fun x y cf => rtuple_drop5th (semi_carry_binop_cmlz wsub Z.sub x y cf);
    id_nargs := 2;
    id_args_kinds := ak_xreg_xreg;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_bn_basic_mnemonic BN_CMPB);
    id_safe := [::];
    id_pp_asm := pp_bn_basic_op BN_CMPB;
  |}.

Definition _desc_bn_basic_mnemonic : instr_desc_t :=
  match mn with
  | BN_ADD => desc_bn_basic_binop wadd Z.add
  | BN_ADDC => desc_bn_basic_carry_binop wadd Z.add
  | BN_SUB => desc_bn_basic_binop wsub Z.sub
  | BN_SUBB => desc_bn_basic_carry_binop wsub Z.sub
  | BN_AND => desc_bin_mlz wand Z.land
  | BN_OR => desc_bin_mlz wor Z.lor
  | BN_NOT => desc_un_mlz wnot Z.lnot
  | BN_XOR => desc_bin_mlz wxor Z.lxor
  | BN_CMP => desc_BN_CMP
  | BN_CMPB => desc_BN_CMPB
  end.

End BN_BASIC_DESC.

Notation desc_bn_basic_mnemonic :=
  (_desc_bn_basic_mnemonic xreg_size) (only parsing).


Section BN_BASIC_SHIFT_DESC.

Let mk_shifted_semi_unop
  sh ws oT : semi_type [:: sword ws ] oT -> semi_type [:: sword ws; sword8 ] oT
  := mk_shifted_semi_unop (@word_shift_of_reg_shift sh).

Let mk_shifted_semi_binop_2
  sh ws oT ty0 :
  semi_type [:: ty0; sword ws ] oT ->
  semi_type [:: ty0; sword ws; sword8 ] oT
  := mk_shifted_semi_binop_2 (@word_shift_of_reg_shift sh).

Let xsemi x fg := id_semi (desc_bn_basic_mnemonic x fg).

Notation mk_shifted_un x fg sh :=
  (mk_shifted (mk_shifted_semi_unop sh (xsemi x fg))).
Notation mk_shifted_bin x fg sh :=
  (mk_shifted (mk_shifted_semi_binop_2 sh (xsemi x fg))).

Notation mk_shifted_carry x fg sh semi semiZ :=
  (mk_shifted
     (idt := desc_bn_basic_mnemonic x fg)
     (shifted_semi_carry_binop_cmlz sh semi semiZ)).

Definition desc_bn_basic_shift_mnemonic
  (mn : bn_basic_mnemonic)
  (fg : bn_flag_group)
  (sh : bn_register_shift) :
  instr_desc_t :=
  match mn with
  | BN_ADD => mk_shifted_bin BN_ADD fg sh
  | BN_SUB => mk_shifted_bin BN_SUB fg sh
  | BN_AND => mk_shifted_bin BN_AND fg sh
  | BN_OR => mk_shifted_bin BN_OR fg sh
  | BN_XOR => mk_shifted_bin BN_XOR fg sh
  | BN_CMP => mk_shifted_bin BN_CMP fg sh
  | BN_NOT => mk_shifted_un BN_NOT fg sh
  | BN_ADDC => mk_shifted_carry BN_ADDC fg sh wadd Z.add
  | BN_SUBB => mk_shifted_carry BN_SUBB fg sh wsub Z.sub
  | BN_CMPB =>
      let shifted := shifted_semi_carry_binop_cmlz sh wsub Z.sub in
      let semi x y cf sham := rtuple_drop5th (shifted x y cf sham) in
      mk_shifted (idt := desc_bn_basic_mnemonic BN_CMPB fg) semi
  end.

End BN_BASIC_SHIFT_DESC.


(* -------------------------------------------------------------------------- *)
(* Modular BN mnemonics.
   These are arithmetic operations modulo some number (in the [MOD] register).
   We define a generic instruction description parameterized by the integer
   semantics. *)

Section MODULAR_OP.

Definition semi_modular_binop
  (ws : wsize)
  (semiZ : Z -> Z -> Z) :
  semi_type [:: sword ws; sword ws; sword ws ] [:: sword ws ] :=
  fun wx wy wm =>
    let m := wunsigned wm in
    let res := semiZ (wunsigned wx) (wunsigned wy) in
    let res_m :=
      if res <=? 0
      then res + m
      else if res >=? m then res - m else res
    in
    ok (wrepr ws (res_m / wbase ws)).

(* TODO_OTBN: Right now we only use ws = U256, but we define it
   generically. *)
Definition _desc_otbn_op_modular_binop
  (mn : otbn_op) (ws : wsize) (semiZ : Z -> Z -> Z) : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws; sword ws ];
    id_in := [:: E 1; E 2; Xreg MOD ];
    id_tout := [:: sword ws ];
    id_out := [:: E 0 ];
    id_semi := semi_modular_binop semiZ;
    id_nargs := 3;
    id_args_kinds := ak_xreg_xreg_xreg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op mn);
    id_safe := [::];
    id_pp_asm := pp_otbn_op mn xreg_size;
  |}.

Let desc_otbn_op_modular_binop mn := _desc_otbn_op_modular_binop mn U256.

Definition desc_BN_ADDM : instr_desc_t :=
  desc_otbn_op_modular_binop BN_ADDM Z.add.

Definition desc_BN_SUBM : instr_desc_t :=
  desc_otbn_op_modular_binop BN_SUBM Z.sub.

End MODULAR_OP.

Definition semi_binopI_cmlz
  (ws : wsize)
  (chk : word ws -> exec unit)
  (semi : word ws -> word ws -> word ws)
  (semiZ : Z -> Z -> Z) :
  semi_type [:: sword ws; sword ws ] (ty_cmlz ++ [:: sword ws ]) :=
  fun x y =>
    Let _ := chk y in
    let res := semi x y in
    let res_unsigned := semiZ (wunsigned x) (wunsigned y) in
    ok (with_cmlz res res_unsigned).

Definition _desc_bn_binopI
  (ws : wsize)
  (op : otbn_op)
  (fg : bn_flag_group)
  (semi : word ws -> word ws -> word ws)
  (semiZ : Z -> Z -> Z) :
  instr_desc_t :=
  let chk x := assert (wunsigned x <=? 1023) E.no_semantics in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws ];
    id_in := [:: E 1; E 2 ];
    id_tout := ty_cmlz ++ [:: sword ws ];
    id_out := ad_cmlz fg ++ [:: E 0 ];
    id_semi := semi_binopI_cmlz chk semi semiZ;
    id_nargs := 3;
    id_args_kinds := ak_xreg_xreg_imm256;
    id_eq_size := ltac:(by t_case_ad_cmlz fg);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz fg);
    id_str_jas := pp_s (string_of_otbn_op op);
    id_safe := [::];
    id_pp_asm := pp_otbn_op op ws;
  |}.

Definition desc_bn_binopI := _desc_bn_binopI (ws := xreg_size).

Definition desc_BN_MOV : instr_desc_t :=
  let ws := xreg_size in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws ];
    id_in := [:: E 1 ];
    id_tout := [:: sword ws ];
    id_out := [:: E 0 ];
    id_semi := fun x => ok x;
    id_nargs := 2;
    id_args_kinds := ak_xreg_xreg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op BN_MOV);
    id_safe := [::];
    id_pp_asm := pp_otbn_op BN_MOV ws;
  |}.

Definition desc_BN_SEL (fg : bn_flag_group) : instr_desc_t :=
  let ws := xreg_size in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword ws; sword ws; sbool ];
    id_in := [:: E 1; E 2; E 3 ];
    id_tout := [:: sword ws ];
    id_out := [:: E 0 ];
    id_semi := fun wn wm b => ok (if b then wn else wm);
    id_nargs := 4;
    id_args_kinds := ak_xreg_xreg_xreg_bool;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op (BN_SEL fg));
    id_safe := [::];
    id_pp_asm := pp_otbn_op (BN_SEL fg) xreg_size;
  |}.


(* Reference manual:

       Concatenate and right shift immediate.

       Syntax:
           BN.RSHI <wrd>, <wrs1>, <wrs2> >> <imm>

       Concatenates the content of WDRs referenced by wrs1 and wrs2 (wrs1 forms
       the upper part), shifts it right by an immediate value and truncates to
       WLEN bit.
       The result is stored in the WDR referenced by wrd.

   Remark: we are not modeling the semantics exactly as specified because we
   don't have a [u512] type. *)

Definition semi_BN_RSHI (x y : u256) (wsham : u8) : exec u256 :=
  let sham := wunsigned wsham in
  Let _ := chk_range sham 0 255 in
  let lo_part := wshr y sham in
  let hi_part := wshl x (256 - sham) in
  ok (wor hi_part lo_part).

Definition desc_BN_RSHI : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sword256; sword256; sword U8 ];
    id_in := [:: E 1; E 2; E 3 ];
    id_tout := [:: sword256 ];
    id_out := [:: E 0 ];
    id_semi := semi_BN_RSHI;
    id_nargs := 4;
    id_args_kinds := ak_xreg_xreg_xreg_imm8;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op BN_RSHI);
    id_safe := [::];
    id_pp_asm := pp_otbn_op BN_RSHI xreg_size;
  |}.


(* -------------------------------------------------------------------------- *)
(* [MULQACC]. *)

Section MULQACC.

Context
  (fg : bn_flag_group)
  (wb : bn_halfword_writeback)
.

Notation ty_mlz := (behead ty_cmlz).
Notation current_mlz := (behead (current_cmlz fg)).
Notation ad_mlz := (behead (ad_cmlz fg)).
Tactic Notation "t_case_ad_cmlz" := t_case_ad_cmlz fg.

(* Extract the [n]-bit subword starting at [i]. *)
Definition extract_subword {ws : wsize} (x : word ws) (i n : Z) : word ws :=
  wand (wshr x (i * n)) (wrepr ws (Z.shiftl 1 n - 1)).

(* Get the [i]-th 64-bit word of a 256-bit word. *)
Definition get_qword (x : u256) (ix : u8) : exec u256 :=
  let i := wunsigned ix in
  Let _ := chk_range i 0 3 in
  ok (extract_subword x i 64).

Definition shift_mulqacc (x : u256) (wsham : u8) : exec u256 :=
  let sham := wunsigned wsham in
  Let _ := chk_range_steps sham 0 192 64 in
  ok (wshl x sham).

Let base_mulqacc_tin :=
  [:: sword256; sword8; sword256; sword8; sword256; sword8 ].

Let base_mulqacc_z_tin :=
  [:: sword256; sword8; sword256; sword8; sword8 ].

Definition semi_BN_MULQACC : semi_type base_mulqacc_tin [:: sword256 ] :=
  fun x ix y iy acc sham =>
    Let x_sub := get_qword x ix in
    Let y_sub := get_qword y iy in
    Let mul_res := shift_mulqacc (x_sub * y_sub) sham in
    ok (acc + mul_res)%R.

(* Reference manual:

       Quarter-word Multiply and Accumulate.

       Syntax:
           BN.MULQACC[<zero_acc>]
             <wrs1>.<wrs1_qwsel>,
             <wrs2>.<wrs2_qwsel>,
             <acc_shift_imm>

       Multiplies two WLEN/4 WDR values, shifts the product by acc_shift_imm
       bits, and adds the result to the accumulator. *)

Definition desc_BN_MULQACC : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_tin;
    id_in := [:: E 0; E 1; E 2; E 3; Xreg ACC; E 4 ];
    id_tout := [:: sword256 ];
    id_out := [:: Xreg ACC ];
    id_semi := semi_BN_MULQACC;
    id_nargs := 5;
    id_args_kinds := ak_xreg_imm8_xreg_imm8_imm8;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op BN_MULQACC);
    id_safe := [::];
    id_pp_asm := pp_otbn_op BN_MULQACC xreg_size;
  |}.

Definition desc_BN_MULQACC_Z : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_z_tin;
    id_in := [:: E 0; E 1; E 2; E 3; E 4 ];
    id_tout := [:: sword256 ];
    id_out := [:: Xreg ACC ];
    id_semi := fun x ix y iy sham => semi_BN_MULQACC x ix y iy 0%R sham;
    id_nargs := 5;
    id_args_kinds := ak_xreg_imm8_xreg_imm8_imm8;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op BN_MULQACC_Z);
    id_safe := [::];
    id_pp_asm := pp_otbn_op BN_MULQACC_Z xreg_size;
  |}.

(* Reference manual:

       Quarter-word Multiply and Accumulate with full-word writeback.

       Syntax:
           BN.MULQACC.WO[<zero_acc>]
             <wrd>,
             <wrs1>.<wrs1_qwsel>,
             <wrs2>.<wrs2_qwsel>,
             <acc_shift_imm>
             [, FG<flag_group>]

       Multiplies two WLEN/4 WDR values, shifts the product by acc_shift_imm
       bits, and adds the result to the accumulator.
       Writes the resulting accumulator to wrd. *)

Definition semi_BN_MULQACC_WO :
  semi_type base_mulqacc_tin (ty_mlz ++ [:: sword256; sword256 ]) :=
  fun x ix y iy acc sham =>
    Let res := semi_BN_MULQACC x ix y iy acc sham in
    ok
      (:: MF_of_word res
        , LF_of_word res
        , ZF_of_word res
        , res
        & res
      ).

Definition desc_BN_MULQACC_WO : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_tin;
    id_in := [:: E 1; E 2; E 3; E 4; Xreg ACC; E 5 ];
    id_tout := ty_mlz ++ [:: sword256; sword256 ];
    id_out := ad_mlz ++ [:: E 0; Xreg ACC ];
    id_semi := semi_BN_MULQACC_WO;
    id_nargs := 6;
    id_args_kinds := ak_xreg_xreg_imm8_xreg_imm8_imm8;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_otbn_op (BN_MULQACC_WO fg));
    id_safe := [::];
    id_pp_asm := pp_otbn_op (BN_MULQACC_WO fg) xreg_size;
  |}.

Definition desc_BN_MULQACC_WO_Z : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := base_mulqacc_z_tin;
    id_in := [:: E 1; E 2; E 3; E 4; E 5 ];
    id_tout := ty_mlz ++ [:: sword256; sword256 ];
    id_out := ad_mlz ++ [:: E 0; Xreg ACC ];
    id_semi := fun x ix y iy sham => semi_BN_MULQACC_WO x ix y iy 0%R sham;
    id_nargs := 6;
    id_args_kinds := ak_xreg_xreg_imm8_xreg_imm8_imm8;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_otbn_op (BN_MULQACC_WO_Z fg));
    id_safe := [::];
    id_pp_asm := pp_otbn_op (BN_MULQACC_WO_Z fg) xreg_size;
  |}.

(* Reference manual:

       Quarter-word Multiply and Accumulate with half-word writeback.

       Syntax:
           BN.MULQACC.SO[<zero_acc>]
             <wrd>.<wrd_hwsel>,
             <wrs1>.<wrs1_qwsel>,
             <wrs2>.<wrs2_qwsel>,
             <acc_shift_imm>
             [, FG<flag_group>]

       Multiplies two WLEN/4 WDR values, shifts the product by acc_shift_imm
       bits and adds the result to the accumulator.
       Next, shifts the resulting accumulator right by half a word (128 bits).
       The bits that are shifted out are written to a half-word of wrd,
       selected with wrd_hwsel.

       This instruction never changes the C flag.

       If wrd_hwsel is zero (so the instruction is updating the lower
       half-word of wrd), it updates the L and Z flags and leaves M unchanged.
       The L flag is set iff the bottom bit of the shifted-out result is zero.
       The Z flag is set iff the shifted-out result is zero.

       If wrd_hwsel is one (so the instruction is updating the upper half-word
       of wrd), it updates the M and Z flags and leaves L unchanged.
       The M flag is set iff the top bit of the shifted-out result is zero.
       The Z flag is left unchanged if the shifted-out result is zero and
       cleared if not.

   Remark: The flags correspond to the value in wrd only when we write to the
   top half, due to the Z flag. *)

Let mulqacc_so_tin := ty_mlz ++ [:: sword256 ] ++ base_mulqacc_tin.
Let mulqacc_so_tout := ty_mlz ++ [:: sword256; sword256 ].

Definition wrd_hwsel : Z :=
  match wb with
  | WB_upper => 1
  | WB_lower => 0
  end.

Definition semi_BN_MULQACC_SO : semi_type mulqacc_so_tin mulqacc_so_tout :=
  fun mf lf zf r x ix y iy acc sham =>
    Let base_res := semi_BN_MULQACC x ix y iy acc sham in
    let lo_part := extract_subword base_res 0 128 in
    let hi_part := extract_subword base_res 128 128 in
    let hw_shift := 128 * wrd_hwsel in
    let hw_mask := wrepr U256 (Z.shiftl (Z.shiftl 1 128 - 1) hw_shift) in
    let new_wrd := wor (wand r (wnot hw_mask)) (wshl lo_part hw_shift) in
    let '(mf', lf', zf') :=
      if wrd_hwsel == 1
      then (wand (wshr lo_part 127) 1 != 0, lf, zf && (lo_part == 0))%R
      else (mf, wand lo_part 1 != 0, lo_part == 0)%R
    in
    ok (:: Some mf', Some lf', Some zf', new_wrd & hi_part ).

Definition desc_BN_MULQACC_SO : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := mulqacc_so_tin;
    id_in := ad_mlz ++ [:: E 0; E 1; E 2; E 3; E 4; Xreg ACC; E 5 ];
    id_tout := mulqacc_so_tout;
    id_out := ad_mlz ++ [:: E 0; Xreg ACC ];
    id_semi := semi_BN_MULQACC_SO;
    id_nargs := 6;
    id_args_kinds := ak_xreg_xreg_imm8_xreg_imm8_imm8;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_otbn_op (BN_MULQACC_SO fg wb));
    id_safe := [::];
    id_pp_asm := pp_otbn_op (BN_MULQACC_SO fg wb) xreg_size;
  |}.

Definition desc_BN_MULQACC_SO_Z : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := ty_mlz ++ [:: sword256 ] ++ base_mulqacc_z_tin;
    id_in := ad_mlz ++ [:: E 0; E 1; E 2; E 3; E 4; E 5 ];
    id_tout := mulqacc_so_tout;
    id_out := ad_mlz ++ [:: E 0; Xreg ACC ];
    id_semi :=
      fun mf lf zf r x ix y ix sham =>
        semi_BN_MULQACC_SO mf lf zf r x ix y ix 0%R sham;
    id_nargs := 6;
    id_args_kinds := ak_xreg_xreg_imm8_xreg_imm8_imm8;
    id_eq_size := ltac:(by t_case_ad_cmlz);
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by t_case_ad_cmlz);
    id_str_jas := pp_s (string_of_otbn_op (BN_MULQACC_SO_Z fg wb));
    id_safe := [::];
    id_pp_asm := pp_otbn_op (BN_MULQACC_SO_Z fg wb) xreg_size;
  |}.

End MULQACC.

(*
Definition desc_FGRS (fg : bn_flag_group) : instr_desc_t := TODO_OTBN "FGRS".
Definition desc_FGRW (fg : bn_flag_group) : instr_desc_t := TODO_OTBN "FGRW".
*)

Definition desc_BN_WSR op ad_in ad_out : instr_desc_t :=
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sxreg ];
    id_in := [:: ad_in ];
    id_tout := [:: sxreg ];
    id_out := [:: ad_out ];
    id_semi := fun x => ok x;
    id_nargs := 1;
    id_args_kinds := ak_xreg;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := ltac:(by case ad_out);
    id_str_jas := pp_s (string_of_otbn_op op);
    id_safe := [::];
    id_pp_asm := pp_otbn_op op xreg_size;
  |}.

Definition desc_BN_indirect op is_str : instr_desc_t :=
  let arg_pos := (if is_str then 0 else 2)%nat in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [:: sreg; sxreg ];
    id_in := [:: E 1; E arg_pos ];
    id_tout := [:: sxreg ];
    id_out := [:: E (2 - arg_pos) ];
    id_semi := fun _ x => ok x;
    id_nargs := 3;
    id_args_kinds := ak_xreg_reg_mem;
    id_eq_size := refl_equal;
    id_tin_narr := refl_equal;
    id_tout_narr := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_otbn_op op);
    id_safe := [::];
    id_pp_asm := pp_otbn_op op xreg_size;
  |}.

Definition desc_otbn_op (op : otbn_op) : instr_desc_t :=
  match op with
  | RV32 mn => desc_rv_mnemonic mn
  | BN_basic mn fg => desc_bn_basic_mnemonic mn fg
  | BN_basic_shift mn fg sh => desc_bn_basic_shift_mnemonic mn fg sh
  | BN_ADDI fg => desc_bn_binopI op fg wadd Z.add
  | BN_SUBI fg => desc_bn_binopI op fg wsub Z.sub
  | BN_MOV => desc_BN_MOV
  | BN_RSHI => desc_BN_RSHI
  | BN_SEL fg => desc_BN_SEL fg
  | BN_ADDM => desc_BN_ADDM
  | BN_SUBM => desc_BN_SUBM
  | BN_MULQACC => desc_BN_MULQACC
  | BN_MULQACC_Z => desc_BN_MULQACC_Z
  | BN_MULQACC_WO fg => desc_BN_MULQACC_WO fg
  | BN_MULQACC_WO_Z fg => desc_BN_MULQACC_WO_Z fg
  | BN_MULQACC_SO fg wb => desc_BN_MULQACC_SO fg wb
  | BN_MULQACC_SO_Z fg wb => desc_BN_MULQACC_SO_Z fg wb
  (* | FGRS fg => desc_FGRS fg
  | FGRW fg => desc_FGRW fg *)
  | BN_ACCR => desc_BN_WSR op (Xreg ACC) (E 0)
  | BN_ACCW => desc_BN_WSR op (E 0) (Xreg ACC)
  | BN_MODR => desc_BN_WSR op (Xreg MOD) (E 0)
  | BN_MODW => desc_BN_WSR op (E 0) (Xreg MOD)
  | BN_RNDR => desc_BN_WSR op (Xreg RND) (E 0)
  | BN_RNDW => desc_BN_WSR op (E 0) (Xreg RND)
  | BN_KEY_S0_L_R => desc_BN_WSR op (Xreg KEY_S0_L) (E 0)
  | BN_KEY_S0_L_W => desc_BN_WSR op (E 0) (Xreg KEY_S0_L)
  | BN_KEY_S0_H_R => desc_BN_WSR op (Xreg KEY_S0_H) (E 0)
  | BN_KEY_S0_H_W => desc_BN_WSR op (E 0) (Xreg KEY_S0_H)
  | BN_KEY_S1_L_R => desc_BN_WSR op (Xreg KEY_S1_L) (E 0)
  | BN_KEY_S1_L_W => desc_BN_WSR op (E 0) (Xreg KEY_S1_L)
  | BN_KEY_S1_H_R => desc_BN_WSR op (Xreg KEY_S1_H) (E 0)
  | BN_KEY_S1_H_W => desc_BN_WSR op (E 0) (Xreg KEY_S1_H)
  | BN_LID => desc_BN_indirect BN_LID false
  | BN_SID => desc_BN_indirect BN_SID true
  end.


Section PRIM_STRING.

  Let map_prim_string
    {A : Type}
    (to_string : A -> string)
    (to_prim : (A -> prim_constructor otbn_op))
    (s : seq A)
    : seq (string * prim_constructor otbn_op) :=
    map (fun a => (to_string a, to_prim a)) s.

  (* [LA] computes an address relative to the PC. *)
  Let rv_prim_string :=
    map_prim_string
      string_of_rv_mnemonic
      (fun mn => PrimOTBN_none (RV32 mn))
      (filter (fun mn => mn != LA) cenum).

  Let bn_basic_prim_string :=
    map_prim_string
      string_of_bn_basic_mnemonic
      (fun mn => PrimOTBN_fg (fun fg => BN_basic mn fg))
      cenum.

  (* Intrinsic string does not change with flag group. *)
  Let bn_flag_group_prim_string :=
    map_prim_string
      (fun mn => string_of_otbn_op (mn FG0))
      (fun mn => PrimOTBN_fg mn)
      [:: BN_ADDI; BN_SUBI; BN_SEL ].

  Let bn_no_opt_prim_string :=
    map_prim_string
      string_of_otbn_op
      (PrimOTBN_none (asm_op := otbn_op))
      [:: BN_MOV; BN_RSHI; BN_ADDM; BN_SUBM; BN_ACCR; BN_ACCW; BN_MODR
        ; BN_MODW; BN_RNDR; BN_RNDW
        ; BN_KEY_S0_L_R; BN_KEY_S0_L_W; BN_KEY_S0_H_R; BN_KEY_S0_H_W
        ; BN_KEY_S1_L_R; BN_KEY_S1_L_W; BN_KEY_S1_H_R; BN_KEY_S1_H_W
      ].

  (* Intrinsic string does not change with flag group or writeback. *)
  Let bn_mulqacc_prim_string :=
      let fg := FG0 in
      let wb := WB_upper in
      let str := string_of_otbn_op BN_MULQACC in
      let str_z := string_of_otbn_op BN_MULQACC_Z in
      let str_wo := string_of_otbn_op (BN_MULQACC_WO fg) in
      let str_wo_z := string_of_otbn_op (BN_MULQACC_WO_Z fg) in
      let str_so := string_of_otbn_op (BN_MULQACC_SO fg wb) in
      let str_so_z := string_of_otbn_op (BN_MULQACC_SO_Z fg wb) in
      [:: (str, PrimOTBN_none BN_MULQACC)
        ; (str_z, PrimOTBN_none BN_MULQACC_Z)
        ; (str_wo, PrimOTBN_fg BN_MULQACC_WO)
        ; (str_wo_z, PrimOTBN_fg BN_MULQACC_WO_Z)
        ; (str_so, PrimOTBN_mulqacc_so BN_MULQACC_SO)
        ; (str_so_z, PrimOTBN_mulqacc_so BN_MULQACC_SO_Z)
      ].

  Definition otbn_prim_string : seq (string * prim_constructor otbn_op) :=
    Eval vm_compute in
    map
      (fun '(s, p) => (replace_dot s, p))
      (rv_prim_string
       ++ bn_basic_prim_string
       ++ bn_flag_group_prim_string
       ++ bn_no_opt_prim_string
       ++ bn_mulqacc_prim_string).

End PRIM_STRING.

#[export]
Instance otbn_op_decl : asm_op_decl otbn_op :=
  {|
    instr_desc_op := desc_otbn_op;
    prim_string := otbn_prim_string;
  |}.

Definition otbn_prog := asm_prog (asm_op_d := otbn_op_decl).

Section VALIDATION.
  Import strings.

  Let strings := map fst otbn_prim_string.

  Goal uniq strings. done. Qed.

  Let hidden := [:: "LA"; "BN_LID"; "BN_SID" ]%string.

  Goal
    forall op,
      let: s := replace_dot (string_of_otbn_op op) in
      xorb (s \in hidden) (s \in strings).
  by move=> [] // [] //. Qed.

  Definition aux (seen : seq nat) (x : arg_desc) : seq nat :=
    if x is ADExplicit _ n _
    then if n \notin seen then n :: seen else seen
    else seen.

  Fixpoint count_explicit_arguments_aux
    (seen : seq nat) (xs : seq arg_desc) : nat :=
    match xs with
    | [::] => size seen
    | x :: xs =>
        let seen' := aux seen x in
        count_explicit_arguments_aux seen' xs
    end.

  Definition count_explicit_arguments := count_explicit_arguments_aux [::].

  Goal
    forall op,
      let t := instr_desc_op op in
      all
        (fun x => size x == count_explicit_arguments (id_in t ++ id_out t))
        (id_args_kinds t).
  by move=> [] // [] // []. Qed.

  Goal
    forall op,
      let t := instr_desc_op op in
      id_nargs t = count_explicit_arguments (id_in t ++ id_out t).
  by move=> [] // [] // []. Qed.

End VALIDATION.

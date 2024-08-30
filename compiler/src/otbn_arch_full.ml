open Arch_decl
open Prog
open Otbn_decl_core
open Otbn_decl


module type OTBN_input = sig
  val call_conv :
    (register, Otbn_decl.__, wide_register, flag, condition) calling_convention
end

module OTBN_core = struct
  type reg = register
  type regx = Otbn_decl.__
  type xreg = wide_register
  type rflag = flag
  type cond = condition
  type asm_op = Otbn_instr_decl.otbn_op
  type extra_op = Otbn_extra.extra_op
  type fresh_vars = Otbn_lowering.fresh_vars
  type lowering_options = Otbn_lowering.lowering_options

  let atoI = X86_arch_full.atoI otbn_decl

  let asm_e = Otbn_extra.otbn_extra atoI
  let aparams = Otbn_params.otbn_params atoI

  let known_implicits = ["CF", "_cf_"; "MF", "_mf_"; "LF", "_lf_"; "ZF", "_zf_"]

  let reg_unallocatable = [ X00; X01 ]
  let xreg_unallocatable = [ ACC; MOD; RND ]
end

module OTBN (Input : OTBN_input) : Arch_full.Core_arch = struct
  include OTBN_core
  include Input

  let lowering_opt = ()

  let not_saved_stack = (Otbn_params.liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_otbn.print_prog

  (* TODO_OTBN: Fix this. *)
  let callstyle = Arch_full.ByReg (Some X01)
end

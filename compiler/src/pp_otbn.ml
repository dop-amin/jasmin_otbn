open Arch_decl
open Prog
open Utils
open Otbn_decl_core
open Otbn_decl

(* -------------------------------------------------------------------------- *)
(* Errors. *)

module E = struct
  let loc = Lnone
  let kind = "pretty printing"
  let internal = true
  let err s = fun () -> hierror ~loc ~kind ~internal s

  let invalid_address = err "invalid address"
  let invalid_jmpi = err "invalid JMPI"
  let invalid_jcc = err "invalid Jcc"
  let invalid_call = err "invalid CALL"
  let invalid_jal = err "invalid JAL"
  let invalid_args = err "invalid arguments"
  let invalid_cond_asm_arg = err "invalid condition argument"
  let pp_error = err "found PP_error"
  let invalid_pp_aop_ext = err "invalid pp_aop_ext"

  let not_implemented = hierror ~loc ~kind ~internal "not implemented: %s"

  let address_not_supported base disp off scal =
    let pp =
      Format.pp_print_option
        ~none:(fun fmt () -> Format.fprintf fmt "0")
        (fun fmt -> Format.fprintf fmt "%s")
    in
    hierror
      ~loc
      ~kind
      ~internal:false
      "address not supported in OTBN: [%s + %a * %a + %a]"
      base
      pp off
      pp scal
      pp disp
end

(* -------------------------------------------------------------------------- *)

let arch = otbn_decl
let imm_pre = ""
let global_data_label = "glob_data"
let headers = [".section .text.start"] (* put directives *)
let data_directives = [".data"; ".balign 32"]
let iwidth = 15

let pp_reg_address_aux base disp off scal =
  match (disp, off, scal) with
  | None, None, None -> Format.sprintf "0(%s)" base
  | Some disp, None, None -> Format.sprintf "%s(%s)" disp base
  | _, _, _ -> E.address_not_supported base disp off scal

let pp_rip_address p =
  Format.asprintf "%s+%a" global_data_label Z.pp_print (Conv.z_of_int32 p)

(* -------------------------------------------------------------------------- *)
(* TODO_OTBN: This is generic. *)

type asm_line =
  | LLabel of string
  | LInstr of string * string list
  | LByte of string

let print_asm_line fmt ln =
  match ln with
  | LLabel lbl -> Format.fprintf fmt "%s:" lbl
  | LInstr (s, []) -> Format.fprintf fmt "\t%-*s" iwidth s
  | LInstr (s, args) ->
      Format.fprintf fmt "\t%-*s\t%s" iwidth s (String.concat ", " args)
  | LByte n -> Format.fprintf fmt "\t.byte\t%s" n

let print_asm_lines fmt = List.iter (Format.fprintf fmt "%a\n%!" print_asm_line)

(* -------------------------------------------------------------------------- *)
(* TODO_OTBN: This is generic. *)

let string_of_label name p = Format.sprintf "L%s$%d" name (Conv.int_of_pos p)
let pp_label = string_of_label
let pp_remote_label (fn, lbl) = string_of_label fn.fn_name lbl

let hash_to_string_core (to_string : 'a -> string) =
  let tbl = Hashtbl.create 17 in
  fun r ->
    try Hashtbl.find tbl r
    with Not_found ->
      let s = to_string r in
      Hashtbl.add tbl r s;
      s

let hash_to_string to_string =
  hash_to_string_core (fun x -> Conv.string_of_cstring (to_string x))

let pp_register = hash_to_string arch.toS_r.to_string
let pp_register_ext = hash_to_string arch.toS_rx.to_string
let pp_xregister = hash_to_string arch.toS_x.to_string
let pp_imm imm = Format.sprintf "%s%s" imm_pre (Z.to_string imm)
let pp_flag f =
  match f with
  | CF0 -> "FG0.C"
  | MF0 -> "FG0.M"
  | LF0 -> "FG0.L"
  | ZF0 -> "FG0.Z"
  | CF1 -> "FG1.C"
  | MF1 -> "FG1.M"
  | LF1 -> "FG1.L"
  | ZF1 -> "FG1.Z"

let pp_reg_address addr =
  match addr.ad_base with
  | None -> E.invalid_address ()
  | Some r ->
      let base = pp_register r in
      let disp = Conv.z_of_word (arch_pd arch) addr.ad_disp in
      let disp =
        if Z.equal disp Z.zero then None else Some (Z.to_string disp)
      in
      let off = Option.map pp_register addr.ad_offset in
      let scal = Conv.z_of_nat addr.ad_scale in
      let scal =
        if Z.equal scal Z.zero then None else Some (Z.to_string scal)
      in
      pp_reg_address_aux base disp off scal

let pp_address addr =
  match addr with
  | Areg ra -> pp_reg_address ra
  | Arip r -> pp_rip_address r

let pp_asm_arg arg =
  match arg with
  | Condt ct ->
      begin match ct with
      | BNcond f -> pp_flag f
      | RVcond _ -> E.invalid_cond_asm_arg ()
      end
  | Imm (ws, w) -> pp_imm (Conv.z_unsigned_of_word ws w)
  | Reg r -> pp_register r
  | Regx r -> pp_register_ext r
  | Addr addr -> pp_address addr
  | XReg r -> pp_xregister r

let mangle x = Format.sprintf "_%s" x

let pp_syscall o =
  match o with
  | Syscall_t.RandomBytes _ -> "__jasmin_syscall_randombytes__"

(* -------------------------------------------------------------------------- *)

let pp_is_eq is_eq = if is_eq then "eq" else "ne"

let pp_mnemonic_ext ext =
  match ext with
  | PP_error -> E.pp_error ()
  | PP_name -> ""
  | _ -> E.invalid_pp_aop_ext ()

(* TODO_OTBN: Remove. *)
let indirect_args pp =
  match Conv.string_of_cstring pp.pp_aop_name with
  | "BN.LID" | "BN.SID" -> List.tl pp.pp_aop_args
  | _ -> pp.pp_aop_args

(* TODO_OTBN: Is this generic? *)
let pp_otbn_op pp =
  let pp_args = indirect_args pp in
  let name =
    Format.sprintf
      "%s%s"
      (Conv.string_of_cstring pp.pp_aop_name |> String.lowercase)
      (pp_mnemonic_ext pp.pp_aop_ext)
  in
  let args = List.map (fun (_, a) -> pp_asm_arg a) pp_args in
  name, args

let addr_rsp =
  let k0 =
    Ssralg.GRing.zero (Ssralg.GRing.ComRing.zmodType (Word0.word Wsize.U32))
  in
  { ad_base = Some X02; ad_disp = k0; ad_scale = O; ad_offset = None }

let symbol_of_shift sh =
  match sh with
  | Otbn_options.RS_left -> "<<"
  | RS_right -> ">>"

(* TODO_OTBN: This is ugly. *)
(* Return the list of arguments updated with shift notations.
   We need to combine register shifts with the second operand and the shift
   operator. *)
let pp_args_shift op args =
  let pp_shift sh =
    match List.rev args with
    | sham :: r :: rest ->
        let r' = Format.sprintf "%s %s %s" r (symbol_of_shift sh) sham in
        List.rev (r' :: rest)
    | _ -> E.invalid_args ()
  in
  match op with
  | Otbn_instr_decl.BN_basic_shift (_, _, sh) -> pp_shift sh
  | BN_RSHI -> pp_shift Otbn_options.RS_right
  | _ -> args

let string_of_bn_flag_group fg =
  match fg with
  | Otbn_options.FG0 -> "FG0"
  | FG1 -> "FG1"

(* We need to print the flag group as another argument, but only if it's FG1. *)
let pp_args_flag_group op args =
  let sfg =
    match op with
    | Otbn_instr_decl.BN_basic (_, fg)
    | BN_basic_shift (_, fg, _)
    | BN_ADDI fg
    | BN_SUBI fg
    | BN_MULQACC_WO fg
    | BN_MULQACC_WO_Z fg
    | BN_MULQACC_SO (fg, _)
    | BN_MULQACC_SO_Z (fg, _)
      -> [ string_of_bn_flag_group fg ]
    | _ -> []
  in
  args @ sfg

let pp_args_mulqacc_selectors op args =
  let pp_qwsel = Format.sprintf "%s.%s" in
  let pp_hwsel wr hwsel =
    let s =
      match hwsel with
      | Otbn_options.WB_upper -> "U"
      | WB_lower -> "L"
    in
    Format.sprintf "%s.%s" wr s
  in
  match op with
  | Otbn_instr_decl.BN_MULQACC | BN_MULQACC_Z ->
      begin match args with
      | wrs1 :: qwsel1 :: wrs2 :: qwsel2 :: rest ->
          pp_qwsel wrs1 qwsel1 :: pp_qwsel wrs2 qwsel2 :: rest
      | _ -> E.invalid_args ()
      end
  | BN_MULQACC_WO _ | BN_MULQACC_WO_Z _ ->
      begin match args with
      | wrd :: wrs1 :: qwsel1 :: wrs2 :: qwsel2 :: rest ->
          wrd :: pp_qwsel wrs1 qwsel1 :: pp_qwsel wrs2 qwsel2 :: rest
      | _ -> E.invalid_args ()
      end
  | BN_MULQACC_SO (_, hwsel) | BN_MULQACC_SO_Z (_, hwsel) ->
      begin match args with
      | wrd :: wrs1 :: qwsel1 :: wrs2 :: qwsel2 :: rest ->
          pp_hwsel wrd hwsel
          :: pp_qwsel wrs1 qwsel1
          :: pp_qwsel wrs2 qwsel2
          :: rest
      | _ -> E.invalid_args ()
      end
  | _ -> args

let pp_args op args =
  pp_args_shift op args
  |> pp_args_flag_group op
  |> pp_args_mulqacc_selectors op

let pp_instr fn i =
  let x0 = pp_register X00 in
  let ra = pp_register X01 in
  let sp = pp_register X02 in
  let ret r =
    if r == ra
    then LInstr ("ret", []) (* This is syntactic sugar for [JALR x0; ra; 0 ]. *)
    else LInstr ("jalr", [ x0; r; pp_imm Z.zero ])
  in
  match i with
  | ALIGN -> E.not_implemented "pp_instr ALIGN"

  | LABEL (_, lbl) -> [ LLabel (pp_label fn lbl) ]

  | STORELABEL (dst, lbl) ->
      [ LInstr ("la", [ pp_register dst; string_of_label fn lbl ]) ]

  | JMP lbl -> [ LInstr ("beq", [ x0; x0; pp_remote_label lbl ]) ]

  | JMPI arg ->
      let rlbl =
        match arg with
        | Reg r -> r
        | _ -> E.invalid_jmpi ()
      in
      [ ret (pp_register rlbl) ]

  | Jcc (lbl, ct) ->
      begin match ct with
      | RVcond(is_eq, r0, r1) ->
          let iname = Format.sprintf "b%s" (pp_is_eq is_eq) in
          let args = [ pp_register r0; pp_register r1; pp_label fn lbl ] in
          [ LInstr (iname, args) ]
      | BNcond _ -> E.invalid_jcc ()
      end

  | JAL (X01, lbl) -> [ LInstr ("jal", [ ra; pp_remote_label lbl ]) ]

  | CALL _ -> E.invalid_call ()

  | JAL _ -> E.invalid_jal ()

  | REPEATCALL(count, fn) ->
    let scount, name =
      match count with
      | Datatypes.Coq_inl v -> (pp_register v, "loop")
      | Datatypes.Coq_inr cz -> (Z.to_string (Conv.z_of_cz cz), "loopi")
    in
    let lbl = (fn, Conv.pos_of_int 1) in
    [
      LInstr(name, [scount; "2"]);
      LInstr("  jal", [ra; pp_remote_label lbl]);
      LInstr("  nop", []);
    ]

  | POPPC ->
      [ LInstr ("lw", [ ra; pp_address (Areg addr_rsp) ])
      ; LInstr ("addi", [ sp; sp; pp_imm (Z.of_int 4) ])
      ; ret ra
      ]

  | SysCall op -> [ LInstr ("jal", [ ra; pp_syscall op ]) ]

  | AsmOp (op, args) ->
      let id = instr_desc otbn_decl Otbn_instr_decl.otbn_op_decl (None, op) in
      let pp = id.id_pp_asm args in
      let name, args = pp_otbn_op pp in
      let args = pp_args op args in
      [ LInstr (name, args) ]

let pp_fun_pre fn fd =
  if fd.asm_fd_export then
    let ra = pp_register X01 in
    let sp = pp_register X02 in
    [ LLabel (mangle fn)
    ; LLabel fn
    ; LInstr ("sw", [ ra; pp_address (Areg addr_rsp) ])
    ; LInstr ("addi", [ sp; sp; pp_imm (Z.of_int (-4)) ])
    ]
  else []

let pp_fun_pos fn fd = if fd.asm_fd_export then pp_instr fn POPPC else []

(* -------------------------------------------------------------------------- *)
(* TODO_OTBN: This is generic. *)

let pp_body fn cmd = List.concat_map (pp_instr fn) cmd

let pp_fun (fn, fd) =
  let fn = fn.fn_name in
  let head =
    if fd.asm_fd_export then
      [ LInstr (".global", [ mangle fn ]); LInstr (".global", [ fn ]) ]
    else []
  in
  let pre = pp_fun_pre fn fd in
  let body = pp_body fn fd.asm_fd_body in
  let pos = pp_fun_pos fn fd in
  head @ pre @ body @ pos

let pp_funcs funs = List.concat_map pp_fun funs

let pp_data globs =
  if not (List.is_empty globs) then
    let mk b = LByte (Z.to_string (Conv.z_of_int8 b)) in
    LLabel global_data_label :: List.map mk globs
  else []

let pp_prog p =
  let headers = List.map (fun s -> LInstr (s, [])) headers in
  let data_directives = List.map (fun s -> LInstr (s, [])) data_directives in
  let code = pp_funcs p.asm_funcs in
  let data = pp_data p.asm_globs in
  headers @ code @ data_directives @ data

let print_instr s fmt i = print_asm_lines fmt (pp_instr s i)
let print_prog fmt p = print_asm_lines fmt (pp_prog p)

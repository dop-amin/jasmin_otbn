open Otbn_options

open Utils

module L = Location
module S = Syntax

(* -------------------------------------------------------------------- *)
(* OTBN parsing. *)

let get_flag_group s =
  if String.ends_with s "_FG0"
  then (Some FG0, String.drop_end 4 s)
  else
    if String.ends_with s "_FG1"
    then (Some FG1, String.drop_end 4 s)
    else (None, s)

let get_hw_writeback s =
  if String.ends_with s "_L"
  then (Some WB_lower, String.drop_end 2 s)
  else
    if String.ends_with s "_U"
    then (Some WB_upper, String.drop_end 2 s)
    else (None, s)

let get_otbn_opts s =
  let fg, s = get_flag_group s in
  let wb, s = get_hw_writeback s in
  (s, fg, wb)

let tt_prim ~unknown ps s sa =
  if Option.is_some sa then raise unknown;
  let name, ofg, owb = get_otbn_opts s in
  let fg = Option.default FG0 ofg in
  match List.assoc name ps with
  | Sopn.PrimOTBN_none op -> op
  | PrimOTBN_fg pr -> pr fg
  | PrimOTBN_mulqacc_so pr ->
      begin match owb with
      | Some wb -> pr fg wb
      | None -> raise unknown
      end
  | _ | exception Not_found -> raise unknown
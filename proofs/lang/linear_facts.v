From Coq Require Import Relations.
From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  label
  linear
  linear_sem
  one_varmap
  psem
  sem_one_varmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

#[local] Existing Instance withsubword.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
.

Lemma setpc_id ls :
  setpc ls (lpc ls) = ls.
Proof. by case: ls. Qed.

Lemma setpc_lset_estate ls pc scs m vm :
  lset_estate (setpc ls pc) scs m vm
  = setpc (lset_estate ls scs m vm) pc.
Proof. done. Qed.

Lemma lnext_pc_setpc ls n :
  lnext_pc (setpc ls n) = setpc ls n.+1.
Proof. done. Qed.

Lemma setcpc_setpc ls fn n n' :
  setcpc (setpc ls n') fn n = setcpc ls fn n.
Proof. done. Qed.

Lemma lfn_lset_estate ls scs m vm :
  lfn (lset_estate ls scs m vm) = lfn ls.
Proof. done. Qed.

Lemma lsem_transn lp l : transn_refl_spec (R := lsem lp) l.
Proof. exact: (transn_refl_specP (rt_trans _ _) (rt_refl _ _)). Qed.

Lemma lsem_trans3 lp ls0 ls1 ls2 ls3 :
  lsem lp ls0 ls1 ->
  lsem lp ls1 ls2 ->
  lsem lp ls2 ls3 ->
  lsem lp ls0 ls3.
Proof. exact: (lsem_transn _ [:: _; _; _; _ ]). Qed.

Lemma lsem_trans4 lp ls0 ls1 ls2 ls3 ls4 :
  lsem lp ls0 ls1 ->
  lsem lp ls1 ls2 ->
  lsem lp ls2 ls3 ->
  lsem lp ls3 ls4 ->
  lsem lp ls0 ls4.
Proof. exact: (lsem_transn _ [:: _; _; _; _; _ ]). Qed.

Lemma lsem_trans5 lp ls0 ls1 ls2 ls3 ls4 ls5 :
  lsem lp ls0 ls1 ->
  lsem lp ls1 ls2 ->
  lsem lp ls2 ls3 ->
  lsem lp ls3 ls4 ->
  lsem lp ls4 ls5 ->
  lsem lp ls0 ls5.
Proof. exact: (lsem_transn _ [:: _; _; _; _; _; _ ]). Qed.

Lemma find_labelE lbl c :
  find_label lbl c =
  if c is i :: c'
  then
    if is_label lbl i
    then ok O
    else Let r := find_label lbl c' in ok r.+1
  else type_error.
Proof.
  case: c => // i c; rewrite /find_label /=.
  case: (is_label lbl i) => //.
  rewrite ltnS.
  by case: ifP.
Qed.

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2)
  = Let pc := find_label lbl c2 in ok (size c1 + pc).
Proof.
  rewrite /find_label find_cat size_cat => /negbTE ->.
  by rewrite ltn_add2l;case:ifP.
Qed.

Definition is_linear_of (lp : lprog) (fn : funname) (lc : lcmd) : Prop :=
  exists2 fd,
    get_fundef (lp_funcs lp) fn = Some fd
    & lfd_body fd = lc.

Lemma find_instrE lp ls body :
  is_linear_of lp (lfn ls) body ->
  find_instr lp ls = oseq.onth body (lpc ls).
Proof. by rewrite /find_instr => - [] fd /= -> ->. Qed.

Lemma find_instr_skip' lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls n,
    lpc ls = size pre + n ->
    lfn ls = fn ->
    find_instr lp ls = oseq.onth pos n.
Proof.
  move=> h ls n hpc hfn.
  rewrite -hfn in h.
  rewrite (find_instrE h) !oseq.onth_nth map_cat nth_cat size_map.
  by rewrite hpc lt_nm_n sub_nmn.
Qed.

Lemma find_instr_skip lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls n,
    lfn ls = fn ->
    find_instr lp (setpc ls (size pre + n)) = oseq.onth pos n.
Proof. by eauto using find_instr_skip'. Qed.

Lemma find_instr_skip0 lp fn pre pos :
  is_linear_of lp fn (pre ++ pos) ->
  forall ls,
    lpc ls = size pre ->
    lfn ls = fn ->
    find_instr lp ls = oseq.onth pos 0.
Proof. rewrite -(addn0 (size pre)). by eauto using find_instr_skip'. Qed.

Lemma eval_lsem1 lp ls ls' pre pos li fn :
  is_linear_of lp fn (pre ++ li :: pos) ->
  lpc ls = size pre ->
  lfn ls = fn ->
  eval_instr lp li ls = ok ls' ->
  lsem1 lp ls ls'.
Proof.
  rewrite /lsem1 /step.
  by move=> /find_instr_skip0 /[apply] /[apply] ->.
Qed.

Lemma eval_lsem_step1 lp ls ls' pre pos li fn :
  is_linear_of lp fn (pre ++ li :: pos) ->
  lpc ls = size pre ->
  lfn ls = fn ->
  eval_instr lp li ls = ok ls' ->
  lsem lp ls ls'.
Proof. by eauto using lsem_step1, eval_lsem1. Qed.

Lemma eval_jumpE lp fn body :
  is_linear_of lp fn body ->
  forall lbl s,
    eval_jump lp (fn, lbl) s
    = Let pc := find_label lbl body in ok (setcpc s fn pc.+1).
Proof. by case => ? /= -> ->. Qed.

Lemma eval_jumpP lp fn lfd lbl lbl' :
  get_fundef (lp_funcs lp) fn = Some lfd ->
  find_label lbl (lfd_body lfd) = ok lbl' ->
  eval_jump lp (fn, lbl) = fun ls => ok (setcpc ls fn lbl'.+1).
Proof. by rewrite /eval_jump => -> /= ->. Qed.

End WITH_PARAMS.

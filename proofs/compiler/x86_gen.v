Require Import x86_sem linear_sem.
Import Utf8 Relation_Operators.
Import all_ssreflect all_algebra.
Require Import compiler_util expr psem x86_sem linear x86_variables x86_variables_proofs asmgen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition assemble_i rip (i: linstr) : ciexec asm :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lopn ds op es => 
    Let oa := assemble_sopn rip ii op ds es in
    ok (AsmOp oa.1 oa.2)

  | Lalign  => ciok ALIGN

  | Llabel lbl =>  ciok (LABEL lbl)

  | Lgoto lbl => ciok (JMP lbl)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ciok (Jcc l cond)
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_c rip (lc: lcmd) : ciexec (seq asm) :=
  mapM (assemble_i rip) lc.

(* -------------------------------------------------------------------- *)
Variant x86_gen_error_t :=
| X86Error_InvalidStackPointer
| X86Error_StackPointerInArguments of register
.

Definition x86_gen_error (e: x86_gen_error_t) : instr_error :=
  (xH, Cerr_assembler (AsmErr_string
  match e with
  | X86Error_InvalidStackPointer => "Invalid stack pointer"
  | X86Error_StackPointerInArguments sp =>
    "Stack pointer (" ++ string_of_register sp ++ ") is also an argument"
  end)).

(* -------------------------------------------------------------------- *)

Definition assemble_saved_stack (x:stack_alloc.saved_stack) := 
  match x with
  | stack_alloc.SavedStackNone  => ok (x86_sem.SavedStackNone)
  | stack_alloc.SavedStackReg r => Let r := reg_of_var xH r in ok (x86_sem.SavedStackReg r)
  | stack_alloc.SavedStackStk z => ok (x86_sem.SavedStackStk z)
  end.

Definition assemble_fd rip (fd: lfundef) :=
  Let fd' := assemble_c rip (lfd_body fd) in

  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
      Let arg := reg_of_vars xH (lfd_arg fd) in
      Let res := reg_of_vars xH (lfd_res fd) in
      Let _ :=
        assert (~~ (sp \in arg)) (x86_gen_error (X86Error_StackPointerInArguments sp)) in
      Let tosave := reg_of_vars xH (map (fun x => VarI x xH) (lfd_extra fd).1) in
      Let saved  := assemble_saved_stack (lfd_extra fd).2 in
      ciok (XFundef (lfd_stk_size fd) sp arg fd' res (tosave, saved))

  | None => Error (x86_gen_error X86Error_InvalidStackPointer)
  end.

(* -------------------------------------------------------------------- *)

Definition mk_rip name := {| vtype := sword Uptr; vname := name |}.

Definition assemble_prog (p: lprog) : cfexec xprog :=
  let rip := mk_rip p.(lp_rip) in
  Let _ := assert (register_of_var rip == None)
                    (Ferr_msg (Cerr_assembler ( AsmErr_string "Invalid RIP: please report"))) in                       
  Let fds := map_cfprog (assemble_fd rip) p.(lp_funcs) in
  ok {| xp_globs := p.(lp_globs);
        xp_funcs := fds |}.

(* -------------------------------------------------------------------- *)
Variant match_state rip (ls: lstate) (xs: x86_state) : Prop :=
| MS
  `(lom_eqv rip (to_estate ls) (xm xs))
  `(assemble_c rip (lc ls) = ok (xc xs))
  `(lpc ls = xip xs)
.

Lemma assemble_i_is_label rip a b lbl :
  assemble_i rip a = ok b →
  linear.is_label lbl a = x86_sem.is_label lbl b.
Proof.
by (rewrite /assemble_i /linear.is_label ; case a =>  ii []; t_xrbindP) => /=
  [????? <- | [<-] | ? [<-] | ? [<-] | ???? [<-]].
Qed.

Lemma assemble_c_find_is_label rip c i lbl:
  assemble_c rip c = ok i →
  find (linear.is_label lbl) c = find (x86_sem.is_label lbl) i.
Proof.
rewrite /assemble_c.
elim: c i.
- by move => i [<-].
move => a c ih i' /=; t_xrbindP => b ok_b i ok_i <- {i'} /=.
by rewrite (ih i ok_i) (assemble_i_is_label lbl ok_b).
Qed.

Lemma assemble_c_find_label rip c i lbl:
  assemble_c rip c = ok i →
  linear.find_label lbl c = x86_sem.find_label lbl i.
Proof.
rewrite /assemble_c /linear.find_label /x86_sem.find_label => ok_i.
by rewrite (mapM_size ok_i) (assemble_c_find_is_label lbl ok_i).
Qed.

Lemma assemble_iP rip i j ls ls' xs :
  match_state rip ls xs →
  assemble_i rip i = ok j →
  linear_sem.eval_instr i ls = ok ls' →
  ∃ xs' : x86_state,
    x86_sem.eval_instr j xs = ok xs' ∧
    match_state rip ls' xs'.
Proof.
rewrite /linear_sem.eval_instr /x86_sem.eval_instr; case => eqm eqc eqpc.
case: i => ii [] /=.
- move => lvs op pes; t_xrbindP => -[op' asm_args] hass <- m hsem <-.
  have [s [-> eqm' /=]]:= assemble_sopnP hsem hass eqm.
  (eexists; split; first by reflexivity).
  by constructor => //=; rewrite ?to_estate_of_estate ?eqpc.
- move => [<-] [<-];eexists;split;first by reflexivity.
  by constructor => //; rewrite /setpc eqpc.
- move => lbl [<-] [<-]; eexists; split; first by reflexivity.
  constructor => //.
  by rewrite /setpc /= eqpc.
- move => lbl [<-]; t_xrbindP => pc ok_pc <- {ls'}.
  rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
  by eexists; split; eauto; constructor.
- t_xrbindP => cnd lbl cndt ok_c [<-] b v ok_v ok_b.
  case: eqm => eqm hrip hd eqr eqx eqf.
  have [v' [ok_v' hvv']] := eval_assemble_cond eqf ok_c ok_v.
  case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
  rewrite /eval_Jcc.
  case: b ok_b => ok_b; case: v' ok_v' => // b ok_v' /= ?; subst b;
    (case: (eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b}).
  + t_xrbindP => pc ok_pc <- {ls'} /=.
    rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
    by eexists; split; eauto; constructor.
  case => <- /=; eexists; split; first by reflexivity.
  by constructor => //; rewrite /setpc /= eqpc.
Qed.

Lemma match_state_step rip ls ls' xs :
  match_state rip ls xs →
  step ls = ok ls' →
  ∃ xs',
  fetch_and_eval xs = ok xs' ∧
  match_state rip ls' xs'.
Proof.
move => ms; rewrite /step /find_instr /fetch_and_eval; case: (ms)=> _ eqc ->.
case ok_i : (oseq.onth) => [ i | // ].
have [j [-> ok_j]] := mapM_onth eqc ok_i.
exact: assemble_iP.
Qed.

Lemma match_state_sem rip ls ls' xs :
  lsem ls ls' →
  match_state rip ls xs →
  ∃ xs',
    x86sem xs xs' ∧
    match_state rip ls' xs'.
Proof.
move => h; elim/lsem_ind: h xs; clear.
- move => ls xs h; exists xs; split => //; exact: rt_refl.
move => ls1 ls2 ls3 h1 h ih xs1 m1.
have [xs2 [x m2]] := match_state_step m1 h1.
have [xs3 [y m3]] := ih _ m2.
exists xs3; split => //.
apply: x86sem_trans; last by eauto.
exact: rt_step.
Qed.

Section PROG.

Context (p: lprog) (p': xprog) (ok_p': assemble_prog p = ok p').

Local Notation rip := (mk_rip p.(lp_rip)).

Definition get_reg_value (st: x86_mem) (r: register) : value :=
  Vword (xreg st r).

Definition get_reg_values st rs : values :=
  map (get_reg_value st) rs.

Lemma write_vars_uincl ii xs vs s1 s2 rs xm1 :
  write_vars xs vs s1 = ok s2 →
  reg_of_vars ii xs = ok rs →
  lom_eqv rip s1 xm1 →
  List.Forall2 value_uincl vs (get_reg_values xm1 rs) →
  lom_eqv rip s2 xm1.
Proof.
elim: xs vs s1 s2 rs.
+ by case => // s1 _ _ [<-] [<-].
move => x xs ih /= [] // v vs s1 s3 rs';
  t_xrbindP => s2 ok_s2 ok_s3 r ok_r rs ok_rs <- {rs'} h /List_Forall2_inv_l [v'] [vs'] [/=] /seq_eq_injL [<- {v'} <- {vs'}] [hv rec].
apply: ih; eauto.
move: ok_s2; rewrite /write_var /set_var /=.
have <- /= := var_of_reg_of_var ok_r.
t_xrbindP => vm;apply: on_vuP => // w hw <- <-.
case: h => h1 hrip hd h2 h3 h4; constructor => //=.
+ by rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
+ move=> r' v'; rewrite /get_var /on_vu /=.
  case: (r =P r') => [<- | hne].
  + rewrite Fv.setP_eq => -[<-] /=.
    have hu1 : value_uincl (Vword (pw_word w)) v.
    + have [sz [w' [-> -> /=]]]:= to_pwordI hw.
      case: Sumbool.sumbool_of_bool => hle //=.
      by apply word_uincl_zero_ext; apply cmp_nle_le; rewrite hle.
    by apply (value_uincl_trans hu1 hv).
  rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply var_of_register_inj.
  by apply h2. 
+ move=> r' v'; rewrite /get_var /on_vu /=.
  by rewrite Fv.setP_neq //; apply h3.
move=> f v'; rewrite /get_var /on_vu /=.
by rewrite Fv.setP_neq //; apply h4.
Qed.

(* TODO: Move this *)
Lemma truncate_val_uincl ty v v' :
  truncate_val ty v = ok v' →
  value_uincl v' v.
Proof.
apply: rbindP => z hz [<-].
case: ty z hz => /=.
- by move => b /to_boolI ->.
- by move => z /of_val_int ->.
- move => n t; case: v => //= [len a | []//].
  by rewrite /WArray.cast /WArray.uincl; case: ZleP => // ? [<-].
move => sz w /of_val_word [sz'] [w'] [hle -> ->].
exact: word_uincl_zero_ext.
Qed.

Lemma get_reg_of_vars_uincl ii xs rs vm vs (rm: regmap) :
  (∀ r v, get_var vm (var_of_register r) = ok v → value_uincl v (Vword (rm r))) →
  reg_of_vars ii xs = ok rs →
  mapM (λ x : var_i, get_var vm x) xs = ok vs →
  List.Forall2 value_uincl vs (map (λ r, Vword (rm r)) rs).
Proof.
move => h; elim: xs rs vs.
+ by move => _ _ [<-] [<-]; constructor.
move => x xs ih rs' vs' /=; t_xrbindP => r ok_r rs ok_rs <- {rs'} v ok_v vs ok_vs <- {vs'} /=.
constructor; last exact: ih.
apply: h. rewrite -ok_v {ok_v}; f_equal; apply: var_of_register_of_var.
case: x ok_r => /= x _; exact: reg_of_var_register_of_var.
Qed.

Lemma check_rip_ok : 
  register_of_var rip == None ->
  disj_rip rip.
Proof.
  move=> /eqP h; split => r heq //.
  by move: h; rewrite -heq register_of_var_of_register.
Qed.

Lemma assemble_fdP wrip m1 fn va m2 vr :
  lsem_fd p wrip m1 fn va m2 vr →
  ∃ fd va',
    get_fundef p.(lp_funcs) fn = Some fd ∧
    mapM2 ErrType truncate_val (lfd_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef p'.(xp_funcs) fn = Some fd' ∧
    ∀ st1,
      List.Forall2 value_uincl va' (get_reg_values st1 fd'.(xfd_arg)) →
      st1.(xmem) = m1 →
      ∃ st2,
        x86sem_fd p' wrip fn st1 st2 ∧
        List.Forall2 value_uincl vr (get_reg_values st2 fd'.(xfd_res)) ∧
        st2.(xmem) = m2.
Proof.
case => m1' fd va' vm2 m2' s1 s2 vr' ok_fd ok_m1' /= [<-] {s1} ok_va'.
set vm1 := (vm in {| evm := vm |}).
move => ok_s2 hexec ok_vr' ok_vr -> {m2}.
exists fd, va'. split; first exact: ok_fd. split; first exact: ok_va'.
have [fds [hp' hrip ok_fds]]: exists fds, [/\ p' = {|xp_globs := p.(lp_globs); xp_funcs := fds |}, 
                       disj_rip rip &
                       map_cfprog (assemble_fd rip) (lp_funcs p) = ok fds].
+ have := ok_p'.
  rewrite /assemble_prog; t_xrbindP => _ /assertP /check_rip_ok hrip fds ok_fds <-.
  by exists fds.
subst p'.
have [fd' [h ok_fd']] := get_map_cfprog ok_fds ok_fd.
exists fd'; split => //. 
move => s1 hargs ?; subst m1.
move: h; rewrite /assemble_fd; t_xrbindP => body ok_body.
case ok_sp: (reg_of_string _) => [ sp | // ].
t_xrbindP => args ok_args dsts ok_dsts _ /assertP hsp tosave ? savedstk ? [?]; subst fd'.
set xr1 := mem_write_reg sp (top_stack m1') {| xmem := m1' ; xreg := s1.(xreg) ; xrip := wrip; xxreg := s1.(xxreg) ; xrf := rflagmap0 |}.
have eqm1 : lom_eqv rip {| emem := m1' ; evm := vm1 |} xr1.
+ constructor => //.
  - by rewrite /get_var /vm1 /= Fv.setP_eq.
  - rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK sp)).
    rewrite /get_var /var_of_register /RegMap.set ffunE; case: eqP.
    * move => -> {r} /=.
      rewrite Fv.setP_neq; last first.
      + by apply /eqP => -[] heq; case: hrip => /(_ sp); rewrite /var_of_register -heq.
      rewrite Fv.setP_eq word_extend_reg_id // zero_extend_u => -[<-];
      exact: word_uincl_refl.
    move => ne; rewrite /= Fv.setP_neq; last first.
    + by apply /eqP => -[] heq; case: hrip => /(_ r); rewrite /var_of_register -heq.
    rewrite Fv.setP_neq /vmap0 ?Fv.get0 //.
    by apply/eqP => -[] /inj_string_of_register ?; apply: ne.
  - by move => r v; rewrite /vm1 /= /get_var !Fv.setP_neq // /vmap0 Fv.get0.
  move => f v /=; rewrite /vm1 /rflagmap0 ffunE /=.
  by rewrite /var_of_flag /get_var /= !Fv.setP_neq // /vmap0 Fv.get0.
have h1 : get_reg_values xr1 args = get_reg_values s1 args.
+ rewrite /get_reg_values /get_reg_value /xr1 /=.
  apply: map_ext => // r /xseq.InP hr; f_equal.
  rewrite ffunE; case: eqP => // e.
  by elim: (elimN idP hsp); rewrite -e.
rewrite -h1 in hargs => {h1}.
have eqm2 : lom_eqv rip s2 xr1.
+ by apply: write_vars_uincl; eauto.
have ms : match_state rip (of_estate s2 fd.(lfd_body) 0) {| xm := xr1 ; xc := body ; xip := 0 |}.
+ by constructor => //=; rewrite to_estate_of_estate.
have [[[om or orip oxr orf] oc opc] [xexec]] := match_state_sem hexec ms.
rewrite (mapM_size ok_body).
case => eqm' /=.
rewrite ok_body => -[?] ?; subst oc opc.
eexists; split. econstructor; eauto.
case: eqm' => /= ?; subst om => eqr' _; split => //.
rewrite /get_reg_values /get_reg_value /=.
apply: (Forall2_trans value_uincl_trans).
+ apply: (mapM2_Forall2 _ ok_vr) => a b r _; exact: truncate_val_uincl.
apply: get_reg_of_vars_uincl; eassumption.
Qed.

Lemma assemble_fd_stk_size fd xfd :
  assemble_fd rip fd = ok xfd →
  lfd_stk_size fd = xfd_stk_size xfd.
Proof.
rewrite /assemble_fd; t_xrbindP => c _.
by case: reg_of_string => //; t_xrbindP => ? ? ? ? ? ? ? ? ? ? ? [<-].
Qed.

End PROG.

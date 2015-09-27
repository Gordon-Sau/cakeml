open preamble BasicProvers
     wordLangTheory wordPropsTheory word_instTheory wordSemTheory
     asmTheory word_allocTheory

val _ = new_theory "word_instProof";

val sym_sub_tac = SUBST_ALL_TAC o SYM;

(*First step: Make op expressions have exactly 2 args*)
(*Semantics*)
val flatten_exp_ok = prove(``
  ∀exp s.
  word_exp s exp = word_exp s (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>rw[]>>
  fs[flatten_exp_def]
  >-
    (fs[flatten_exp_def,word_exp_def]>>LET_ELIM_TAC>>
    `ws = ws'` by
      (match_mp_tac LIST_EQ>>unabbrev_all_tac>>fs[EL_MAP,EL_MEM])>>
    metis_tac[])
  >>
    fs[word_exp_def,LET_THM,word_op_def]>>IF_CASES_TAC>>fs[]>>
    TRY(first_x_assum(qspec_then `s` assume_tac)>>rfs[]>>
    pop_assum sym_sub_tac>>fs[])>>metis_tac[option_CLAUSES])

(*All ops are 2 args. Technically, we should probably check that Sub has 2 args. However, the semantics already checks that and it will get removed later*)
val binary_branch_exp_def = tDefine "binary_branch_exp" `
  (binary_branch_exp (Op Sub exps) = EVERY (binary_branch_exp) exps) ∧
  (binary_branch_exp (Op op xs) = (LENGTH xs = 2 ∧ EVERY (binary_branch_exp) xs)) ∧
  (binary_branch_exp (Load exp) = binary_branch_exp exp) ∧
  (binary_branch_exp (Shift shift exp nexp) = binary_branch_exp exp) ∧
  (binary_branch_exp exp = T)`
  (WF_REL_TAC `measure (exp_size ARB)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC))

(*Syntax*)
val flatten_exp_binary_branch_exp = prove(``
  ∀exp.
  binary_branch_exp (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>fs[flatten_exp_def,binary_branch_exp_def,EVERY_MEM,EVERY_MAP])

val flatten_exp_every_var_exp = prove(``
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>fs[flatten_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP])

val num_exp_equiv = prove(``
  word_inst$num_exp = wordSem$num_exp``,
  fs[FUN_EQ_THM]>>Induct>>
  fs[wordSemTheory.num_exp_def,word_instTheory.num_exp_def])

val locals_rel_def = Define`
  locals_rel temp (s:'a word_loc num_map) t ⇔ (∀x. x < temp ⇒ lookup x s = lookup x t)`

val locals_rel_word_exp = prove(``
  ∀s exp w.
  every_var_exp (λx. x < temp) exp ∧
  word_exp s exp = SOME w ∧
  locals_rel temp s.locals loc ⇒
  word_exp (s with locals:=loc) exp = SOME w``,
  ho_match_mp_tac word_exp_ind>>rw[]>>
  fs[word_exp_def,every_var_exp_def,locals_rel_def]
  >-
    (EVERY_CASE_TAC>>
    res_tac>>fs[])
  >-
    (qpat_assum`A= SOME w` mp_tac>>FULL_CASE_TAC>>fs[mem_load_def])
  >-
    (qpat_assum`A= SOME w` mp_tac>>
    LET_ELIM_TAC>>
    Cases_on`EVERY IS_SOME ws`>>fs[]>>
    `ws = ws'` by
      (unabbrev_all_tac>>
      fs[LIST_EQ,MAP_EQ_f,EVERY_MEM,MEM_MAP,IS_SOME_EXISTS]>>rw[]>>
      res_tac>>fs[])>>
    metis_tac[])
  >>
    EVERY_CASE_TAC>>res_tac>>fs[])
     
(*2nd step: Convert expressions to insts*)
val inst_select_exp_thm = prove(``
  ∀c tar temp exp s w loc.
  binary_branch_exp exp ∧
  every_var_exp (λx. x < temp) exp ∧
  locals_rel temp s.locals loc ∧
  word_exp s exp = SOME w
  ⇒
  ∃loc'.
  evaluate ((inst_select_exp c tar temp exp),s with locals:=loc) = (NONE:'a result option,s with locals:=loc') ∧
  ∀x.
    if x = tar then lookup x loc' = SOME (Word w)
    else if x < temp then lookup x loc' = lookup x s.locals
    else T``,
  ho_match_mp_tac inst_select_exp_ind>>
  fs[inst_select_exp_def,evaluate_def,binary_branch_exp_def,every_var_exp_def]>>
  rpt strip_tac
  >-
    (*TODO: Will be replaced by munched version*)
    (fs[GSYM AND_IMP_INTRO,word_exp_def]>>EVERY_CASE_TAC>>fs[]>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
    simp[LET_THM,evaluate_def]>>rw[]>>
    `lookup temp loc' = SOME (Word x)` by metis_tac[]>>
    simp[inst_def,assign_def,word_exp_def,word_op_def]>>fs[mem_load_def]>>
    simp[state_component_equality,set_var_def,lookup_insert]>>
    rw[]>>DISJ2_TAC>>strip_tac>>
    `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def]>>
    simp[state_component_equality,locals_rel_def,lookup_insert]>>
    fs[locals_rel_def])
  >-
    (fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    fs[locals_rel_def]>>pop_assum mp_tac>>ntac 2 FULL_CASE_TAC>>fs[]>>
    res_tac>>fs[alist_insert_def]>>rw[]>>
    simp[state_component_equality,lookup_insert])
  >-
    (fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    FULL_CASE_TAC>>fs[]>>pop_assum mp_tac>>FULL_CASE_TAC>>fs[locals_rel_def]>>
    simp[state_component_equality,lookup_insert])
  >-
    (*TODO: Will be replaced by munched version
      But this shows that the invs work for multiple temporaries
    *)
    (`binary_branch_exp exp ∧ binary_branch_exp exp'` by 
      (Cases_on`op`>>fs[binary_branch_exp_def])>>
    fs[word_exp_def,LET_THM,IS_SOME_EXISTS]>>
    first_x_assum(qspecl_then[`s`,`x`,`loc`] assume_tac)>>rfs[evaluate_def]>>
    simp[LET_THM,inst_def,assign_def]>>
    first_x_assum(qspecl_then[`s with locals:= loc'`,`x'`,`loc'`] mp_tac)>>
    fs[]>>discharge_hyps>-
      (rw[locals_rel_def]
      >-
        (match_mp_tac every_var_exp_mono>>
        HINT_EXISTS_TAC>>fs[]>>DECIDE_TAC)
      >>
        (*word_exp invariant under extra locals*)
        match_mp_tac locals_rel_word_exp>>
        fs[locals_rel_def]>>
        rw[]>>`x'' ≠ temp` by DECIDE_TAC>>
        metis_tac[])
    >>
      strip_tac>>fs[word_exp_def]>>
      `lookup temp loc'' = SOME (Word x) ∧
       lookup (temp+1) loc'' = SOME (Word x')` by
         (first_assum(qspecl_then[`temp`] assume_tac)>>
         first_x_assum(qspecl_then[`temp+1`] assume_tac)>>
         `temp ≠ temp+1` by DECIDE_TAC>>
         fs[]>>metis_tac[])>>
      simp[LET_THM,state_component_equality,set_var_def,lookup_insert]>>
      rw[]>>DISJ2_TAC>>strip_tac>>
      `x''<temp+1 ∧ x'' ≠ temp ∧ x'' ≠ temp+1` by DECIDE_TAC>>
      metis_tac[])
  >-
    (fs[GSYM AND_IMP_INTRO,word_exp_def]>>EVERY_CASE_TAC>>fs[]>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
    simp[]>>strip_tac>>
    simp[evaluate_def,inst_def,word_exp_def,assign_def,num_exp_def]>>
    `lookup temp loc' = SOME (Word x)` by metis_tac[]>>
    fs[num_exp_equiv,set_var_def,state_component_equality,lookup_insert]>>
    rw[]>>DISJ2_TAC>>strip_tac>>
    `x' ≠ temp` by DECIDE_TAC>>
    metis_tac[])
  >>
    fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    Cases_on`v14`>>fs[binary_branch_exp_def])

val locals_rel_get_vars  = prove(``
  ∀ls vs.
  get_vars ls st = SOME vs ∧
  EVERY (λx. x < temp) ls ∧
  locals_rel temp st.locals loc ⇒
  get_vars ls (st with locals:= loc) = SOME vs``,
  Induct>>fs[get_vars_def]>>rw[]>>
  qpat_assum`A=SOME vs` mp_tac>>ntac 2 FULL_CASE_TAC>>rw[]>>
  res_tac>>fs[get_var_def,locals_rel_def]>>
  res_tac>>
  fs[])

val locals_rel_alist_insert = prove(``
  ∀ls vs s t.
  locals_rel temp s t ∧
  EVERY (λx. x < temp) ls ⇒
  locals_rel temp (alist_insert ls vs s) (alist_insert ls vs t)``,
  ho_match_mp_tac alist_insert_ind>>fs[alist_insert_def,locals_rel_def]>>
  rw[]>>
  Cases_on`x'=ls`>>fs[lookup_insert])

val locals_rel_get_var = prove(``
  r < temp ∧
  get_var r st = SOME x ∧
  locals_rel temp st.locals loc ⇒
  get_var r (st with locals:=loc) = SOME x``,
  fs[get_var_def,locals_rel_def]>>
  metis_tac[])

val locals_rel_get_var_imm = prove(``
  every_var_imm (λx.x<temp) r ∧
  get_var_imm r st = SOME x ∧
  locals_rel temp st.locals loc ⇒
  get_var_imm r (st with locals:=loc) = SOME x``,
  Cases_on`r`>>fs[get_var_imm_def,every_var_imm_def]>>
  metis_tac[locals_rel_get_var])

val locals_rel_set_var = prove(``
  ∀n s t.
  locals_rel temp s t ⇒ 
  locals_rel temp (insert n v s) (insert n v t)``,
  rw[]>>fs[locals_rel_def,lookup_insert])

(*Extra temporaries not mentioned in program
  do not affect evaluation
  This is extra work, but might be helpful in props?
  Otherwise, just prove it together with the inst
  select thm
*)
val locals_rel_evaluate_thm = prove(``
  ∀prog st res rst loc temp.
  evaluate (prog,st) = (res,rst) ∧
  res ≠ SOME Error ∧
  every_var (λx.x < temp) prog ∧
  locals_rel temp st.locals loc ⇒
  ∃loc'.
  evaluate (prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  locals_rel temp rst.locals loc'``,
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog`>>
  fs[evaluate_def,LET_THM]
  >-
    metis_tac[]
  >-
    (qpat_assum `A = (res,rst)` mp_tac>> ntac 2 FULL_CASE_TAC>>
    fs[every_var_def]>>
    imp_res_tac locals_rel_get_vars>>
    fs[set_vars_def]>>imp_res_tac locals_rel_alist_insert>>
    fs[state_component_equality]>>
    rw[]>>metis_tac[])
  >-
    (Cases_on`i`>>fs[inst_def,every_var_def,every_var_inst_def]
    >-
      metis_tac[]
    >-
      (fs[assign_def,word_exp_def,set_var_def]>>
      imp_res_tac locals_rel_set_var>>
      fs[state_component_equality]>>
      metis_tac[])
    >>
      cheat)
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>fs[every_var_def]>>
    rfs[state_component_equality,set_var_def]>>
    qpat_assum`A=rst.locals` sym_sub_tac>>
    metis_tac[locals_rel_set_var])
  >>
    cheat)

val inst_select_thm = prove(``
  ∀c temp prog st res rst loc.
  evaluate (prog,st) = (res,rst) ∧
  every_var (λx. x < temp) prog ∧
  res ≠ SOME Error ∧
  locals_rel temp st.locals loc ⇒
  ∃loc'.
  evaluate (inst_select c temp prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  locals_rel temp rst.locals loc'``,
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def,locals_rel_evaluate_thm]
  >-
    (fs[evaluate_def]>>last_x_assum mp_tac>>FULL_CASE_TAC>>rw[]>>
    fs[every_var_def]>>imp_res_tac flatten_exp_every_var_exp>>
    fs[Once flatten_exp_ok]>>
    assume_tac flatten_exp_binary_branch_exp>>
    imp_res_tac inst_select_exp_thm>>rfs[]>>
    first_x_assum(qspecl_then[`c'`,`c`] assume_tac)>>fs[]>>
    simp[state_component_equality,set_var_def,locals_rel_def]>>
    rw[]>>fs[lookup_insert]>>Cases_on`x'=c'`>>fs[]>>
    metis_tac[])
  >-
    (fs[evaluate_def]>>last_x_assum mp_tac>>
    FULL_CASE_TAC>>fs[]>>strip_tac>>
    fs[every_var_def]>>imp_res_tac flatten_exp_every_var_exp>>
    fs[Once flatten_exp_ok]>>
    assume_tac flatten_exp_binary_branch_exp>>
    imp_res_tac inst_select_exp_thm>>rfs[]>>
    first_x_assum(qspecl_then[`temp`,`c`] assume_tac)>>fs[]>>
    fs[LET_THM,evaluate_def,word_exp_def]>>
    first_assum(qspec_then`temp` assume_tac)>>fs[set_store_def]>>
    fs[state_component_equality,locals_rel_def]>>
    rw[]>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (*undo the munched version*)
    cheat
  >-
    (*Seq*)
    (fs[evaluate_def,LET_THM]>>Cases_on`evaluate(prog,st)`>>
    fs[every_var_def,GSYM AND_IMP_INTRO]>>
    `q ≠ SOME Error` by (EVERY_CASE_TAC>>fs[])>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
    fs[]>> disch_then (qspec_then`loc` assume_tac)>>rfs[]>>
    IF_CASES_TAC>>fs[]>>
    metis_tac[])
  >-
    (fs[evaluate_def]>>ntac 4 (pop_assum mp_tac)>>ntac 4 FULL_CASE_TAC>>
    fs[every_var_def]>>
    rw[]>> imp_res_tac locals_rel_get_var>>
    imp_res_tac locals_rel_get_var_imm>>fs[GSYM AND_IMP_INTRO,every_var_def])
  >-
    (*Long proof, but should just need to unwind and apply the IH
      on the state itself, noting that locals_rel is reflexive*)
    cheat)

(*No expressions nesting
  TODO: Probably rename this and add the inst_ok bits to it
  Alternatively, add another every_inst condition
*)
val flat_exp_conventions_def = Define`
  (*These should be converted to Insts*)
  (flat_exp_conventions (Assign v exp) = F) ∧
  (flat_exp_conventions (Store exp num) = F) ∧
  (*The only place where top level (expression) vars are allowed*)
  (flat_exp_conventions (Set store_name (Var r)) = T) ∧
  (flat_exp_conventions (Set store_name _) = F) ∧
  (flat_exp_conventions (Seq p1 p2) =
    (flat_exp_conventions p1 ∧ flat_exp_conventions p2)) ∧
  (flat_exp_conventions (If cmp r1 ri e2 e3) =
    (flat_exp_conventions e2 ∧
    flat_exp_conventions e3)) ∧
  (flat_exp_conventions (Call ret dest args h) =
    ((case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
        flat_exp_conventions ret_handler) ∧
    (case h of
      NONE => T
    | SOME (v,prog,l1,l2) => flat_exp_conventions prog))) ∧
  (flat_exp_conventions _ = T)`

val inst_select_exp_conventions = prove(``
  ∀c tar temp exp.
  flat_exp_conventions (inst_select_exp c tar temp exp)``,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>fs[inst_select_exp_def,flat_exp_conventions_def,LET_THM])

val inst_select_conventions = prove(``
  ∀c temp prog.
  flat_exp_conventions (inst_select c temp prog)``,
  ho_match_mp_tac inst_select_ind >>rw[]>>
  fs[flat_exp_conventions_def,inst_select_def,LET_THM]>>
  EVERY_CASE_TAC>>
  fs[flat_exp_conventions_def]>>
  metis_tac[inst_select_exp_conventions])

(*3rd step: 3 to 2 reg if necessary*)

val distinct_tar_reg_def = Define`
  (distinct_tar_reg (Arith (Binop bop r1 r2 ri))
    ⇔ (r1 ≠ r2 ∧ case ri of (Reg r3) => r1 ≠ r3 | _ => T)) ∧
  (distinct_tar_reg  (Arith (Shift l r1 r2 n))
    ⇔ r1 ≠ r2) ∧
  (distinct_tar_reg _ ⇔ T)`

(*Instructions are 2 register code for arith ok*)
val two_reg_inst_def = Define`
  (two_reg_inst (Arith (Binop bop r1 r2 ri))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (Shift l r1 r2 n))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst _ ⇔ T)`

(*TODO: move to HOL*)
val insert_shadow = prove(``
  ∀t a b c.
  insert a b (insert a c t) = insert a b t``,
  completeInduct_on`a`>>
  Induct>>
  simp[Once insert_def]>>
  rw[]>>
  simp[Once insert_def]>>
  simp[Once insert_def,SimpRHS]>>
  `(a-1) DIV 2 < a` by
    (`0 < (2:num)` by fs[] >>
    imp_res_tac DIV_LT_X>>
    first_x_assum match_mp_tac>>
    DECIDE_TAC)>>
  metis_tac[])

(*Semantics preservation*)
val three_to_two_reg_correct = prove(``
  ∀prog s res s'.
  every_inst distinct_tar_reg prog ∧
  evaluate (prog,s) = (res,s') ∧ res ≠ SOME Error
  ⇒
  evaluate(three_to_two_reg prog,s) = (res,s')``,
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[]>>fs[three_to_two_reg_def,evaluate_def,state_component_equality]>>
  TRY
    (ntac 2 (pop_assum mp_tac)>>fs[inst_def,assign_def,word_exp_def,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    EVERY_CASE_TAC >>
    fs[LET_THM,alist_insert_def,every_inst_def,distinct_tar_reg_def,word_exp_def,lookup_insert,set_var_def,insert_shadow]>>NO_TAC)
  >-
    (ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>fs[every_inst_def]>>
    Cases_on`res'' = SOME Error`>>fs[]>>res_tac>>
    EVERY_CASE_TAC>>fs[]>>
    metis_tac[])
  >-
    (ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>fs[every_inst_def]>>
    unabbrev_all_tac>>
    Cases_on`ret`>>Cases_on`handler`>>fs[evaluate_def]
    >-
      (EVERY_CASE_TAC>>fs[])
    >-
      (EVERY_CASE_TAC>>fs[]>>
      res_tac>>fs[]>>
      rfs[])
    >>
      PairCases_on`x`>>PairCases_on`x'`>>fs[]>>
      Cases_on`get_vars args s`>>fs[]>>
      Cases_on`find_code dest x s.code`>>fs[]>>
      Cases_on`x'`>>Cases_on`cut_env x1 s.locals`>>fs[]>>
      IF_CASES_TAC>>fs[push_env_def,LET_THM]>>
      EVERY_CASE_TAC>>fs[]>>
      res_tac>>fs[]>>
      rfs[]))

(*Syntactic correctness*)
val three_to_two_reg_syn = prove(``
  ∀prog. every_inst two_reg_inst (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>fs[every_inst_def,two_reg_inst_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>fs[])

(*word_alloc preserves all syntactic program convs*)
val word_alloc_two_reg_inst_lem = prove(``
  ∀f prog.
  every_inst two_reg_inst prog ⇒
  every_inst two_reg_inst (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>fs[every_inst_def]>>rw[]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>
    fs[apply_colour_inst_def,two_reg_inst_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>fs[every_inst_def])

val word_alloc_two_reg_inst = prove(``
  ∀k prog.
  every_inst two_reg_inst prog ⇒
  every_inst two_reg_inst (word_alloc k prog)``,
  fs[word_alloc_two_reg_inst_lem,word_alloc_def,LET_THM])

val word_alloc_flat_exp_conventions_lem = prove(``
  ∀f prog.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>fs[flat_exp_conventions_def]>>rw[]
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>fs[flat_exp_conventions_def])
  >>
    Cases_on`exp`>>fs[flat_exp_conventions_def])

val word_alloc_flat_exp_conventions = prove(``
  ∀k prog.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (word_alloc k prog)``,
  fs[word_alloc_flat_exp_conventions_lem,word_alloc_def,LET_THM])

val fake_moves_flat_exp_conventions = prove(``
  ∀ls ssal ssar na l r a b c.
  fake_moves ls ssal ssar na = (l,r,a,b,c) ⇒
  flat_exp_conventions l ∧
  flat_exp_conventions r``,
  Induct>>fs[fake_moves_def]>>rw[]>>fs[flat_exp_conventions_def]>>
  pop_assum mp_tac>> LET_ELIM_TAC>> EVERY_CASE_TAC>> fs[LET_THM]>>unabbrev_all_tac>>
  metis_tac[flat_exp_conventions_def,fake_move_def])

(*ssa generates distinct regs and also preserves flattening*)
val ssa_cc_trans_flat_exp_conventions_lem = prove(``
  ∀prog ssa na.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (FST (ssa_cc_trans prog ssa na))``,
  ho_match_mp_tac ssa_cc_trans_ind>>fs[ssa_cc_trans_def]>>rw[]>>
  unabbrev_all_tac>>
  fs[flat_exp_conventions_def]
  >-
    (pop_assum mp_tac>>fs[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>fs[flat_exp_conventions_def]>>
    metis_tac[fake_moves_flat_exp_conventions,flat_exp_conventions_def])
  >-
    (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>fs[flat_exp_conventions_def,EQ_SYM_EQ])
  >-
    (Cases_on`exp`>>fs[ssa_cc_trans_exp_def,flat_exp_conventions_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>fs[flat_exp_conventions_def]
    >-
      (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
      LET_ELIM_TAC>>fs[flat_exp_conventions_def,EQ_SYM_EQ])
    >>
      LET_ELIM_TAC>>unabbrev_all_tac>>
      fs[list_next_var_rename_move_def,flat_exp_conventions_def]>>
      fs[fix_inconsistencies_def]>>
      rpt (pop_assum mp_tac)>> LET_ELIM_TAC>>fs[]>>
      metis_tac[fake_moves_flat_exp_conventions,flat_exp_conventions_def])

val _ = export_theory ();

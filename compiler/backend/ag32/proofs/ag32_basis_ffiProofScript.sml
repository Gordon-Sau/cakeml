(*
  Verify that the ag32 implementation of the FFI primitives satisfies
  interference_implemented.
*)

open preamble
  ag32_memoryTheory
  ag32_machine_configTheory
  ag32_ffi_codeProofTheory
local open blastLib basis_ffiTheory in end

val _ = new_theory"ag32_basis_ffiProof";

(* TODO: move *)

val INDEX_OF_IMP_EL = store_thm("INDEX_OF_IMP_EL",
  ``!xs x index. (INDEX_OF x xs = SOME index) ==> (EL index xs = x)``,
  rw [GSYM find_index_INDEX_OF]
  \\ imp_res_tac find_index_LESS_LENGTH \\ fs[]
  \\ imp_res_tac find_index_is_MEM
  \\ imp_res_tac find_index_MEM
  \\ first_x_assum (qspec_then `0` mp_tac)
  \\ fs []);

val IN_all_words = Q.store_thm("IN_all_words", (* should replace IN_all_words_add *)
  `x ∈ all_words base n ⇔ (∃i. i < n ∧ x = base + n2w i)`,
  qid_spec_tac`base`
  \\ Induct_on`n`
  \\ rw[all_words_def, ADD1]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  >- ( qexists_tac`i + 1` \\ simp[GSYM word_add_n2w] )
  \\ Cases_on`i` \\ fs[ADD1]
  \\ disj2_tac
  \\ simp[GSYM word_add_n2w]
  \\ asm_exists_tac \\ simp[]);

val bytes_in_memory_UPDATE_GT = Q.store_thm("bytes_in_memory_UPDATE_GT",`
  k <+ (pc:word32) ∧
  LENGTH ls <= 2**31 ∧
  ¬word_msb pc ∧
  bytes_in_memory pc ls m dm ⇒
  bytes_in_memory pc ls ((k =+ v)m) dm`,
  rw[]>>
  match_mp_tac asmPropsTheory.bytes_in_memory_change_mem>>
  asm_exists_tac>>fs[APPLY_UPDATE_THM]>>
  ntac 2 strip_tac>>
  `k <+ pc + n2w n` by
    (match_mp_tac WORD_LOWER_LOWER_EQ_TRANS>>
    asm_exists_tac>>fs[]>>
    fs[WORD_LS]>>
    DEP_REWRITE_TAC [w2n_add]>>
    fs[word_msb_n2w_numeric])>>
  rw[]>>fs[WORD_LOWER_REFL]);

val bytes_in_memory_UPDATE_LT = Q.store_thm("bytes_in_memory_UPDATE_LT",`
  (w2n pc + (LENGTH ls) <= w2n (k:word32)) ∧
  LENGTH ls <= 2**31 ∧
  ¬word_msb pc ∧
  bytes_in_memory pc ls m dm ⇒
  bytes_in_memory pc ls ((k =+ v)m) dm`,
  rw[]>>
  match_mp_tac asmPropsTheory.bytes_in_memory_change_mem>>
  asm_exists_tac>>fs[APPLY_UPDATE_THM]>>
  ntac 2 strip_tac>>
  `n + w2n pc < w2n k` by fs[]>>
  rw[]>>
  CCONTR_TAC>> pop_assum kall_tac>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC [w2n_add]>>
  fs[word_msb_n2w_numeric]);

val bytes_in_memory_asm_write_bytearray_LT = Q.store_thm("bytes_in_memory_asm_write_bytearray_LT",`
  (w2n pc + (LENGTH ls) <= w2n (k:word32)) ∧
  (w2n k + (LENGTH bs) < dimword(:32))∧
  LENGTH ls <= 2**31 ∧
  ¬word_msb pc ∧
  bytes_in_memory pc ls m dm ⇒
  bytes_in_memory pc ls (asm_write_bytearray k bs m) dm`,
  rw[]>>
  match_mp_tac asmPropsTheory.bytes_in_memory_change_mem>>
  asm_exists_tac>>fs[APPLY_UPDATE_THM]>>
  ntac 2 strip_tac>>
  `n + w2n pc < w2n k` by fs[]>>
  rw[]>>
  match_mp_tac EQ_SYM>>
  match_mp_tac asm_write_bytearray_unchanged>>
  simp[]>>
  DISJ1_TAC>>simp[WORD_LO]>>
  DEP_REWRITE_TAC [w2n_add]>>
  fs[word_msb_n2w_numeric]);

val _ = temp_overload_on("nxt",
  ``λmc n ms. FUNPOW mc.target.next n ms``);

val interference_implemented_def = Define`
  interference_implemented mc ffi_rel md ms0 ⇔
    ∃next_interfer ccache_interfer ffi_interfer.
    (∀n. mc.next_interfer n = next_interfer) ∧
    (∀n. mc.ccache_interfer n = ccache_interfer) ∧
    (∀n. mc.ffi_interfer n = ffi_interfer) ∧
    ∀ms k0.
      (ms = FUNPOW mc.target.next k0 ms0) ∧
      (∀x. x ∉ md ∧ x ∉ mc.prog_addresses ⇒ (mc.target.get_byte ms x = mc.target.get_byte ms0 x))
      ⇒
      (mc.target.get_pc ms ∈ mc.prog_addresses ∧
       encoded_bytes_in_mem mc.target.config (mc.target.get_pc ms)
         (mc.target.get_byte ms) mc.prog_addresses ∧
       (∀x. x ∉ mc.prog_addresses ⇒ (mc.target.get_byte (mc.target.next ms) x = mc.target.get_byte ms x)) ∧
       mc.target.state_ok ms
      ⇒
        ∃k. (next_interfer (mc.target.next ms)
             = FUNPOW mc.target.next k (mc.target.next ms)) ∧
            (ffi_rel ms = ffi_rel (mc.target.next ms)) ∧
            (ffi_rel (mc.target.next ms) =
             ffi_rel (FUNPOW mc.target.next k (mc.target.next ms))) ∧
            (∀x. x ∉ md ∨ x ∈ mc.prog_addresses ⇒
                  (mc.target.get_byte (FUNPOW mc.target.next k (mc.target.next ms)) x =
                   mc.target.get_byte (mc.target.next ms) x))) ∧
      ((mc.target.get_pc ms = mc.ccache_pc) ⇒
        ∃k. (ccache_interfer
             (mc.target.get_reg ms mc.ptr_reg,
              mc.target.get_reg ms mc.len_reg,ms)
             = FUNPOW mc.target.next k ms) ∧
            (ffi_rel ms =
             ffi_rel (FUNPOW mc.target.next k ms)) ∧
            (∀x. x ∉ md ∨ x ∈ mc.prog_addresses ⇒
              (mc.target.get_byte (FUNPOW mc.target.next k ms) x =
               mc.target.get_byte ms x))) ∧
        ∀ffi ffi_index bytes bytes2 new_ffi new_bytes.
          (find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME ffi_index) ∧
          (read_ffi_bytearrays mc ms = (SOME bytes, SOME bytes2)) ∧
          (call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 =
            FFI_return new_ffi new_bytes) ∧
          (ffi_rel ms ffi)
          ⇒
          ∃k.
            (ffi_interfer (ffi_index,new_bytes,ms) =
             FUNPOW mc.target.next k ms) ∧
            (ffi_rel (FUNPOW mc.target.next k ms) new_ffi) ∧
            (∀x. x ∉ md ∧
                 x ∉ all_words (mc.target.get_reg ms mc.ptr2_reg) (LENGTH bytes2) ⇒
              (mc.target.get_byte (FUNPOW mc.target.next k ms) x =
               mc.target.get_byte ms x))`;

val evaluate_Halt_FUNPOW_next = Q.store_thm("evaluate_Halt_FUNPOW_next",
  `∀mc (ffi:'ffi ffi_state) k ms t ms' ffi'.
   interference_implemented mc ffi_rel md ms ∧ ffi_rel ms ffi ∧
   (evaluate mc ffi k ms = (Halt t, ms', ffi')) ⇒
     ∃k'. (ms' = FUNPOW mc.target.next k' ms) ∧
          (ffi_rel ms' ffi') ∧
          (∀x. x ∉ md ∪ mc.prog_addresses ⇒ (mc.target.get_byte ms' x = mc.target.get_byte ms x)) ∧
          ((∀x. t ≠ FFI_outcome x) ⇒ (mc.target.get_pc ms' = mc.halt_pc)) ∧
          (((mc.target.get_reg ms' mc.ptr_reg = 0w) ∧ (∀x. t ≠ FFI_outcome x))
            ⇒ (t = Success))`,
  ho_match_mp_tac targetSemTheory.evaluate_ind
  \\ rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ pop_assum mp_tac
  \\ simp[Once targetSemTheory.evaluate_def]
  \\ fs[CaseEq"bool",targetSemTheory.apply_oracle_def,shift_seq_def]
  \\ strip_tac \\ fs[] \\ rw[]
  \\ TRY (qexists_tac`0` \\ simp[] \\ NO_TAC)
  >- (
    last_x_assum mp_tac
    \\ impl_tac
    >- (
      fs[interference_implemented_def]
      \\ conj_tac >- (
        qx_gen_tac`k0`
        \\ strip_tac
        \\ first_assum(qspec_then`0`mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(mp_tac o CONJUNCT1)
        \\ impl_tac >- fs[]
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD]
        \\ first_x_assum(qspec_then`SUC(k0+k1)`mp_tac)
        \\ simp[FUNPOW] \\ strip_tac
        \\ rw[] \\ fs[ADD1,FUNPOW_ADD]
        \\ metis_tac[])
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[] \\ rw[] \\ fs[]
      \\ metis_tac[])
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac o CONJUNCT1)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2+1` \\ rw[FUNPOW_ADD])
  >- (
    last_x_assum mp_tac
    \\ impl_tac
    >- (
      conj_tac >- (
        fs[interference_implemented_def]
        \\ qx_gen_tac`k0`
        \\ first_assum(qspec_then`0`mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(mp_tac o CONJUNCT1 o CONJUNCT2)
        \\ impl_tac >- fs[]
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD] \\ rw[]
        \\ first_x_assum(qspec_then`k0+k1`mp_tac)
        \\ simp[]
        \\ disch_then(mp_tac o CONJUNCT2 o CONJUNCT2)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then match_mp_tac \\ rw[]
        \\ fs[targetSemTheory.read_ffi_bytearrays_def,
              targetSemTheory.read_ffi_bytearray_def])
      \\ fs[interference_implemented_def]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then(qx_choose_then`k1`strip_assume_tac o CONJUNCT1)
      \\ fs[GSYM FUNPOW_ADD]
      \\ metis_tac[])
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac o CONJUNCT1)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2` \\ rw[])
  >- (
    fs[CaseEq"option",CaseEq"prod"]
    \\ reverse(fs[CaseEq"ffi$ffi_result"]) \\ rfs[]
    >- ( qexists_tac`0` \\ rw[] )
    \\ last_x_assum drule
    \\ fs[]
    \\ impl_tac
    >- (
      conj_tac >- (
        fs[interference_implemented_def]
        \\ qx_gen_tac`k0`
        \\ first_assum(qspec_then`0`mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(mp_tac o CONJUNCT2 o CONJUNCT2)
        \\ simp_tac(srw_ss())[]
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD]
        \\ strip_tac
        \\ first_x_assum(qspec_then`k0+k1`mp_tac)
        \\ simp[]
        \\ impl_tac
        >- (
          rw[]
          \\ first_x_assum irule
          \\ rw[]
          \\ fs[targetSemTheory.read_ffi_bytearrays_def]
          \\ imp_res_tac targetPropsTheory.read_ffi_bytearray_IMP_SUBSET_prog_addresses
          \\ fs[SUBSET_DEF]
          \\ metis_tac[] )
        \\ rw[]
        \\ first_x_assum match_mp_tac
        \\ fs[targetSemTheory.read_ffi_bytearrays_def,
              targetSemTheory.read_ffi_bytearray_def]
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ fs[])
      \\ fs[interference_implemented_def]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then (first_assum o mp_then Any mp_tac)
      \\ impl_tac >- fs[]
      \\ disch_then(qx_choose_then`k1`strip_assume_tac)
      \\ fs[GSYM FUNPOW_ADD]
      \\ metis_tac[evaluatePropsTheory.call_FFI_rel_def])
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[]
    \\ disch_then (first_assum o mp_then Any mp_tac)
    \\ impl_tac >- fs[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2` \\ rw[]
    \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [targetSemTheory.read_ffi_bytearrays_def]
    \\ imp_res_tac targetPropsTheory.read_ffi_bytearray_IMP_SUBSET_prog_addresses
    \\ fs [SUBSET_DEF] \\ metis_tac []));

val machine_sem_Terminate_FUNPOW_next = Q.store_thm("machine_sem_Terminate_FUNPOW_next",
  `interference_implemented mc ffi_rel md ms ∧
   (ffi_rel ms st) ∧
   machine_sem mc (st:'ffi ffi_state) ms (Terminate t io_events) ⇒
   ∃k st'.
     ffi_rel (nxt mc k ms) st' ∧ (io_events = st'.io_events) ∧
       (∀x. x ∉ md ∪ mc.prog_addresses ⇒ (mc.target.get_byte (nxt mc k ms) x = mc.target.get_byte ms x)) ∧
       ((∀x. t ≠ FFI_outcome x) ⇒ (mc.target.get_pc (nxt mc k ms) = mc.halt_pc)) ∧
       ((mc.target.get_reg (nxt mc k ms) mc.ptr_reg = 0w) ∧ (∀x. t ≠ FFI_outcome x)
        ⇒ (t = Success))`,
  rw[targetSemTheory.machine_sem_def]
  \\ imp_res_tac evaluate_Halt_FUNPOW_next
  \\ rfs[] \\ PROVE_TAC[]);

val word_of_bytes_bytes_to_word = Q.store_thm("word_of_bytes_bytes_to_word",
  `∀be a bs k.
   LENGTH bs ≤ k ⇒
   (word_of_bytes be a bs = bytes_to_word k a bs 0w be)`,
  Induct_on`bs`
  >- (
    EVAL_TAC
    \\ Cases_on`k`
    \\ EVAL_TAC
    \\ rw[] )
  \\ rw[data_to_word_memoryProofTheory.word_of_bytes_def]
  \\ Cases_on`k` \\ fs[]
  \\ rw[data_to_word_memoryProofTheory.bytes_to_word_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ first_x_assum match_mp_tac
  \\ fs[]);

val word_of_bytes_extract_bytes_le_32 = Q.store_thm("word_of_bytes_extract_bytes_le_32",
  `word_of_bytes F 0w [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] = w : word32`,
  rw[data_to_word_memoryProofTheory.word_of_bytes_def]
  \\ rw[wordSemTheory.set_byte_def,wordSemTheory.byte_index_def,wordSemTheory.word_slice_alt_def]
  \\ blastLib.BBLAST_TAC);

val bytes_in_mem_bytes_in_memory = Q.store_thm("bytes_in_mem_bytes_in_memory",
  `∀a bs m md k. bytes_in_mem a bs m md k ⇔ bytes_in_memory a bs m (md DIFF k)`,
  Induct_on`bs` \\ EVAL_TAC \\ rw[]
  \\ rw[EQ_IMP_THM]);

val read_bytearray_IMP_bytes_in_memory_WORD_LOWER = Q.store_thm("read_bytearray_IMP_bytes_in_memory_WORD_LOWER",
  `∀p n m ba m' md.
   (n = LENGTH ba) ∧ w2n p + n < dimword(:'a) ∧
   (∀k. (p <=+ k ∧ k <+ p + n2w n) ⇒ k ∈ md ∧ (m k = SOME (m' k))) ∧
   (read_bytearray (p:'a word) n m = SOME ba) ⇒
   bytes_in_memory p ba m' md`,
  Induct_on`ba` \\ rw[] >- EVAL_TAC
  \\ simp[asmSemTheory.bytes_in_memory_def]
  \\ fs[read_bytearray_def, CaseEq"option"]
  \\ first_assum(qspec_then`p`mp_tac)
  \\ impl_tac
  >- (
    simp[WORD_LOWER_EQ_REFL]
    \\ Cases_on`p`
    \\ simp[word_add_n2w, word_lo_n2w] \\ fs[] )
  \\ rw[]
  \\ first_x_assum irule
  \\ Cases_on`p` \\ fs[ADD1,word_add_n2w]
  \\ qexists_tac`m` \\ fs[]
  \\ Cases \\ strip_tac
  \\ first_x_assum irule
  \\ simp[WORD_LOWER_EQ_REFL, word_ls_n2w]
  \\ fs[word_lo_n2w, word_ls_n2w] \\ rfs[]);

val bytes_in_memory_IMP_asm_write_bytearray = store_thm(
   "bytes_in_memory_IMP_asm_write_bytearray",
  ``!bs a m. bytes_in_memory a bs m md ==> (asm_write_bytearray a bs m = m)``,
  rw [FUN_EQ_THM]
  \\ irule asm_write_bytearray_id
  \\ metis_tac [asmPropsTheory.bytes_in_memory_EL]);

val IMP_word_list = Q.store_thm("IMP_word_list",
  `8 <= dimindex(:'a) ⇒
   ∀p ls m.
   (m = IMAGE (λk. (p + n2w k * (bytes_in_word:'a word), EL k ls)) (count (LENGTH ls))) ∧
   w2n p + LENGTH ls * w2n (bytes_in_word:'a word) < dimword(:'a)
   ⇒ word_list p ls m`,
  strip_tac
  \\ Induct_on`ls` \\ rw[word_list_def] >- EVAL_TAC
  \\ fs[]
  \\ first_x_assum(qspec_then`p + bytes_in_word`mp_tac)
  \\ impl_tac
  >- (
    fs[ADD1, LEFT_ADD_DISTRIB]
    \\ Cases_on`p` \\ Cases_on`bytes_in_word`
    \\ fs[word_add_n2w] )
  \\ qmatch_goalsub_abbrev_tac`word_list _ ls m2`
  \\ strip_tac
  \\ simp[set_sepTheory.STAR_def]
  \\ simp[set_sepTheory.one_def]
  \\ qexists_tac`m2`
  \\ simp[set_sepTheory.SPLIT_def]
  \\ conj_tac
  >- (
    simp[Abbr`m2`,EXTENSION]
    \\ qx_gen_tac`x`
    \\ Cases_on`x = (p,h)` \\ fs[]
    >- ( qexists_tac`0` \\ simp[] )
    \\ EQ_TAC \\ strip_tac \\ simp[]
    >- (
      qexists_tac`SUC k`
      \\ simp[GSYM word_add_n2w,ADD1,WORD_LEFT_ADD_DISTRIB])
    \\ Cases_on`k` >- fs[]
    \\ simp[]
    \\ qexists_tac`n`
    \\ simp[GSYM word_add_n2w,ADD1,WORD_LEFT_ADD_DISTRIB])
  \\ rw[Abbr`m2`]
  \\ Cases_on`k < LENGTH ls` \\ fs[]
  \\ rpt disj1_tac
  \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
  \\ rewrite_tac[addressTheory.WORD_EQ_ADD_CANCEL]
  \\ Cases_on`bytes_in_word`
  \\ fs[word_add_n2w,word_mul_n2w,ADD1,LEFT_ADD_DISTRIB]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ fs[]
  \\ conj_tac >- (
    irule LESS_EQ_LESS_TRANS
    \\ qpat_x_assum`_ +_ < _`assume_tac
    \\ asm_exists_tac \\ fs[]
    \\ irule LESS_EQ_TRANS
    \\ qexists_tac`n * LENGTH ls`
    \\ simp[]
    \\ CONV_TAC(LAND_CONV (REWR_CONV MULT_COMM))
    \\ simp[] )
  \\ disj1_tac
  \\ fs[bytes_in_word_def]
  \\ rw[]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ simp[dimword_def,DIV_LT_X,DIV_EQ_0]
  \\ `dimindex(:'a) = 1 * dimindex(:'a)` by fs[]
  \\ pop_assum(CONV_TAC o LAND_CONV o REWR_CONV)
  \\ irule bitTheory.LESS_MULT_MONO2
  \\ simp[]);

(*
val align_eq_0_imp = Q.store_thm("align_eq_0_imp",
  `0 < p ⇒ ((align p a = 0w) ⇒ w2n a < 2 ** p)`,
  rw[alignmentTheory.align_w2n, dimword_def]
  \\ reverse(Cases_on`p ≤ dimindex(:'a)`)
  >- (
    qspec_then`a`assume_tac w2n_lt
    \\ fs[dimword_def]
    \\ irule LESS_LESS_EQ_TRANS
    \\ asm_exists_tac \\ fs[] )
  \\ fs[MOD_EQ_0_DIVISOR]
  \\ Cases_on`d` \\ fs[]
  >- (
    `1 < 2 ** p` by fs[ONE_LT_EXP]
    \\ fs[DIV_EQ_0] )
  \\ fs[MULT]
*)

val get_byte_word_of_bytes = Q.store_thm("get_byte_word_of_bytes",
  `good_dimindex(:'a) ⇒
   i < LENGTH ls ∧ LENGTH ls ≤ w2n (bytes_in_word:'a word) ⇒
  (get_byte (n2w i) (word_of_bytes be (0w:'a word) ls) be = EL i ls)`,
  strip_tac
  \\ `∃k. dimindex(:'a) DIV 8 = 2 ** k` by(
    fs[labPropsTheory.good_dimindex_def]
    \\ TRY(qexists_tac`2` \\ EVAL_TAC \\ NO_TAC)
    \\ TRY(qexists_tac`3` \\ EVAL_TAC \\ NO_TAC) )
  \\ strip_tac
  \\ Q.ISPECL_THEN[`be`,`0w`,`ls`,`2 ** k`]mp_tac word_of_bytes_bytes_to_word
  \\ impl_keep_tac >- (
    rfs[bytes_in_word_def, dimword_def]
    \\ fs[labPropsTheory.good_dimindex_def] \\ rfs[])
  \\ rw[]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_bytes_to_word]
  \\ rw[]);

val word_msb_align = Q.store_thm("word_msb_align",
  `p < dimindex(:'a) ⇒ (word_msb (align p w) = word_msb (w:'a word))`,
  rw[alignmentTheory.align_bitwise_and,word_msb]
  \\ rw[data_to_word_memoryProofTheory.word_bit_and]
  \\ rw[data_to_word_memoryProofTheory.word_bit_lsl]
  \\ rw[word_bit_test, MOD_EQ_0_DIVISOR, dimword_def]);

val get_byte_EL_words_of_bytes = Q.store_thm("get_byte_EL_words_of_bytes",
  `∀be ls.
   i < LENGTH ls ∧ w2n (bytes_in_word:'a word) * LENGTH ls ≤ dimword(:'a) ∧ good_dimindex(:'a) ⇒
   (get_byte (n2w i : α word)
      (EL (w2n (byte_align ((n2w i):α word)) DIV (w2n (bytes_in_word:α word)))
        (words_of_bytes be ls)) be = EL i ls)`,
  completeInduct_on`i`
  \\ Cases_on`ls`
  \\ rw[data_to_word_memoryProofTheory.words_of_bytes_def]
  \\ qmatch_goalsub_abbrev_tac`MAX 1 bw`
  \\ `0 < bw` by (
     fs[Abbr`bw`,labPropsTheory.good_dimindex_def]
     \\ EVAL_TAC \\ fs[dimword_def] )
  \\ `MAX 1 bw = bw` by rw[MAX_DEF] \\ fs[]
  \\ Cases_on`i < bw` \\ fs[]
  >- (
    `byte_align (n2w i) = 0w`
    by(
      simp[alignmentTheory.byte_align_def]
      \\ irule imp_align_eq_0
      \\ fs[labPropsTheory.good_dimindex_def,Abbr`bw`]
      \\ rfs[bytes_in_word_def,dimword_def] )
    \\ simp[ZERO_DIV]
    \\ DEP_REWRITE_TAC[UNDISCH get_byte_word_of_bytes]
    \\ fs[LENGTH_TAKE_EQ]
    \\ Cases_on`i` \\ fs[EL_TAKE] )
  \\ fs[NOT_LESS]
  \\ pop_assum (strip_assume_tac o SIMP_RULE std_ss [LESS_EQ_EXISTS])
  \\ `byte_align (n2w (bw + p)) = n2w bw + byte_align (n2w p)`
  by (
    simp[GSYM word_add_n2w]
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[align_add_aligned_gen]
    \\ simp[Abbr`bw`]
    \\ CONV_TAC(REWR_CONV(GSYM alignmentTheory.byte_aligned_def))
    \\ (data_to_word_assignProofTheory.byte_aligned_bytes_in_word
        |> Q.GEN`w` |> Q.SPEC`1w` |> UNDISCH |> mp_tac)
    \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ conj_tac
  >- (
    simp[Abbr`bw`]
    \\ reverse conj_tac >- (
      fs[labPropsTheory.good_dimindex_def,
         bytes_in_word_def]
      \\ EVAL_TAC \\ fs[] \\ EVAL_TAC )
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[word_msb_align]
    \\ conj_tac >- ( fs[labPropsTheory.good_dimindex_def])
    \\ simp[word_msb_n2w]
    \\ qmatch_assum_abbrev_tac`bw * r ≤ dimword _`
    \\ `r ≤ dimword (:'a) DIV bw` by fs[X_LE_DIV]
    \\ `p < dimword(:'a) DIV bw` by fs[]
    \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
    \\ fs[dimword_def, bytes_in_word_def]
    \\ fs[Abbr`bw`, labPropsTheory.good_dimindex_def]
    \\ rfs[] )
  \\ `bw < dimword(:'a)` by fs[Abbr`bw`, bytes_in_word_def]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ simp[]
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]
  \\ `n2w bw = byte_align (n2w bw)`
  by(
    fs[Abbr`bw`,bytes_in_word_def,alignmentTheory.byte_align_def]
    \\ fs[labPropsTheory.good_dimindex_def]
    \\ EVAL_TAC \\ fs[dimword_def] \\ EVAL_TAC )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ simp[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ first_x_assum(qspec_then`p`mp_tac)
  \\ simp[]
  \\ disch_then(qspecl_then[`be`,`DROP (bw-1)t`]mp_tac)
  \\ impl_tac >- fs[ADD1]
  \\ simp[EL_DROP]);

val words_of_bytes_append_word = Q.store_thm("words_of_bytes_append_word",
  `0 < LENGTH l1 ∧ (LENGTH l1 = w2n (bytes_in_word:'a word)) ⇒
   (words_of_bytes be (l1 ++ l2) = word_of_bytes be (0w:'a word) l1 :: words_of_bytes be l2)`,
  rw[]
  \\ Cases_on`l1` \\ rw[data_to_word_memoryProofTheory.words_of_bytes_def] \\ fs[]
  \\ fs[MAX_DEF]
  \\ first_x_assum(assume_tac o SYM) \\ fs[ADD1]
  \\ rw[TAKE_APPEND,DROP_APPEND,DROP_LENGTH_NIL] \\ fs[]);

val get_mem_word_get_byte_gen = Q.store_thm("get_mem_word_get_byte_gen",
  `(∀x. r0 + n2w (4 * (LENGTH ll + k)) <=+ x ∧ x <+ r0 + n2w (4 * (LENGTH ll + k) + 4)
      ⇒ (m x = get_byte x (EL (w2n (byte_align x - r0) DIV 4) (ll ++ ls ++ lr)) F)) ∧
   (LENGTH ll = off) ∧
   k < LENGTH ls ∧ byte_aligned r0 ∧ (4 * (off + k)) < dimword(:31) ∧
   w2n r0 + (4 * (off + k) + 4) < dimword(:32)
   ⇒ (get_mem_word m (r0 + n2w (4 * (off + k))) = EL k ls)`,
  rw[get_mem_word_def]
  \\ ntac 4 (
    qmatch_goalsub_abbrev_tac`m x`
    \\ first_assum(qspec_then`x`mp_tac)
    \\ impl_tac
    >- (
      fs[Abbr`x`]
      \\ Cases_on`r0` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ disch_then SUBST_ALL_TAC
    \\ qunabbrev_tac`x`)
  \\ last_x_assum kall_tac
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ simp[GSYM ALIGNED_eq_aligned]
    \\ simp[addressTheory.ALIGNED_n2w])
  \\ simp[align_add_aligned_gen]
  \\ simp[Abbr`pc`]
  \\ qmatch_goalsub_abbrev_tac`r0 + x`
  \\ `align 2 (r0 + x) = r0 + x` by fs[alignmentTheory.aligned_def]
  \\ `r0 + x = byte_align (r0 + x)` by fs[alignmentTheory.byte_align_def]
  \\ qhdtm_x_assum`align`SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum SUBST_ALL_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ DEP_REWRITE_TAC[
       data_to_word_memoryProofTheory.get_byte_byte_align
       |> Q.GEN`a'` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[]]
  \\ rewrite_tac[CONJ_ASSOC]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ conj_tac >- ( simp[Abbr`x`] \\ EVAL_TAC )
  \\ conj_tac >- (
    fs[Abbr`x`, word_msb_n2w_numeric, NOT_LESS_EQUAL]
    \\ EVAL_TAC )
  \\ `w2n x DIV 4 = k + LENGTH ll`
  by (
    simp[Abbr`x`]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ pop_assum SUBST_ALL_TAC
  \\ ntac 3 (
    qmatch_goalsub_abbrev_tac`w2n a`
    \\ pop_assum mp_tac \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac \\ simp[Abbr`a`] )
  \\ simp[EL_APPEND_EQN]
  \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def]
  \\ blastLib.BBLAST_TAC);

val get_mem_word_get_byte =
  get_mem_word_get_byte_gen
  |> Q.GEN`r0` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[EVAL``byte_aligned 0w``]
  |> curry save_thm "get_mem_word_get_byte";

val asm_step_target_configured = Q.store_thm("asm_step_target_configured",
  `asm_step c s1 i s2 ∧ target_configured s1 mc ⇒
   target_configured s2 mc`,
  rw[asmSemTheory.asm_step_def]
  \\ fs[lab_to_targetProofTheory.target_configured_def]);

val RTC_asm_step_target_configured = Q.store_thm("RTC_asm_step_target_configured",
  `RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2 ∧
   target_configured s1 mc ⇒
   target_configured s2 mc`,
  rw[]
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac \\ rw[]
  \\ metis_tac[asm_step_target_configured]);

val LENGTH_words_of_bytes = Q.store_thm("LENGTH_words_of_bytes",
  `8 ≤ dimindex(:'a) ⇒
   ∀be ls.
   (LENGTH (words_of_bytes be ls : 'a word list) =
    LENGTH ls DIV (w2n (bytes_in_word : 'a word)) +
    MIN 1 (LENGTH ls MOD (w2n (bytes_in_word : 'a word))))`,
  strip_tac
  \\ recInduct data_to_word_memoryProofTheory.words_of_bytes_ind
  \\ `1 ≤ w2n bytes_in_word`
  by (
    simp[bytes_in_word_def,dimword_def]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ rw[DIV_LT_X, X_LT_DIV, X_LE_DIV]
    \\ match_mp_tac LESS_TRANS
    \\ qexists_tac`2 ** dimindex(:'a)`
    \\ simp[] )
  \\ simp[data_to_word_memoryProofTheory.words_of_bytes_def]
  \\ conj_tac
  >- ( DEP_REWRITE_TAC[ZERO_DIV] \\ fs[] )
  \\ rw[ADD1]
  \\ `MAX 1 (w2n (bytes_in_word:'a word)) = w2n (bytes_in_word:'a word)`
      by rw[MAX_DEF]
  \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`(m - n) DIV _`
  \\ Cases_on`m < n` \\ fs[]
  >- (
    `m - n = 0` by fs[]
    \\ simp[]
    \\ simp[LESS_DIV_EQ_ZERO]
    \\ rw[MIN_DEF]
    \\ fs[Abbr`m`] )
  \\ simp[SUB_MOD]
  \\ qspec_then`1`(mp_tac o GEN_ALL)(Q.GEN`q`DIV_SUB) \\ fs[]
  \\ disch_then kall_tac
  \\ Cases_on`m MOD n = 0` \\ fs[]
  >- (
    DEP_REWRITE_TAC[SUB_ADD]
    \\ fs[X_LE_DIV] )
  \\ `MIN 1 (m MOD n) = 1` by simp[MIN_DEF]
  \\ fs[]
  \\ `m DIV n - 1 + 1 = m DIV n` suffices_by fs[]
  \\ DEP_REWRITE_TAC[SUB_ADD]
  \\ fs[X_LE_DIV]);

val ag32_io_events_unchanged = Q.store_thm("ag32_io_events_unchanged",
  `Decode (
    let v : word32 = (31 >< 2) ms.PC : word30 @@ (0w:word2) in
      (ms.MEM (v + 3w) @@
       ((ms.MEM (v + 2w) @@
         ((ms.MEM (v + 1w) @@
           ms.MEM (v + 0w)) : word16)) : word24)))
    ≠ Interrupt
   ⇒
   ((Next ms).io_events = ms.io_events) `,
  rw[ag32Theory.Next_def]
  \\ rw[ag32Theory.Run_def]
  \\ PURE_CASE_TAC \\ fs[] \\ TRY(PairCases_on`p`)
  \\ rw[
    ag32Theory.dfn'Accelerator_def,
    ag32Theory.dfn'In_def,
    ag32Theory.dfn'Jump_def,
    ag32Theory.ALU_def,
    ag32Theory.dfn'JumpIfNotZero_def,
    ag32Theory.dfn'JumpIfZero_def,
    ag32Theory.dfn'LoadConstant_def,
    ag32Theory.dfn'LoadMEM_def,
    ag32Theory.dfn'LoadMEMByte_def,
    ag32Theory.dfn'LoadUpperConstant_def,
    ag32Theory.dfn'Normal_def,
    ag32Theory.norm_def,
    ag32Theory.dfn'Out_def,
    ag32Theory.dfn'Shift_def,
    ag32Theory.dfn'StoreMEM_def,
    ag32Theory.dfn'StoreMEMByte_def,
    ag32Theory.incPC_def]
  \\ PURE_CASE_TAC \\ fs[] \\ rw[]);

val ag32_enc_lengths = Q.store_thm("ag32_enc_lengths",
  `LENGTH (ag32_enc istr) ∈ {4;8;12;16}`,
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\  rw[ag32_targetTheory.ag32_enc_def,
         ag32_targetTheory.ag32_constant_def,
         ag32_targetTheory.ag32_jump_constant_def,
         ag32_targetTheory.ag32_encode_def,
         ag32_targetTheory.ag32_encode1_def]);

val ag32_enc_not_Interrupt = Q.store_thm("ag32_enc_not_Interrupt",
  `4 * k < LENGTH (ag32_enc istr) ⇒
   let bs = DROP (4 * k) (ag32_enc istr) in
   Decode (EL 3 bs @@ ((EL 2 bs @@ ((EL 1 bs @@ EL 0 bs) : word16)) : word24)) ≠ Interrupt`,
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\ rw[ag32_targetTheory.ag32_enc_def,
        ag32_targetTheory.ag32_encode_def,
        ag32_targetTheory.ag32_encode1_def,
        ag32_targetProofTheory.concat_bytes,
        ag32_targetTheory.ag32_constant_def,
        ag32_targetTheory.ag32_jump_constant_def,
        ag32_targetProofTheory.Decode_Encode]
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC k < _`
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC k) < _`
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC (SUC k)) < _`
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]);

val RTC_asm_step_ag32_target_state_rel_io_events = Q.store_thm("RTC_asm_step_ag32_target_state_rel_io_events",
  `target_state_rel ag32_target s1 ms ∧
   RTC (λs1 s2. ∃i. asm_step ag32_config s1 i s2) s1 s2
   ⇒
   ∃n. target_state_rel ag32_target s2 (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ s1.mem_domain ⇒ ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  once_rewrite_tac[CONJ_COMM]
  \\ rewrite_tac[GSYM AND_IMP_INTRO]
  \\ qid_spec_tac`ms`
  \\ simp[RIGHT_FORALL_IMP_THM]
  \\ qho_match_abbrev_tac`RR^* s1 s2 ⇒ P s1 s2`
  \\ match_mp_tac RTC_INDUCT
  \\ simp[Abbr`P`,Abbr`RR`]
  \\ conj_tac
  >- ( rw[] \\ qexists_tac`0` \\ simp[] )
  \\ rpt gen_tac \\ strip_tac
  \\ ntac 2 strip_tac
  \\ ((MATCH_MP
        (REWRITE_RULE[GSYM AND_IMP_INTRO] targetPropsTheory.backend_correct_asm_step_target_state_rel)
        ag32_targetProofTheory.ag32_backend_correct) |> GEN_ALL |> drule)
  \\ simp[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.config``]
  \\ simp[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.next``]
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ fs[GSYM FUNPOW_ADD]
  \\ once_rewrite_tac[CONJ_COMM]
  \\ asm_exists_tac \\ simp[]
  \\ `y.mem_domain = x.mem_domain`
  by ( fs[asmSemTheory.asm_step_def] \\ rveq \\ fs[] )
  \\ fs[]
  \\ ntac 4 (pop_assum kall_tac)
  \\ fs[asmSemTheory.asm_step_def]
  \\ `x.pc = ms.PC` by (
    fs[asmPropsTheory.target_state_rel_def, ag32_targetTheory.ag32_target_def] )
  \\ pop_assum SUBST_ALL_TAC
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.get_byte``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.state_ok``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.get_pc``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_config_def]``ag32_config.encode``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_config_def]``ag32_config.code_alignment``]
  \\ `bytes_in_memory ms.PC (ag32_enc i) ms.MEM x.mem_domain`
  by (
    fs[asmPropsTheory.target_state_rel_def]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.get_byte``]
    \\ rw[]
    \\ first_x_assum(irule o GSYM)
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ fs[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ok (FUNPOW Next n ms)` by fs[asmPropsTheory.target_state_rel_def, ag32_targetTheory.ag32_target_def]
  \\ qpat_x_assum`∀j x. _`kall_tac
  \\ ntac 3 (pop_assum mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ qid_spec_tac`ms`
  \\ Induct_on`n` \\ simp[]
  \\ rw[FUNPOW_SUC]
  \\ qho_match_abbrev_tac`f (Next (FUNPOW Next n ms)) = f ms`
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac`f (FUNPOW Next n ms)`
  \\ (reverse conj_tac >- ( fsrw_tac[DNF_ss][Abbr`f`] \\ first_x_assum irule \\ simp[] ) )
  \\ qunabbrev_tac`f`
  \\ irule ag32_io_events_unchanged
  \\ qmatch_goalsub_abbrev_tac`st.MEM`
  \\ `bytes_in_memory ms.PC (ag32_enc i) st.MEM x.mem_domain`
  by (
    irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ fsrw_tac[DNF_ss][asmPropsTheory.all_pcs_thm, PULL_EXISTS,Abbr`st`])
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`m (pc + _)`
  \\ `ag32_ok st` by fs[Abbr`st`]
  \\ `aligned 2 st.PC` by rfs[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def]
  \\ `pc = st.PC`
  by (
    simp[Abbr`pc`]
    \\ pop_assum mp_tac
    \\ simp[alignmentTheory.aligned_extract]
    \\ blastLib.BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum(qspec_then`n`mp_tac) \\ rw[]
  \\ fs[asmPropsTheory.all_pcs_thm]
  \\ qmatch_asmsub_rename_tac`4 * k < _`
  \\ Q.ISPECL_THEN[`TAKE (4 * k) (ag32_enc i)`, `DROP (4 * k) (ag32_enc i)`,`ms.PC`]mp_tac asmPropsTheory.bytes_in_memory_APPEND
  \\ simp[]
  \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`pc + _`
  \\ qmatch_asmsub_abbrev_tac`bytes_in_memory pc bs`
  \\ `∀j. j < 4 ⇒ (m (pc + n2w j) = EL j bs)`
  by (
    rw[]
    \\ Q.ISPECL_THEN[`TAKE j bs`,`DROP j bs`,`st.PC`]mp_tac asmPropsTheory.bytes_in_memory_APPEND
    \\ simp[]
    \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
    \\ simp[]
    \\ `j < LENGTH bs` by (
      fs[Abbr`bs`]
      \\ qspec_then`i`mp_tac(Q.GEN`istr`ag32_enc_lengths)
      \\ Cases_on`k` \\ fs[]
      \\ Cases_on`n'` \\ fs[]
      \\ Cases_on`n''` \\ fs[]
      \\ Cases_on`n'` \\ fs[] )
    \\ Cases_on`DROP j bs` \\ fs[DROP_NIL]
    \\ simp[asmSemTheory.bytes_in_memory_def]
    \\ rw[]
    \\ imp_res_tac DROP_EL_CONS
    \\ rfs[] )
  \\ simp[]
  \\ drule ag32_enc_not_Interrupt
  \\ simp[]
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ simp[]);

val read_bytearray_IMP_domain = store_thm("read_bytearray_IMP_domain", (* replace uses with read_bytearray_IMP_mem_SOME *)
  ``!n a xs.
      (read_bytearray a n
        (λa. if a ∈ md then SOME (m a) else NONE) = SOME xs) ==>
      !i. i < n ==> a + n2w i IN md``,
  Induct \\ fs [read_bytearray_def] \\ rw []
  \\ fs [option_case_eq] \\ rveq \\ fs []
  \\ res_tac
  \\ Cases_on `i` \\ fs [ADD1,GSYM word_add_n2w]);

(* -- *)

val startup_asm_code_small_enough = Q.store_thm("startup_asm_code_small_enough",
  `∀i. LENGTH (ag32_enc i) * LENGTH (startup_asm_code n cl bl) ≤ startup_code_size`,
  gen_tac (* change startup_code_size definition if this does not go through *)
  \\ qspec_then`i`mp_tac (Q.GEN`istr`ag32_enc_lengths)
  \\ rw[LENGTH_startup_asm_code, startup_code_size_def]);

val FFI_codes_covers_basis_ffi = Q.store_thm("FFI_codes_covers_basis_ffi",
  `∀name st conf bytes. basis_ffi_oracle name st conf bytes ≠ Oracle_final FFI_failed ⇒ name ∈ set (MAP FST FFI_codes)`,
  rw[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[FFI_codes_def]
  \\ pop_assum mp_tac
  \\ rpt(IF_CASES_TAC \\ fs[]));

val get_output_io_event_def = Define`
  get_output_io_event (IO_event name conf bs2) =
    if name = "write" then
      case MAP FST bs2 of (n1 :: n0 :: off1 :: off0 :: tll) =>
        let k = MIN (w22n [n1; n0]) output_buffer_size in
        if (SND (HD bs2) = 0w) then
          let written = TAKE k (DROP (w22n [off1; off0]) tll) in
            SOME (conf ++ [0w;0w;n1;n0] ++ written)
        else SOME []
      | _ => NONE
    else NONE`;

val get_ag32_io_event_def = Define`
  get_ag32_io_event m =
    let call_id = m (n2w (ffi_code_start_offset - 1)) in
    if call_id = n2w (THE (ALOOKUP FFI_codes "write")) then
      if m (n2w output_offset) = 0w then
        let n1 = m (n2w (output_offset + 10)) in
        let n0 = m (n2w (output_offset + 11)) in
        let n = MIN (w22n [n1; n0]) output_buffer_size in
          read_bytearray (n2w output_offset) (8 + 4 + n) (SOME o m)
      else SOME []
    else NONE`;

val is_ag32_init_state_def = ag32_targetTheory.is_ag32_init_state_def;

val target_state_rel_ag32_init = Q.store_thm("target_state_rel_ag32_init",
  `is_ag32_init_state m ms ⇒
   target_state_rel ag32_target
    (ag32_init_asm_state m md) ms`,
  rw[asmPropsTheory.target_state_rel_def]
  >- (
    rw[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def]
    \\ fs[is_ag32_init_state_def]
    \\ fs[alignmentTheory.byte_aligned_def]
    \\ EVAL_TAC)
  >- ( fs[is_ag32_init_state_def,ag32_init_asm_state_def] \\ EVAL_TAC \\ fs[] )
  >- ( fs[is_ag32_init_state_def,ag32_init_asm_state_def] \\ EVAL_TAC \\ fs[] )
  >- (
    fs[is_ag32_init_state_def,ag32_init_asm_state_def]
    \\ ntac 2 (pop_assum mp_tac)
    \\ EVAL_TAC \\ rw[]
    \\ EVAL_TAC \\ rw[])
  >- ( pop_assum mp_tac \\ EVAL_TAC ));

val stdin_fs_def = Define`
  stdin_fs inp =
    <| files :=
       [(IOStream (strlit "stdout"), "")
       ;(IOStream (strlit "stderr"), "")
       ;(IOStream (strlit "stdin"), inp)]
     ; infds :=
       [(0, IOStream(strlit"stdin"), ReadMode, 0)
       ;(1, IOStream(strlit"stdout"), WriteMode, 0)
       ;(2, IOStream(strlit"stderr"), WriteMode, 0)]
     ; numchars := LGENLIST (K output_buffer_size) NONE
     ; maxFD := 2
     |>`;

val wfFS_stdin_fs = Q.store_thm("wfFS_stdin_fs",
  `wfFS (stdin_fs inp)`,
  rw[stdin_fs_def, fsFFIPropsTheory.wfFS_def] \\ rw[]
  \\ rw[fsFFIPropsTheory.liveFS_def]
  \\ rw[fsFFIPropsTheory.live_numchars_def]
  \\ qmatch_goalsub_abbrev_tac`always P ll`
  \\ `∀x. (x = ll) ⇒ always P x` suffices_by rw[]
  \\ ho_match_mp_tac always_coind
  \\ rw[]
  \\ qexists_tac`output_buffer_size`
  \\ conj_tac
  >- ( simp[Abbr`ll`] \\ simp[LGENLIST_EQ_CONS] )
  \\ simp[Abbr`P`]
  \\ EVAL_TAC);

val STD_streams_stdin_fs = Q.store_thm("STD_streams_stdin_fs",
  `STD_streams (stdin_fs inp)`,
  rw[fsFFIPropsTheory.STD_streams_def]
  \\ qexists_tac`0`
  \\ rw[stdin_fs_def]
  \\ rw[]
  \\ rw[EQ_IMP_THM]);

val ag32_fs_ok_def = Define`
  ag32_fs_ok fs ⇔
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (∀fd. IS_SOME (ALOOKUP fs.infds fd) ⇔ fd < 3) ∧
   (∀fd fnm md off.
     (ALOOKUP fs.infds fd = SOME (fnm,md,off)) ⇒
     ∃cnt. (ALOOKUP fs.files fnm = SOME cnt) ∧ (fd ∈ {1;2} ⇒ (off = LENGTH cnt))) ∧
   (* maybe *) fs.maxFD ≤ 2 ∧
   STD_streams fs`;

val ag32_stdin_implemented_def = Define`
  ag32_stdin_implemented fs m ⇔
    ∃off inp.
      (ALOOKUP fs.infds 0 = SOME (IOStream(strlit"stdin"), ReadMode, off)) ∧
      (ALOOKUP fs.files (IOStream(strlit"stdin")) = SOME inp) ∧
      (get_mem_word m (n2w stdin_offset) = n2w off) ∧
      (get_mem_word m (n2w (stdin_offset + 4)) = n2w (LENGTH inp)) ∧
      off ≤ LENGTH inp ∧ LENGTH inp ≤ stdin_size ∧
      bytes_in_memory (n2w (stdin_offset + 8)) (MAP (n2w o ORD) inp)
        m (all_words (n2w (stdin_offset + 8)) (LENGTH inp))`;

val ag32_cline_implemented_def = Define`
  ag32_cline_implemented cl m ⇔
    (get_mem_word m (n2w startup_code_size) = n2w (LENGTH cl)) ∧
    LENGTH cl < 256 * 256`;

val ag32_ffi_rel_def = Define`
  ag32_ffi_rel ms ffi ⇔
    (MAP get_ag32_io_event ms.io_events =
     MAP get_output_io_event ffi.io_events) ∧
    (ffi.oracle = basis_ffi_oracle) ∧
    (ag32_fs_ok (SND ffi.ffi_state)) ∧
    (ag32_stdin_implemented (SND ffi.ffi_state) ms.MEM) ∧
    (ag32_cline_implemented (FST ffi.ffi_state) ms.MEM)`;

val extract_write_def = Define`
  extract_write fd oevent =
    if NULL oevent then NONE else
      let conf = TAKE 8 oevent in
      if (w82n conf = fd) then
        SOME (DROP (8 + 4) oevent)
      else NONE`;

val extract_writes_def = Define`
  extract_writes fd oevents =
    FLAT (MAP (MAP (CHR o w2n) o THE) (FILTER IS_SOME (MAP (combin$C OPTION_BIND (extract_write fd)) oevents)))`;

(* TODO: why is this proof so slow? make it faster? *)
val extract_fs_extract_writes = Q.store_thm("extract_fs_extract_writes",
  `∀ls fs fs' off off' out rest.
   (extract_fs fs ls = SOME fs') ∧
   (* can only read/write up to output_buffer_size - this could be made more nuanced *)
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (* IOStream of interest exists at the start *)
   (ALOOKUP fs.infds fd = SOME (IOStream nam, WriteMode, LENGTH out)) ∧
   (ALOOKUP fs.files (IOStream nam) = SOME out) ∧
   (* no non-IOStream files *)
   (∀nm. ¬inFS_fname fs (File nm)) ∧
   (* well-formedness invariants for the filesystem *)
   (∀fd fnm md off. (ALOOKUP fs'.infds fd = SOME (fnm, md, off)) ⇒ inFS_fname fs' fnm) ∧
   (∀fd1 nm md1 off1 fd2 md2 off2. (* this one depends on us not being able to open IOStreams *)
     (ALOOKUP fs'.infds fd1 = SOME (IOStream nm, md1, off1)) ∧
     (ALOOKUP fs'.infds fd2 = SOME (IOStream nm, md2, off2))
     ⇒ (fd1 = fd2)) ∧
   (* -- *)
   (* nothing has changed except the IOStream of interest -- is this actually necessary? *)
   (∀x. x ≠ fd ⇒ (OPTREL (inv_image (=) FST) (ALOOKUP fs'.infds x) (ALOOKUP fs.infds x))) ∧
   (∀fnm. inFS_fname fs' fnm = inFS_fname fs fnm) ∧
   (* and it has only changed by appending *)
   (ALOOKUP fs'.infds fd = SOME (IOStream nam, WriteMode, LENGTH out + LENGTH rest)) ∧
   (ALOOKUP fs'.files (IOStream nam) = SOME (out ++ rest))
   ⇒
   (extract_writes fd (MAP get_output_io_event ls) = rest)`,
  Induct
  >- (
    rw[basis_ffiTheory.extract_fs_def, extract_writes_def]
    \\ fs[basis_ffiTheory.extract_fs_with_numchars_def]
    \\ rveq \\ fs[] )
  \\ Cases
  \\ rpt gen_tac
  \\ fs[basis_ffiTheory.extract_fs_def, PULL_EXISTS]
  \\ rw[]
  \\ fs[basis_ffiTheory.extract_fs_with_numchars_def]
  \\ fs[get_output_io_event_def]
  \\ reverse(rw[])
  >- (
    fs[extract_writes_def]
    \\ first_x_assum irule
    \\ fs[CaseEq"option"]
    >- ( qexists_tac`fs` \\ fs[] \\ metis_tac[])
    \\ fs[CaseEq"ffi_result"]
    \\ qexists_tac`fs'` \\ fs[]
    \\ fs[fsFFITheory.fs_ffi_part_def]
    \\ rveq
    \\ fs[CaseEq"bool"] \\ rveq
    >- (
      fs[fsFFITheory.ffi_open_in_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
      \\ TRY (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.openFile_def]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    >- (
      fs[fsFFITheory.ffi_open_out_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
      \\ TRY (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.openFile_truncate_def]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    >- (
      fs[fsFFITheory.ffi_read_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
      \\ fs[CaseEq"list"]
      \\ fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
      \\ TRY (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.read_def]
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.bumpFD_def]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ fs[fsFFIPropsTheory.forwardFD_def, ALIST_FUPDKEY_ALOOKUP]
      \\ rw[]
      \\ TRY PURE_CASE_TAC \\ fs[]
      \\ TRY PURE_CASE_TAC \\ fs[CaseEq"option"]
      \\ rveq \\ fs[] \\ rfs[]
      >- metis_tac[]
      >- ( first_x_assum drule \\ simp[OPTREL_def] )
      >- metis_tac[]
      >- metis_tac[]
      (*
      \\ imp_res_tac ALOOKUP_MEM
      \\ reverse(Cases_on`fnm`)
      >- ( fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD] \\ metis_tac[] )
      \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_keeps_iostreams)
      \\ simp[ALIST_FUPDKEY_ALOOKUP]
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ disch_then drule
      \\ simp[] *))
    >- (
      reverse(fs[fsFFITheory.ffi_close_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[])
      >- metis_tac[]
      >- metis_tac[]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ fs[fsFFITheory.closeFD_def]
      \\ rveq \\ fs[]
      \\ fs[ALOOKUP_ADELKEY]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_closes_iostreams)
      \\ simp[ALOOKUP_ADELKEY]
      \\ Cases_on`w82n l = fd` \\ fs[]
      >- (
        rw[]
        \\ simp[DISJ_EQ_IMP]
        \\ CONV_TAC SWAP_EXISTS_CONV
        \\ qexists_tac`w82n l` \\ simp[]
        \\ rw[] \\ strip_tac
        \\ first_x_assum(qspec_then`fd'`mp_tac)
        \\ impl_tac >- simp[]
        \\ simp[OPTREL_def, FORALL_PROD]
        \\ metis_tac[] )
      \\ first_assum(qspec_then`w82n l`mp_tac)
      \\ impl_tac >- simp[]
      \\ simp_tac (srw_ss())[Once OPTREL_def]
      \\ simp[EXISTS_PROD] \\ strip_tac
      \\ rw[] \\ rw[] \\ rw[]
      >- metis_tac[]
      (*
      >- metis_tac[]
      *)
      \\ rw[OPTREL_def]
      \\ first_x_assum(qspec_then`w82n l`mp_tac o CONV_RULE SWAP_FORALL_CONV) \\ rw[]
      \\ qmatch_asmsub_rename_tac`_ = SOME(x1,x2,x3)`
      \\ Cases_on`x1 = IOStream nam`
      >- (
        fs[] \\ CCONTR_TAC \\ fs[]
        \\ Cases_on`x2` \\ metis_tac[] )
      \\ `MEM x1 (MAP FST z.files)` by metis_tac[]
      \\ `IS_SOME (ALOOKUP z.files x1)`
      by simp[data_to_word_gcProofTheory.IS_SOME_ALOOKUP_EQ]
      \\ fs[IS_SOME_EXISTS]
      \\ reverse(Cases_on`x1`) \\ fs[]
      >- (
        imp_res_tac ALOOKUP_MEM
        \\ fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
        \\ metis_tac[] )
      \\ CCONTR_TAC \\ fs[]
      \\ Cases_on`fd' = fd` \\ fs[]
      \\ first_x_assum drule
      \\ simp[OPTREL_def, FORALL_PROD]
      \\ CCONTR_TAC \\ fs[]
      \\ metis_tac[])
    )
  \\ fs[fsFFITheory.fs_ffi_part_def]
  \\ fs[CaseEq"option",CaseEq"ffi_result"]
  \\ last_x_assum drule
  \\ fs[fsFFITheory.ffi_write_def]
  \\ fs[CaseEq"list"] \\ rveq
  \\ strip_tac
  \\ reverse IF_CASES_TAC
  >- (
    Cases_on`l0` \\ fs[LUPDATE_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION]
    \\ TRY pairarg_tac \\ fs[]
    \\ fs[extract_writes_def, extract_write_def]
    \\ first_x_assum irule
    \\ rveq
    \\ fs[] \\ rfs[]
    \\ metis_tac[])
  \\ Cases_on`l0` \\ fs[LUPDATE_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION]
  \\ TRY pairarg_tac \\ fs[]
  \\ PairCases_on`h`
  \\ fs[] \\ rveq
  \\ fs[fsFFITheory.write_def]
  \\ pairarg_tac \\ fs[]
  \\ rfs[fsFFITheory.fsupdate_def]
  \\ rveq \\ fs[ALIST_FUPDKEY_ALOOKUP, LDROP1_THM]
  \\ rfs[]
  \\ qmatch_asmsub_abbrev_tac`extract_fs_with_numchars fs'`
  \\ qmatch_asmsub_abbrev_tac`ALIST_FUPDKEY fnm (K new_content)`
  \\ fs[extract_writes_def, extract_write_def]
  \\ simp[TAKE_APPEND]
  \\ simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
  \\ simp[TAKE_LENGTH_TOO_LONG]
  \\ reverse(Cases_on`w82n l = fd`) \\ fs[]
  >- (
    first_x_assum irule
    \\ simp[]
    \\ IF_CASES_TAC
    >- (
      rveq \\ fs[]
      \\ first_x_assum drule
      \\ simp[Once OPTREL_def, EXISTS_PROD]
      \\ metis_tac[] )
    \\ `inFS_fname fs fnm`
    by (
      simp[fsFFIPropsTheory.inFS_fname_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ simp[MEM_MAP, EXISTS_PROD]
      \\ asm_exists_tac \\ rw[] )
    \\ Cases_on`fnm` \\ rfs[]
    \\ first_assum(qspec_then`w82n l`mp_tac)
    \\ impl_tac >- fs[]
    \\ qpat_x_assum`ALOOKUP fs.infds (w82n l) = _`mp_tac
    \\ simp_tac(srw_ss())[Once OPTREL_def, EXISTS_PROD]
    \\ ntac 2 strip_tac
    \\ last_assum drule
    \\ simp_tac(srw_ss())[fsFFIPropsTheory.inFS_fname_def]
    \\ strip_tac
    \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_keeps_iostreams)
    \\ disch_then drule
    \\ simp[Abbr`fs'`, ALIST_FUPDKEY_ALOOKUP]
    \\ qmatch_goalsub_abbrev_tac`_ + zz ≤ _`
    \\ strip_tac
    \\ reverse conj_tac
    >- (
      fs[fsFFIPropsTheory.inFS_fname_def]
      \\ conj_tac >- metis_tac[]
      \\ rw[]
      \\ fs[OPTREL_def, FORALL_PROD]
      \\ PURE_CASE_TAC \\ fs[]
      \\ PURE_CASE_TAC \\ fs[]
      \\ metis_tac[NOT_SOME_NONE,SOME_11] )
    \\ fs[fsFFIPropsTheory.inFS_fname_def])
  \\ fs[MAP_TAKE]
  \\ qmatch_goalsub_abbrev_tac`written ++ _`
  \\ rveq \\ fs[]
  \\ rveq \\ fs[]
  \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_keeps_iostreams)
  \\ disch_then drule
  \\ simp[Abbr`fs'`, ALIST_FUPDKEY_ALOOKUP]
  \\ simp[data_to_word_assignProofTheory.IMP]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`off + nw`
  \\ fs[Abbr`new_content`]
  \\ `LENGTH written = nw`
  by (
    simp[Abbr`written`, LENGTH_TAKE_EQ]
    \\ rw[] \\ fs[Abbr`nw`] )
  \\ fs[Abbr`off`, DROP_LENGTH_TOO_LONG]
  \\ qmatch_asmsub_abbrev_tac`¬inFS_fname fs' (File _)`
  \\ `nw ≤ LENGTH rest` by fs[Abbr`nw`]
  \\ rfs[] \\ fs[]
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac
  >- (
    rw[]
    \\ fs[CaseEq"option"]
    \\ CCONTR_TAC \\ fs[]
    \\ rveq
    \\ first_x_assum(qspec_then`fd'`mp_tac)
    \\ simp[OPTREL_def, FORALL_PROD]
    \\ metis_tac[] )
  \\ strip_tac
  \\ rveq \\ fs[]
  \\ first_x_assum irule
  \\ fs[fsFFIPropsTheory.inFS_fname_def]
  \\ simp[Abbr`fs'`]
  \\ conj_tac >- metis_tac[]
  \\ rw[] \\ PURE_CASE_TAC \\ fs[]
  \\ metis_tac[]);

val ag32_ffi_write_thm = Q.store_thm("ag32_ffi_write_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "write" ffi_names = SOME index) ∧
   (ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "write")))
   ⇒
   (ag32_ffi_write s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ drule INDEX_OF_IMP_EL \\ strip_tac
  \\ simp[ag32_ffi_write_def]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s'`
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_asmsub_abbrev_tac`if (s1.PC = _) then _ else _`
  \\ mp_tac ag32_ffi_write_set_id_thm
  \\ impl_tac
  >- ( simp[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_check_conf s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`]ag32_ffi_write_check_conf_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`n2w (_ - _) = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_load_noff s3`
  \\ qpat_x_assum`_ = s3`kall_tac
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ fs[fsFFITheory.ffi_write_def, CaseEq"list"]
  \\ rveq
  \\ qspec_then`s3`mp_tac(Q.GENL[`s`]ag32_ffi_write_load_noff_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s3`,APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`n2w(_ - _)= _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_check_lengths s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`ltll`,`off`,`n`,`cnd`]ag32_ffi_write_check_lengths_thm)
  \\ disch_then(qspecl_then[`LENGTH tll`,`w22n [off1; off0]`,`w22n [n1; n0]`,
                            `(LENGTH conf = 8) ∧ w82n conf < 3 ∧ 0 < w82n conf`]mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,Abbr`s3`,APPLY_UPDATE_THM]
    \\ simp[MarshallingTheory.w22n_def]
    \\ Cases_on`s.R 4w` \\ fs[ADD1,word_add_n2w]
    \\ Cases_on`off0` \\ Cases_on`off1` \\ fs[]
    \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[Abbr`s3`, APPLY_UPDATE_THM]
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`COND cnd`
  \\ qmatch_asmsub_abbrev_tac`s' = if cnd' then _ else _`
  \\ `cnd' = cnd`
  by (
    simp[Abbr`cnd'`,Abbr`s1`]
    \\ Cases_on`cnd` \\ simp[]
    \\ EVAL_TAC \\ simp[] )
  \\ qpat_x_assum`Abbrev(cnd' = _)`kall_tac
  \\ rveq
  \\ reverse(Cases_on`cnd`) \\ fs[]
  >- (
    qpat_x_assum`Abbrev(s' = _)`mp_tac
    \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ strip_tac
    \\ simp[Abbr`s'`]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac`OPTION_CHOICE o1`
    \\ `o1 = NONE`
    by (
      simp[Abbr`o1`]
      \\ simp[EXISTS_PROD]
      \\ simp[fsFFITheory.write_def, EXISTS_PROD]
      \\ fs[ag32_fs_ok_def]
      \\ Cases_on`LENGTH conf = 8` \\ fs[]
      \\ last_x_assum(qspec_then`w82n conf`mp_tac)
      \\ Cases_on`w82n conf < 3` \\ fs[]
      \\ simp[IS_SOME_EXISTS]
      \\ strip_tac \\ simp[]
      \\ PairCases_on`x` \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ Cases_on`ALOOKUP fs.files x0` \\ fs[]
      \\ fs[markerTheory.Abbrev_def]
      \\ fs[fsFFIPropsTheory.STD_streams_def]
      \\ last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
      \\ simp[] \\ rfs[])
    \\ fs[] \\ rveq
    \\ simp[LUPDATE_def]
    \\ qmatch_goalsub_abbrev_tac`A ∧ (B ∧ A)`
    \\ `A ∧ B` suffices_by rw[]
    \\ qunabbrev_tac`B`
    \\ reverse conj_tac
    >- (
      simp[FUN_EQ_THM, APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ simp[] )
    \\ simp[Abbr`A`]
    \\ simp[ag32_ffi_mem_update_def]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ Cases
    \\ IF_CASES_TAC \\ fs[]
    \\ IF_CASES_TAC
    >- simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      match_mp_tac EQ_SYM
      \\ fs[asmSemTheory.bytes_in_memory_def,
            asm_write_bytearray_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ rveq
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`_ = n2w n`(mp_tac o SYM)
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def,word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`_ = n2w n`(mp_tac o SYM)
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`_ = n2w n`(mp_tac o SYM)
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ conj_tac
      >- ( Cases_on`s.R 3w` \\ fs[ADD1, memory_size_def, word_add_n2w] )
      \\ Cases_on`s.R 3w`
      \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
      \\ fs[EVAL``code_start_offset _``, FFI_codes_def]
      \\ fs[LEFT_ADD_DISTRIB]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ fs[word_add_n2w] \\ rfs[]
      \\ rveq \\ fs[] \\ rfs[]
      \\ qpat_x_assum`n2w n' ∈ _`mp_tac
      \\ simp[word_add_n2w, Abbr`md`]
      \\ simp[ag32_prog_addresses_def]
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB])
    \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ fs[asmSemTheory.bytes_in_memory_def] \\ rveq
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ match_mp_tac EQ_SYM
    \\ Cases_on`n2w n <+ s.R 3w + 4w ∨ s.R 3w + 4w + n2w (LENGTH tll) <=+ n2w n`
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] )
    \\ fs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
    \\ Cases_on`s.R 3w`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] \\ rfs[]
    \\ qpat_x_assum`_ ≤ n`mp_tac
    \\ rw[LESS_EQ_EXISTS] \\ fs[]
    \\ drule asmPropsTheory.bytes_in_memory_EL
    \\ disch_then drule
    \\ rw[word_add_n2w]
    \\ qmatch_goalsub_rename_tac`n2w (a + (p + 4))`
    \\ `n2w(a + (p + 4)) = n2w(a+4) + n2w p:word32` by simp[word_add_n2w]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule asm_write_bytearray_EL
    \\ simp[] )
  \\ pop_assum mp_tac \\ simp[markerTheory.Abbrev_def] \\ strip_tac
  \\ qspec_then`s1`mp_tac(Q.GEN`s`ag32_ffi_write_write_header_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[memory_size_def, word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ qhdtm_x_assum`ag32_ffi_write_write_header`kall_tac
  \\ qmatch_asmsub_abbrev_tac`1w =+ n2w n`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`k`]ag32_ffi_write_num_written_thm)
  \\ simp[]
  \\ impl_tac
  >- (
    simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      simp[Abbr`n`, MarshallingTheory.w22n_def]
      \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[] )
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ rveq
    \\ DEP_REWRITE_TAC[asm_write_bytearray_append]
    \\ simp[EVAL``output_offset``]
    \\ fs[memory_size_def, word_add_n2w]
    \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ EVAL_TAC \\ fs[]
    \\ qpat_x_assum`n2w n' ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[FFI_codes_def]
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ disch_then assume_tac
    \\ conj_tac
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
    \\ conj_tac
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
    \\ conj_tac
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ simp[word_add_n2w]
    \\ match_mp_tac EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[word_add_n2w, APPLY_UPDATE_THM]
    \\ simp[word_ls_n2w, word_lo_n2w])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s3`
  \\ fs[]
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qhdtm_x_assum`ag32_ffi_write_num_written`kall_tac
  \\ qspec_then`s3`mp_tac(ag32_ffi_copy_thm)
  \\ qmatch_asmsub_abbrev_tac`LENGTH tll - off`
  \\ disch_then(qspec_then`TAKE (MIN n output_buffer_size) (DROP off tll)`mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[Abbr`s3`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ EVAL_TAC
      \\ fs[memory_size_def, word_add_n2w]
      \\ simp[MIN_DEF]
      \\ simp[IN_DISJOINT]
      \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ simp[Abbr`md`]
      \\ EVAL_TAC \\ fs[]
      \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ `tll = TAKE off tll ++ DROP off tll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL asmPropsTheory.bytes_in_memory_APPEND))))
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`TAKE kk ll`
    \\ `ll = TAKE kk ll ++ DROP kk ll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL asmPropsTheory.bytes_in_memory_APPEND))))
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gen_tac \\ strip_tac
    \\ simp[asm_write_bytearray_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ simp[word_add_n2w]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ Cases_on`s.R 3w`
    \\ simp[word_add_n2w, MarshallingTheory.n2w2_def]
    \\ simp[word_ls_n2w, word_lo_n2w]
    \\ fs[]
    \\ rfs[Abbr`ll`]
    \\ `kk ≤ n` by simp[Abbr`kk`]
    \\ fs[LENGTH_TAKE_EQ]
    \\ simp[APPLY_UPDATE_THM]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ EVAL_TAC
    \\ simp[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ `kk ≤ LENGTH tll - off` by fs[] \\ fs[]
    \\ fs[FFI_codes_def, EVAL``code_start_offset _``] \\ rfs[]
    \\ `kk ≤ output_buffer_size` by simp[Abbr`kk`]
    \\ fs[EVAL``output_buffer_size``]
    \\ qpat_x_assum`n2w n'' ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ simp[word_ls_n2w, word_lo_n2w, word_add_n2w])
  \\ strip_tac
  \\ qunabbrev_tac`s'`
  \\ fs[]
  \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ A`
  \\ `B ∧ A` suffices_by rw[]
  \\ simp[Abbr`B`, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ EVAL_TAC \\ simp[]
  \\ qhdtm_x_assum`ag32_ffi_copy`kall_tac
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def, ADD1]
  \\ qmatch_goalsub_abbrev_tac`THE (bs:word8 list option)`
  \\ qmatch_asmsub_abbrev_tac`bytes_in_memory _ bs'`
  \\ `bs = SOME bs'`
  by (
    simp[Abbr`bs`]
    \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ fs[Abbr`bs'`]
    \\ gen_tac \\ strip_tac
    \\ drule asmPropsTheory.bytes_in_memory_EL
    \\ simp[]
    \\ drule asmPropsTheory.bytes_in_memory_in_domain
    \\ simp[] )
  \\ simp[Abbr`bs`, Abbr`bs'`]
  \\ fs[fsFFITheory.write_def]
  \\ `∃x. ALOOKUP fs.infds (w82n conf) = SOME x` by metis_tac[IS_SOME_EXISTS, ag32_fs_ok_def]
  \\ fs[] \\ PairCases_on`x` \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ first_x_assum drule
  \\ simp[IS_SOME_EXISTS]
  \\ strip_tac \\ fs[]
  \\ rveq \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`THE (bs:word8 list option)`
  \\ `bs = SOME conf`
  by (
    simp[Abbr`bs`]
    \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ fs[]
    \\ gen_tac \\ strip_tac
    \\ conj_tac
    >- (
      once_rewrite_tac[WORD_ADD_COMM]
      \\ irule asmPropsTheory.bytes_in_memory_in_domain
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[] )
    \\ once_rewrite_tac[WORD_ADD_COMM]
    \\ irule asmPropsTheory.bytes_in_memory_EL
    \\ simp[]
    \\ asm_exists_tac
    \\ simp[] )
  \\ simp[Abbr`bs`]
  \\ qmatch_goalsub_abbrev_tac`lhs = _`
  \\ DEP_ONCE_REWRITE_TAC[asm_write_bytearray_append]
  \\ simp[Abbr`lhs`]
  \\ conj_tac
  >- (
    EVAL_TAC
    \\ rw[MIN_DEF] )
  \\ qmatch_asmsub_rename_tac`mode = WriteMode`
  \\ Cases_on`mode`
  >- (
    fs[fsFFIPropsTheory.STD_streams_def]
    \\ qpat_x_assum`_ < 3`mp_tac
    \\ simp[NUMERAL_LESS_THM]
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ rw[] )
  \\ fs[]
  \\ rveq \\ fs[]
  \\ rewrite_tac[GSYM WORD_ADD_ASSOC, word_add_n2w]
  \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ Cases
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (n2w _) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`n2w n' + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] )
  \\ simp[MarshallingTheory.n2w2_def]
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[])
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[])
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC
    >- (
      fs[word_add_n2w, memory_size_def]
      \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
      \\ drule read_bytearray_IMP_mem_SOME
      \\ simp[IS_SOME_EXISTS]
      \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
      \\ simp[IN_all_words_add]
      \\ simp[Abbr`md`]
      \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB]
      \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[FFI_codes_def] \\ rfs[]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ rfs[])
    \\ irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ fs[word_add_n2w, memory_size_def]
    \\ Cases_on`s.R 3w`
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rfs[]
    \\ qpat_x_assum`read_bytearray (n2w _) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ impl_tac
    >- (
      asm_simp_tac bool_ss []
      \\ irule IN_all_words_add
      \\ simp[] )
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[] )
  \\ IF_CASES_TAC
  >- (
    `LENGTH tll + 4 = SUC(SUC(SUC(SUC(LENGTH tll))))` by simp[ADD1]
    \\ full_simp_tac std_ss [read_bytearray_def]
    \\ fs[CaseEq"bool",CaseEq"option"])
  \\ irule EQ_SYM
  \\ DEP_REWRITE_TAC[asm_write_bytearray_id]
  \\ simp[APPLY_UPDATE_THM]
  \\ gen_tac \\ strip_tac
  \\ IF_CASES_TAC
  >- (
    fs[word_add_n2w, memory_size_def]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[]
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rfs[])
  \\ drule asmPropsTheory.bytes_in_memory_EL
  \\ disch_then(qspec_then`j + 4`mp_tac)
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]);

val ag32_ffi_read_thm = Q.store_thm("ag32_ffi_read_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "read" ffi_names = SOME index) ∧
   (ffi_read conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧ ag32_stdin_implemented fs s.MEM ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "read")))
   ⇒
   (ag32_ffi_read s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ drule INDEX_OF_IMP_EL \\ strip_tac
  \\ simp[ag32_ffi_read_def]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s'`
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_asmsub_abbrev_tac`if (s1.PC = _) then _ else _`
  \\ fs[ag32_ffi_read_set_id_thm]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_read_check_conf s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`]ag32_ffi_read_check_conf_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`n2w (_ - _) = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_read_load_lengths s3`
  \\ qpat_x_assum`_ = s3`kall_tac
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ fs[fsFFITheory.ffi_read_def, CaseEq"list"]
  \\ rveq
  \\ fs[ag32_stdin_implemented_def]
  \\ qspecl_then[`s3`,`LENGTH inp`]mp_tac(Q.GENL[`s`,`len`]ag32_ffi_read_load_lengths_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s3`,APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      fs[get_mem_word_def, APPLY_UPDATE_THM]
      \\ fs[EVAL``ffi_code_start_offset``,EVAL``stdin_offset``] )
    \\ fs[asmSemTheory.bytes_in_memory_def, APPLY_UPDATE_THM]
    \\ rpt(qpat_x_assum`_ ∈ md`mp_tac)
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w`
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def, word_add_n2w] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_read_check_length s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`ltll`,`n`,`cnd`]ag32_ffi_read_check_length_thm)
  \\ disch_then(qspecl_then[`LENGTH tll`,`w22n [n1; n0]`,
                            `(LENGTH conf = 8) ∧ (w82n conf = 0)`]mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,Abbr`s3`,APPLY_UPDATE_THM]
    \\ simp[MarshallingTheory.w22n_def]
    \\ Cases_on`s.R 4w` \\ fs[ADD1,word_add_n2w]
    \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[Abbr`s3`, APPLY_UPDATE_THM]
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`COND cnd`
  \\ qmatch_asmsub_abbrev_tac`s' = if cnd' then _ else _`
  \\ `cnd' = cnd`
  by (
    simp[Abbr`cnd'`,Abbr`s1`]
    \\ Cases_on`cnd` \\ simp[]
    \\ EVAL_TAC \\ simp[] )
  \\ qpat_x_assum`Abbrev(cnd' = _)`kall_tac
  \\ rveq
  \\ reverse(Cases_on`cnd`) \\ fs[]
  >- (
    qpat_x_assum`Abbrev(s' = _)`mp_tac
    \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ strip_tac
    \\ simp[Abbr`s'`]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac`OPTION_CHOICE o1`
    \\ `o1 = NONE`
    by (
      simp[Abbr`o1`]
      \\ simp[EXISTS_PROD]
      \\ simp[fsFFITheory.read_def, EXISTS_PROD]
      \\ fs[ag32_fs_ok_def]
      \\ Cases_on`LENGTH conf = 8` \\ fs[]
      \\ last_x_assum(qspec_then`w82n conf`mp_tac)
      \\ Cases_on`w82n conf < 3` \\ fs[]
      \\ simp[IS_SOME_EXISTS]
      \\ strip_tac \\ simp[]
      \\ PairCases_on`x` \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ fs[markerTheory.Abbrev_def]
      \\ qpat_x_assum`w82n _ < _`mp_tac
      \\ simp[NUMERAL_LESS_THM]
      \\ fs[fsFFIPropsTheory.STD_streams_def]
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
      \\ rw[])
    \\ fs[] \\ rveq
    \\ simp[LUPDATE_def]
    \\ qmatch_goalsub_abbrev_tac`A ∧ (B ∧ A)`
    \\ `A ∧ B` suffices_by rw[]
    \\ qunabbrev_tac`B`
    \\ reverse conj_tac
    >- (
      simp[FUN_EQ_THM, APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ simp[] )
    \\ simp[Abbr`A`]
    \\ simp[ag32_ffi_mem_update_def]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ Cases
    \\ IF_CASES_TAC
    >- simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      match_mp_tac EQ_SYM
      \\ fs[asmSemTheory.bytes_in_memory_def,
            asm_write_bytearray_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ rveq
      \\ fs[EVAL``ffi_code_start_offset``] \\ rfs[] \\ rveq
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def,word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB])
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB])
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB])
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ conj_tac
      >- ( Cases_on`s.R 3w` \\ fs[ADD1, memory_size_def, word_add_n2w] )
      \\ Cases_on`s.R 3w`
      \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
      \\ fs[EVAL``code_start_offset _``, FFI_codes_def]
      \\ fs[LEFT_ADD_DISTRIB]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ fs[word_add_n2w] \\ rfs[]
      \\ rveq \\ fs[] \\ rfs[]
      \\ qpat_x_assum`n2w n' ∈ _`mp_tac
      \\ simp[word_add_n2w, Abbr`md`]
      \\ simp[ag32_prog_addresses_def]
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB])
    \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ fs[asmSemTheory.bytes_in_memory_def] \\ rveq
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ match_mp_tac EQ_SYM
    \\ Cases_on`n2w n <+ s.R 3w + 4w ∨ s.R 3w + 4w + n2w (LENGTH tll) <=+ n2w n`
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[EVAL``ffi_code_start_offset``] \\ rfs[]
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] )
    \\ fs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
    \\ fs[EVAL``ffi_code_start_offset``] \\ rfs[]
    \\ Cases_on`s.R 3w`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] \\ rfs[]
    \\ qpat_x_assum`_ ≤ n`mp_tac
    \\ rw[LESS_EQ_EXISTS] \\ fs[]
    \\ qpat_x_assum`bytes_in_memory (n2w (_ + 4)) _ _ _`assume_tac
    \\ drule asmPropsTheory.bytes_in_memory_EL
    \\ disch_then drule
    \\ rw[word_add_n2w]
    \\ qmatch_goalsub_rename_tac`n2w (a + (p + 4))`
    \\ `n2w(a + (p + 4)) = n2w(a+4) + n2w p:word32` by simp[word_add_n2w]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule asm_write_bytearray_EL
    \\ simp[] )
  \\ pop_assum mp_tac \\ simp[markerTheory.Abbrev_def] \\ strip_tac
  \\ qspecl_then[`s1`,`w22n[n1;n0]`,`LENGTH inp - off`]mp_tac
       (Q.GENL[`s`,`n`,`lcmo`,`k`]ag32_ffi_read_num_written_thm)
  \\ simp[]
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      simp[MarshallingTheory.w22n_def]
      \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[]
      \\ fs[stdin_size_def])
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ rveq
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rpt(qpat_x_assum`_ ∈ md`mp_tac)
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[FFI_codes_def]
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[word_ls_n2w, word_lo_n2w, memory_size_def]
    \\ rpt (disch_then assume_tac)
    \\ qpat_x_assum`bytes_in_memory (n2w (_ + 4)) _ _ _`mp_tac
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ simp[word_add_n2w])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ qhdtm_x_assum`ag32_ffi_read_num_written`kall_tac
  \\ qmatch_asmsub_abbrev_tac`off + k`
  \\ qspecl_then[`all_words (n2w (stdin_offset + 8)) (LENGTH inp)`,`s2`,`MAP (n2w o ORD) (TAKE k (DROP off inp))`]
      mp_tac(Q.GEN`md`ag32_ffi_copy_thm)
  \\ impl_tac >- (
    simp[Abbr`s2`, APPLY_UPDATE_THM, Abbr`s'`]
    \\ `MAP (n2w o ORD) inp : word8 list =
        MAP (n2w o ORD) (TAKE off inp) ++
        MAP (n2w o ORD) (DROP off inp)`
    by (
      rewrite_tac[GSYM MAP_APPEND]
      \\ AP_TERM_TAC
      \\ MATCH_ACCEPT_TAC (GSYM TAKE_DROP) )
    \\ pop_assum SUBST_ALL_TAC
    \\ fs[asmPropsTheory.bytes_in_memory_APPEND]
    \\ rfs[LENGTH_TAKE]
    \\ `MAP (n2w o ORD) (DROP off inp) : word8 list =
        MAP (n2w o ORD) (TAKE k (DROP off inp)) ++
        MAP (n2w o ORD) (DROP k (DROP off inp))`
    by (
      rewrite_tac[GSYM MAP_APPEND]
      \\ AP_TERM_TAC
      \\ MATCH_ACCEPT_TAC (GSYM TAKE_DROP) )
    \\ pop_assum SUBST_ALL_TAC
    \\ fs[asmPropsTheory.bytes_in_memory_APPEND]
    \\ `k ≤ LENGTH inp - off` by simp[Abbr`k`, MIN_DEF]
    \\ fs[LENGTH_TAKE]
    \\ conj_tac
    >- (
      irule asmPropsTheory.bytes_in_memory_change_mem
      \\ fs[word_add_n2w]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ rw[]
      \\ DEP_REWRITE_TAC[set_mem_word_neq]
      \\ conj_tac
      >- (EVAL_TAC \\ simp[] \\ fs[EVAL``stdin_size``])
      \\ match_mp_tac EQ_SYM
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[EVAL``stdin_size``, EVAL``ffi_code_start_offset``, EVAL``stdin_offset``]
      \\ fs[asmSemTheory.bytes_in_memory_def]
      \\ qpat_x_assum`s.R 3w ∈ md`mp_tac
      \\ simp[Abbr`md`] \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def])
    \\ fs[EVAL``stdin_size``]
    \\ fs[EVAL``stdin_offset``]
    \\ `k ≤ w22n [n1; n0]` by simp[Abbr`k`, MIN_DEF]
    \\ fs[ADD1]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ simp[IN_DISJOINT]
    \\ Cases
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`n2w n ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[]
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def, LEFT_ADD_DISTRIB, EVAL``code_start_offset _``,
          memory_size_def, IN_all_words, word_add_n2w]
    \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[] \\ rfs[] )
  \\ strip_tac
  \\ qunabbrev_tac`s'`
  \\ fs[]
  \\ qhdtm_x_assum`ag32_ffi_copy`kall_tac
  \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ A`
  \\ `B ∧ A` suffices_by rw[]
  \\ simp[Abbr`B`, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ EVAL_TAC \\ simp[]
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def, ADD1]
  \\ reverse(fs[OPTION_CHOICE_EQUALS_OPTION])
  \\ TRY pairarg_tac \\ fs[] \\ rveq \\ fs[LUPDATE_def]
  >- ( fs[fsFFITheory.read_def, ag32_fs_ok_def] )
  \\ fs[fsFFITheory.read_def]
  \\ `SUC strm = output_buffer_size + 1`
  by ( fs[ag32_fs_ok_def] )
  \\ fs[]
  \\ `∃l1 l0. n2w2 (LENGTH l) = [l1; l0]` by simp[MarshallingTheory.n2w2_def]
  \\ simp[]
  \\ `w22n [l1; l0] = LENGTH l` by (
    pop_assum(SUBST1_TAC o SYM)
    \\ irule MarshallingTheory.w22n_n2w2
    \\ rveq \\ simp[LENGTH_TAKE_EQ]
    \\ simp[Abbr`k`]
    \\ EVAL_TAC )
  \\ simp[]
  \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
  \\ conj_tac
  >- (
    fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w` \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, ADD1, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[memory_size_def, EVAL``code_start_offset _``]
    \\ `k ≤ output_buffer_size + 1` by simp[Abbr`k`]
    \\ pop_assum mp_tac \\ EVAL_TAC
    \\ rveq \\ simp[LENGTH_TAKE_EQ] )
  \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
  \\ conj_tac >- EVAL_TAC
  \\ simp[word_add_n2w]
  \\ `LENGTH l = k`
  by ( rveq \\ simp[LENGTH_TAKE_EQ] \\ simp[Abbr`k`] )
  \\ fs[]
  \\ cheat (* order of memory writes *));
(* maybe some of this is useful:
  \\ qmatch_goalsub_abbrev_tac`lhs = _`
  \\ DEP_ONCE_REWRITE_TAC[asm_write_bytearray_append]
  \\ simp[Abbr`lhs`]
  \\ conj_tac
  >- (
    EVAL_TAC
    \\ rw[MIN_DEF] )
  \\ rewrite_tac[GSYM WORD_ADD_ASSOC, word_add_n2w]
  \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ Cases
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (n2w _) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`n2w n' + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] )
  \\ simp[MarshallingTheory.n2w2_def]
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[])
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[])
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC
    >- (
      fs[word_add_n2w, memory_size_def]
      \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
      \\ drule read_bytearray_IMP_mem_SOME
      \\ simp[IS_SOME_EXISTS]
      \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
      \\ simp[IN_all_words_add]
      \\ simp[Abbr`md`]
      \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB]
      \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[FFI_codes_def] \\ rfs[]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ rfs[])
    \\ irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ fs[word_add_n2w, memory_size_def]
    \\ Cases_on`s.R 3w`
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rfs[]
    \\ qpat_x_assum`read_bytearray (n2w _) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ impl_tac
    >- (
      asm_simp_tac bool_ss []
      \\ irule IN_all_words_add
      \\ simp[] )
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[] )
  \\ IF_CASES_TAC
  >- (
    `LENGTH tll + 4 = SUC(SUC(SUC(SUC(LENGTH tll))))` by simp[ADD1]
    \\ full_simp_tac std_ss [read_bytearray_def]
    \\ fs[CaseEq"bool",CaseEq"option"])
  \\ irule EQ_SYM
  \\ DEP_REWRITE_TAC[asm_write_bytearray_id]
  \\ simp[APPLY_UPDATE_THM]
  \\ gen_tac \\ strip_tac
  \\ IF_CASES_TAC
  >- (
    fs[word_add_n2w, memory_size_def]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`s.R 3w + n2w 0`mp_tac)
    \\ simp[IN_all_words_add]
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[]
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rfs[])
  \\ drule asmPropsTheory.bytes_in_memory_EL
  \\ disch_then(qspec_then`j + 4`mp_tac)
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]);
*)

val ag32_ffi_get_arg_count_thm = Q.store_thm("ag32_ffi_get_arg_count_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "get_arg_count" ffi_names = SOME index) ∧
   (ffi_get_arg_count conf bytes (cl:mlstring list) = SOME (FFIreturn new_bytes cl')) ∧
   ag32_cline_implemented cl s.MEM ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg_count")))
   ⇒
   (ag32_ffi_get_arg_count s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ rw[ag32_ffi_get_arg_count_def]
  \\ fs[ag32_cline_implemented_def]
  \\ drule ag32_ffi_get_arg_count_main_thm
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ _`
  \\ `EL index ffi_names = "get_arg_count"`
  by ( drule INDEX_OF_IMP_EL \\ rw[] )
  \\ `B` by ( simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ simp[]
  \\ qunabbrev_tac`B`
  \\ pop_assum kall_tac
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def]
  \\ fs[clFFITheory.ffi_get_arg_count_def]);

val ag32_ffi_open_in_thm = Q.store_thm("ag32_ffi_open_in_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "open_in" ffi_names = SOME index) ∧
   (ffi_open_in conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "open_in")))
   ⇒
   (ag32_ffi_open_in s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ rw[ag32_ffi_open_in_def,ag32_ffi_fail_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ C ∧ _`
  \\ `EL index ffi_names = "open_in"` by ( drule INDEX_OF_IMP_EL \\ rw[] )
  \\ `B` by (
    simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ `C` by (
    simp[Abbr`C`]  \\EVAL_TAC
    \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM])
  \\ simp[Abbr`A`,ag32_ffi_mem_update_def,FUN_EQ_THM]
  \\ rw[]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ match_mp_tac EQ_SYM
  \\ Cases_on`bytes`>>fs[]
  >-
    (* TODO: fs doesn't seem to enforce that bytes ≠ []
      this case split is temporary
    *)
    cheat
  \\ `new_bytes = 1w :: t` by (
    fs[fsFFITheory.ffi_open_in_def,OPTION_CHOICE_EQUALS_OPTION]
    >-
      (pairarg_tac>>fs[fsFFITheory.openFile_def]>>
      fs[ag32_fs_ok_def]>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>
      fs[])
    >>
    rw[]>>fs[LUPDATE_def])
  \\ simp[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ IF_CASES_TAC >> fs[]
  \\ IF_CASES_TAC
  >-
    (match_mp_tac asm_write_bytearray_unchanged >>
    fs[APPLY_UPDATE_THM]>>
    (* use mem domain *)
    cheat)
  >>
    (* this one should be easy, maybe ... *)
    fs[asmSemTheory.bytes_in_memory_def]>>
    drule asmPropsTheory.bytes_in_memory_change_mem>>
    qmatch_goalsub_abbrev_tac`_ _ t mm x`>>
    disch_then(qspec_then`mm` mp_tac)>>
    impl_tac
    >-
      (rw[Abbr`mm`,APPLY_UPDATE_THM]>>
      rfs[]>>
      (* use mem domain *)
      cheat)
    >>
    strip_tac>>
    drule bytes_in_memory_IMP_asm_write_bytearray>>
    fs[Abbr`mm`,APPLY_UPDATE_THM]);

val ag32_ffi_open_out_thm = Q.store_thm("ag32_ffi_open_out_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "open_out" ffi_names = SOME index) ∧
   (ffi_open_out conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "open_out")))
   ⇒
   (ag32_ffi_open_out s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ rw[ag32_ffi_open_out_def,ag32_ffi_fail_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ C ∧ _`
  \\ `EL index ffi_names = "open_out"` by ( drule INDEX_OF_IMP_EL \\ rw[] )
  \\ `B` by (
    simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ `C` by (
    simp[Abbr`C`]  \\EVAL_TAC
    \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM])
  \\ simp[Abbr`A`,ag32_ffi_mem_update_def,FUN_EQ_THM]
  \\ rw[]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ match_mp_tac EQ_SYM
  \\ Cases_on`bytes`>>fs[]
  >-
    (* TODO: fs doesn't seem to enforce that bytes ≠ []
      this case split is temporary
    *)
    cheat
  \\ `new_bytes = 1w :: t` by (
    fs[fsFFITheory.ffi_open_out_def,OPTION_CHOICE_EQUALS_OPTION]
    >-
      (pairarg_tac>>fs[fsFFITheory.openFile_truncate_def]>>
      fs[ag32_fs_ok_def]>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>
      fs[])
    >>
    (* TODO: open_out returns 255 instead of 1??? *)
    rw[]>>fs[LUPDATE_def]>>cheat)
  \\ simp[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ IF_CASES_TAC >> fs[]
  \\ IF_CASES_TAC
  >-
    (match_mp_tac asm_write_bytearray_unchanged >>
    fs[APPLY_UPDATE_THM]>>
    (* use mem domain *)
    cheat)
  >>
    (* this one should be easy, maybe ... *)
    fs[asmSemTheory.bytes_in_memory_def]>>
    drule asmPropsTheory.bytes_in_memory_change_mem>>
    qmatch_goalsub_abbrev_tac`_ _ t mm x`>>
    disch_then(qspec_then`mm` mp_tac)>>
    impl_tac
    >-
      (rw[Abbr`mm`,APPLY_UPDATE_THM]>>
      rfs[]>>
      (* use mem domain *)
      cheat)
    >>
    strip_tac>>
    drule bytes_in_memory_IMP_asm_write_bytearray>>
    fs[Abbr`mm`,APPLY_UPDATE_THM]);

val ag32_ffi_close_thm = Q.store_thm("ag32_ffi_close_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "close" ffi_names = SOME index) ∧
   (ffi_close conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "close")))
   ⇒
   (ag32_ffi_close s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ rw[ag32_ffi_close_def,ag32_ffi_fail_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ C ∧ _`
  \\ `EL index ffi_names = "close"` by ( drule INDEX_OF_IMP_EL \\ rw[] )
  \\ `B` by (
    simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ `C` by (
    simp[Abbr`C`]  \\EVAL_TAC
    \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM])
  \\ simp[Abbr`A`,ag32_ffi_mem_update_def,FUN_EQ_THM]
  \\ rw[]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ match_mp_tac EQ_SYM
  \\ Cases_on`bytes`>>fs[]
  >-
    (* TODO: fs doesn't seem to enforce that bytes ≠ []
      this case split is temporary
    *)
    cheat
  \\ `new_bytes = 1w :: t` by (
    fs[fsFFITheory.ffi_close_def,OPTION_CHOICE_EQUALS_OPTION]
    >-
      (pairarg_tac>>fs[fsFFITheory.closeFD_def]>>
      (* can STDOUT, STDIN and STDERR be closed? *)
      cheat)
    >>
    rw[]>>fs[LUPDATE_def])
  \\ simp[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ IF_CASES_TAC >> fs[]
  \\ IF_CASES_TAC
  >-
    (match_mp_tac asm_write_bytearray_unchanged >>
    fs[APPLY_UPDATE_THM]>>
    (* use mem domain *)
    cheat)
  >>
    (* this one should be easy, maybe ... *)
    fs[asmSemTheory.bytes_in_memory_def]>>
    drule asmPropsTheory.bytes_in_memory_change_mem>>
    qmatch_goalsub_abbrev_tac`_ _ t mm x`>>
    disch_then(qspec_then`mm` mp_tac)>>
    impl_tac
    >-
      (rw[Abbr`mm`,APPLY_UPDATE_THM]>>
      rfs[]>>
      (* use mem domain *)
      cheat)
    >>
    strip_tac>>
    drule bytes_in_memory_IMP_asm_write_bytearray>>
    fs[Abbr`mm`,APPLY_UPDATE_THM]);

val ag32_fs_ok_stdin_fs = Q.store_thm("ag32_fs_ok_stdin_fs",
  `ag32_fs_ok (stdin_fs inp)`,
  rw[ag32_fs_ok_def, STD_streams_stdin_fs]
  \\ rw[stdin_fs_def]
  \\ fs[stdin_fs_def, CaseEq"bool"]);

val ag32_ffi_rel_write_mem_update = Q.store_thm("ag32_ffi_rel_write_mem_update",
  `(ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   (m ((n2w (ffi_code_start_offset - 1)):word32) = n2w (THE (ALOOKUP FFI_codes "write"))) ∧
    ag32_fs_ok fs
   ⇒
   (get_ag32_io_event
     (ag32_ffi_mem_update "write" conf bytes new_bytes m)
    = get_output_io_event (IO_event "write" conf (ZIP (bytes,new_bytes))))`,
  rw[]
  \\ imp_res_tac fsFFIPropsTheory.ffi_write_length
  \\ fs[fsFFITheory.ffi_write_def]
  \\ fs[CaseEq"list"]
  \\ rveq
  \\ simp[get_output_io_event_def, MAP_ZIP]
  \\ rewrite_tac[GSYM EL] \\ simp[EL_ZIP]
  \\ reverse IF_CASES_TAC
  >- (
    simp[ag32_ffi_mem_update_def]
    \\ simp[get_ag32_io_event_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (pop_assum mp_tac \\ EVAL_TAC)
    \\ simp[] )
  \\ simp[ag32_ffi_mem_update_def]
  \\ simp[get_ag32_io_event_def]
  \\ reverse(Cases_on`LENGTH conf = 8` \\ fs[])
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ reverse(Cases_on`w22n [off1; off0] ≤ LENGTH tll` \\ fs[])
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ fs[fsFFITheory.write_def]
  \\ Cases_on`ALOOKUP fs.infds (w82n conf)` \\ fs[]
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ pairarg_tac \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ `∃cnt. (ALOOKUP fs.files fnm = SOME cnt)` by metis_tac[]
  \\ reverse(fs[OPTION_CHOICE_EQUALS_OPTION])
  >- ( rveq \\ fs[LUPDATE_def] )
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ rveq \\ fs[]
  \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
  \\ `HD conf = 0w`
  by (
    fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] )
  \\ conj_tac
  >- (
    irule asm_write_bytearray_unchanged
    \\ simp[]
    \\ fs[EVAL``output_offset``, EVAL``ffi_code_start_offset``]
    \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ simp[EVAL``output_buffer_size``]
    \\ simp[MIN_DEF] )
  \\ reverse IF_CASES_TAC
  >- (
    fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[]
    \\ rveq
    \\ fs[asm_write_bytearray_def, APPLY_UPDATE_THM] )
  \\ qmatch_goalsub_abbrev_tac`w22n [n1'; n0']`
  \\ `n1' = n1`
  by (
    simp[Abbr`n1'`]
    \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray _ ls`
    \\ `n1 = EL 10 ls` by ( simp[Abbr`ls`, EL_APPEND_EQN] )
    \\ pop_assum SUBST1_TAC
    \\ simp[GSYM word_add_n2w]
    \\ irule asm_write_bytearray_EL
    \\ simp[Abbr`ls`]
    \\ simp[MIN_DEF, output_buffer_size_def] )
  \\ qpat_x_assum`Abbrev(n1' = _)`kall_tac
  \\ `n0' = n0`
  by (
    simp[Abbr`n0'`]
    \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray _ ls`
    \\ `n0 = EL 11 ls` by ( simp[Abbr`ls`, EL_APPEND_EQN] )
    \\ pop_assum SUBST1_TAC
    \\ simp[GSYM word_add_n2w]
    \\ irule asm_write_bytearray_EL
    \\ simp[Abbr`ls`]
    \\ simp[MIN_DEF, output_buffer_size_def] )
  \\ qpat_x_assum`Abbrev(n0' = _)`kall_tac
  \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ `n2w i + n2w output_offset :word32= (n2w output_offset) + n2w i` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[asm_write_bytearray_EL]
  \\ simp[]
  \\ simp[MIN_DEF, output_buffer_size_def]);

val ag32_fs_ok_ffi_write = Q.store_thm("ag32_fs_ok_ffi_write",
  `(ffi_write conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'`,
  rw[fsFFITheory.ffi_write_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ `STD_streams fs'`
  by (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ irule fsFFIPropsTheory.STD_streams_fsupdate
    \\ simp[]
    \\ first_x_assum drule
    \\ simp[] )
  \\ conj_tac
  >- (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[]
    \\ rw[fsFFITheory.fsupdate_def, LDROP1_THM] )
  \\ conj_tac
  >- (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[]
    \\ rw[fsFFITheory.fsupdate_def, ALIST_FUPDKEY_ALOOKUP]
    \\ PURE_TOP_CASE_TAC \\ simp[] \\ rw[]
    \\ metis_tac[NOT_SOME_NONE, IS_SOME_EXISTS] )
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, fsFFITheory.write_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[fsFFITheory.fsupdate_def, ALIST_FUPDKEY_ALOOKUP, LDROP1_THM]
  \\ rw[]
  \\ fs[CaseEq"option"]
  \\ PairCases_on`v` \\ fs[]
  \\ fs[CaseEq"bool",PULL_EXISTS] \\ rveq
  >- (
    first_x_assum drule
    \\ rw[] \\ rw[]
    \\ Cases_on`fnm = fnm'` \\ fs[]
    \\ strip_tac \\ fs[] )
  \\ first_assum drule
  \\ strip_tac \\ fs[]
  \\ Cases_on`fnm = fnm'` \\ fs[]
  \\ fs[LENGTH_TAKE_EQ]
  \\ qmatch_goalsub_abbrev_tac`f12 ⇒ _`
  \\ strip_tac \\ fs[] \\ rveq
  \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
  \\ pop_assum mp_tac
  \\ simp[NUMERAL_LESS_THM]
  \\ first_x_assum(qspec_then`w82n conf`mp_tac)
  \\ simp[]
  \\ rw[] \\ fs[] \\ rw[] \\ fs[] \\ rfs[]
  \\ qpat_x_assum`STD_streams fs`mp_tac
  \\ simp[fsFFIPropsTheory.STD_streams_def]
  \\ strip_tac
  \\ TRY (
    first_x_assum(qspecl_then[`2`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ simp[] \\ strip_tac \\ rveq
    \\ first_x_assum(qspecl_then[`fd`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ simp[] \\ NO_TAC )
  \\ TRY (
    first_x_assum(qspecl_then[`fd`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ simp[] \\ strip_tac \\ rveq
    \\ first_x_assum(qspecl_then[`1`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ simp[] \\ NO_TAC )
  \\ TRY (
    last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
    \\ simp[] \\ NO_TAC ));

val ag32_stdin_implemented_ffi_write = Q.store_thm("ag32_stdin_implemented_ffi_write",
  `
  STD_streams fs ∧
  ag32_stdin_implemented fs m ∧
   ffi_write conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs'
     (ag32_ffi_mem_update "write" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "write"))) m)))`,
  rw[ag32_stdin_implemented_def]
  \\ qexists_tac`off`
  \\ qexists_tac`inp`
  \\ simp[]
  \\ CONJ_TAC>- (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def]>>
    every_case_tac>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    rpt(pairarg_tac>>fs[])>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    fs[fsFFITheory.fsupdate_def]>>
    simp[ALIST_FUPDKEY_ALOOKUP]>>
    rw[]>>fs[])
  \\ CONJ_TAC>- (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def]>>
    every_case_tac>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    rpt(pairarg_tac>>fs[])>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    fs[fsFFITheory.fsupdate_def]>>
    simp[ALIST_FUPDKEY_ALOOKUP]>>
    rw[]>>fs[]>>
    fs[fsFFIPropsTheory.STD_streams_def]>>
    rfs[])
  \\ simp[CONJ_ASSOC]
  \\ conj_tac
  >- (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def, EVAL``heap_start_offset``]
    \\ every_case_tac
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[]
    \\ simp[ag32_ffi_mem_update_def]
    >- (
      fs[fsFFITheory.write_def]>>
      rpt(pairarg_tac>>fs[])>>rveq>>fs[]>>
      DEP_REWRITE_TAC [get_mem_word_asm_write_bytearray_UNCHANGED_LT,get_mem_word_UPDATE]>>
      fs[]>>EVAL_TAC>>
      fs[MarshallingTheory.n2w2_def,MarshallingTheory.w22n_def,MIN_DEF]>>
      blastLib.FULL_BBLAST_TAC)
    >>
      DEP_REWRITE_TAC [get_mem_word_UPDATE,get_mem_word_asm_write_bytearray_UNCHANGED_LT]>>
      fs[]>>EVAL_TAC>>
      blastLib.FULL_BBLAST_TAC)
  >>
    (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def]
    \\ every_case_tac
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[]
    \\ simp[ag32_ffi_mem_update_def]
    >- (
      fs[fsFFITheory.write_def]>>
      rpt(pairarg_tac>>fs[])>>rveq>>fs[]>>
      DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT,bytes_in_memory_asm_write_bytearray_LT]>>
      fs[stdin_size_def]>>EVAL_TAC>>fs[MIN_DEF]>>
      `5242880+2300 ≤ w2n (ms.R 3w)` suffices_by fs[]>>
      simp[]>>
      fs[WORD_LS,EVAL``heap_start_offset``])
    >>
    DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT,bytes_in_memory_asm_write_bytearray_LT]>>
    fs[stdin_size_def]>>
    EVAL_TAC>>fs[]>>
    `5242880+2300 ≤ w2n (ms.R 3w)` suffices_by fs[]>>
    simp[]>>
    fs[WORD_LS,EVAL``heap_start_offset``]));

val ag32_cline_implemented_ffi_write = Q.store_thm("ag32_cline_implemented_ffi_write",
  `ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_cline_implemented cl
     (ag32_ffi_mem_update "write" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "write"))) m)))`,
  rw[ag32_cline_implemented_def]
  \\ cheat (* cline unaffected by write, don't prove until all the cline ffi functions are done *));

val ag32_ffi_rel_read_mem_update = Q.store_thm("ag32_ffi_rel_read_mem_update",
  `(ffi_read conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   (m ((n2w (ffi_code_start_offset - 1)):word32) = n2w (THE (ALOOKUP FFI_codes "read"))) ∧
    ag32_fs_ok fs
   ⇒
   (get_ag32_io_event
     (ag32_ffi_mem_update "read" conf bytes new_bytes m)
    = get_output_io_event (IO_event "read" conf (ZIP (bytes,new_bytes))))`,
  rw[]
  \\ imp_res_tac fsFFIPropsTheory.ffi_read_length
  \\ fs[fsFFITheory.ffi_read_def]
  \\ fs[CaseEq"list"]
  \\ rveq
  \\ simp[get_output_io_event_def, MAP_ZIP]
  \\ simp[ag32_ffi_mem_update_def]
  \\ fs[]
  \\ PURE_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ simp[get_ag32_io_event_def]
  \\ reverse(Cases_on`LENGTH conf = 8` \\ fs[])
  >- ( rveq \\ fs[LUPDATE_def] \\ rveq \\ simp[] \\ EVAL_TAC)
  \\ reverse(Cases_on`LENGTH tll ≥ w22n [n1; n0]`) \\ fs[]
  >- ( rveq \\ fs[LUPDATE_def] \\ rveq \\ simp[] \\ EVAL_TAC)
  \\ fs[fsFFITheory.read_def]
  \\ Cases_on`ALOOKUP fs.infds (w82n conf)` \\ fs[]
  >- ( rveq \\ fs[LUPDATE_def] \\ rveq \\ simp[] \\ EVAL_TAC)
  \\ pairarg_tac \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ `IS_SOME (ALOOKUP fs.files fnm)` by metis_tac[IS_SOME_EXISTS]
  \\ fs[IS_SOME_EXISTS, PULL_EXISTS, EXISTS_PROD] \\ fs[]
  \\ rveq \\ fs[]
  \\ reverse(Cases_on`md` \\ fs[LUPDATE_def]) \\ rveq \\ fs[]
  \\ DEP_ONCE_REWRITE_TAC [set_mem_word_neq]>> fs[]>>
  EVAL_TAC);

val ag32_fs_ok_ffi_read = Q.store_thm("ag32_fs_ok_ffi_read",
  `(ffi_read conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'`,
  rw[fsFFITheory.ffi_read_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ `STD_streams fs'`
  by (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ fs[fsFFITheory.read_def]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ reverse(Cases_on`w82n conf = 1 ∨ w82n conf = 2`)
    >- ( fs[fsFFIPropsTheory.STD_streams_bumpFD] )
    \\ qhdtm_x_assum`STD_streams`mp_tac
    \\ simp[Once fsFFIPropsTheory.STD_streams_def]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ fs[] )
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, fsFFITheory.read_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[fsFFITheory.fsupdate_def, ALIST_FUPDKEY_ALOOKUP, LDROP1_THM,
                fsFFITheory.bumpFD_def]
  \\ conj_tac
  >- (
    rw[] \\ every_case_tac \\ fs[]
    \\ metis_tac[IS_SOME_EXISTS, NOT_SOME_NONE])
  \\ rw[]
  \\ fs[CaseEq"option"]
  \\ PairCases_on`v` \\ fs[]
  \\ fs[CaseEq"bool",PULL_EXISTS] \\ rveq
  >- (
    first_x_assum drule
    \\ rw[] \\ rw[]
    \\ Cases_on`fnm = fnm'` \\ fs[]
    \\ strip_tac \\ fs[] ));

val ag32_stdin_implemented_ffi_read = Q.store_thm("ag32_stdin_implemented_ffi_read",
  `ag32_fs_ok fs ∧
   ag32_stdin_implemented fs m ∧
   ffi_read conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   (* you may assume more here from the context where this is used *)
   ⇒
   ag32_stdin_implemented fs'
     (ag32_ffi_mem_update "read" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "read"))) m)))`,
  rw[]>>fs[fsFFITheory.ffi_read_def, fsFFITheory.read_def]>>
  fs[CaseEq"list"]>>
  fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
  >- (
    rpt(pairarg_tac>>fs[])>>rveq>>
    fs[ag32_stdin_implemented_def]>>fs[]>>
    fs[ag32_ffi_mem_update_def,MarshallingTheory.n2w2_def,MarshallingTheory.w22n_def]>>
    DEP_REWRITE_TAC[get_mem_word_set_mem_word]>>
    CONJ_TAC>-
      EVAL_TAC>>
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT,get_mem_word_UPDATE]>>
    CONJ_TAC>- (
      EVAL_TAC>>
      fs[EVAL``heap_start_offset``] >>
      rpt(CONJ_TAC>- blastLib.FULL_BBLAST_TAC)>>
      fs[MIN_DEF]>>rw[]>>fs[] >>
      blastLib.FULL_BBLAST_TAC)>>
    fs[word_add_n2w]>>
    qmatch_goalsub_abbrev_tac`ls MOD _`>>
    qexists_tac`ls`>>simp[]>>
    rw[]
    >-
      (simp[fsFFITheory.bumpFD_def,ALIST_FUPDKEY_ALOOKUP]>>
      reverse IF_CASES_TAC
      >- (
        fs[ag32_fs_ok_def]
        \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
        \\ fs[fsFFIPropsTheory.STD_streams_def]
        \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
        \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
        \\ qpat_x_assum`_ < 3`mp_tac
        \\ simp[NUMERAL_LESS_THM] )
      >>
      fs[Abbr`ls`]>>
      qmatch_goalsub_abbrev_tac`nn = _`>>
      qspec_then`256` assume_tac DIVISION>>fs[]>>
      pop_assum(qspec_then`nn` assume_tac)>>
      `SUC strm = output_buffer_size + 1` by rfs[ag32_fs_ok_def, ADD1] >>
      `nn ≤ output_buffer_size + 1` by simp[Abbr`nn`, MIN_DEF] >>
      fs[EVAL``output_buffer_size``])
    >-
      (pop_assum mp_tac>>EVAL_TAC)
    >- (
      fs[ag32_fs_ok_def]
      \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
      \\ fs[fsFFIPropsTheory.STD_streams_def]
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
      \\ qpat_x_assum`_ < 3`mp_tac
      \\ simp[NUMERAL_LESS_THM]
      \\ rw[] \\ fs[] \\ rveq
      \\ rfs[] \\ rveq
      \\ fs[EVAL``output_buffer_size``]
      \\ simp[Abbr`ls`]
      \\ fs[EVAL``stdin_size``]
      \\ qmatch_goalsub_abbrev_tac`k MOD 256`
      \\ `k < 256` by rw[Abbr`k`, MIN_DEF, DIV_LT_X] \\ fs[]
      \\ qmatch_goalsub_abbrev_tac`j MOD 256`
      \\ simp[Abbr`k`]
      \\ qmatch_goalsub_abbrev_tac`_ + k`
      \\ `k = j` by (
        simp[Abbr`k`]
        \\ qspec_then`256`mp_tac DIVISION
        \\ simp[] )
      \\ rw[]
      \\ pop_assum kall_tac
      \\ `j ≤ LENGTH content - inp'` by simp[Abbr`j`]
      \\ simp[])
    >>
      simp[set_mem_word_def]>>
      ntac 4 (DEP_ONCE_REWRITE_TAC[bytes_in_memory_UPDATE_GT])>>
      DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT,bytes_in_memory_UPDATE_LT]>>
      fs[stdin_size_def]>>
      EVAL_TAC>>fs[]>>
      fs[WORD_LS,EVAL``heap_start_offset``])
  >>
  fs[ag32_stdin_implemented_def]>>
  simp[ag32_ffi_mem_update_def]>>
  simp[LUPDATE_def]>>
  DEP_REWRITE_TAC [get_mem_word_UPDATE,get_mem_word_asm_write_bytearray_UNCHANGED_LT,bytes_in_memory_asm_write_bytearray_LT,bytes_in_memory_UPDATE_LT]>>
  fs[]>>
  EVAL_TAC>>fs[stdin_size_def]>>
  `5242880+2300 ≤ w2n (ms.R 3w)` by
    fs[WORD_LS,EVAL``heap_start_offset``]>>
  fs[]>>
  Cases_on`ms.R 3w` \\ fs[word_lo_n2w]);

val ag32_cline_implemented_ffi_read = Q.store_thm("ag32_cline_implemented_ffi_read",
  `ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_cline_implemented cl
     (ag32_ffi_mem_update "read" conf bytes bytes'
       (asm_read_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "read"))) m)))`,
  rw[ag32_cline_implemented_def]
  \\ cheat (* cline unaffected by read, don't prove until all the cline ffi functions are done *));

val ag32_ffi_interfer_write = Q.store_thm("ag32_ffi_interfer_write",
  `ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "write" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "write" ffi_names = SOME index) ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + index * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "write") + 4 * k))
         = Encode (EL k ag32_ffi_write_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain /\ x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)`,
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ last_x_assum(qspec_then`index * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (index * (ffi_offset DIV 4)) = index * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ simp[EL_FLAT_MAP_mk_jump_ag32_code] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_write_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then drule
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def]
    \\ EVAL_TAC)
  \\ strip_tac
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_write_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ disch_then drule \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ `∃n1 n0 off1 off0 tll. bytes = n1::n0::off1::off0::tll`
  by ( fs[fsFFITheory.ffi_write_def] \\ fs[CaseEq"list"] )
  \\ rveq
  \\ disch_then drule
  \\ fs[]
  \\ impl_tac
  >- (
    reverse conj_tac
    >- (
      simp[Abbr`md`]
      \\ EVAL_TAC
      \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
      \\ fs[memory_size_def, word_add_n2w]
      \\ simp[PULL_FORALL]
      \\ Cases \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X] )
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
    \\ fs[memory_size_def, word_add_n2w]
    \\ simp[PULL_FORALL]
    \\ Cases \\ Cases
    \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X]
    \\ conj_tac
    >- (
      CCONTR_TAC
      \\ fs[]
      \\ rveq \\ fs[]
      \\ qpat_x_assum`_ MOD _ < _`mp_tac \\ simp[]
      \\ qpat_x_assum`_ ≤ _ MOD _`mp_tac \\ simp[] )
    \\ simp[data_to_word_assignProofTheory.IMP]
    \\ strip_tac
    \\ qx_gen_tac`j`
    \\ Cases_on`j < 428` \\ simp[])
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `EL index ffi_names = "write"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ conj_tac
  >- (
    fs[]
    \\ conj_tac
    >- (
      irule ag32_ffi_rel_write_mem_update
      \\ fs[]
      \\ reverse conj_tac
      >- ( asm_exists_tac \\ fs[] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_write_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[asmSemTheory.bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_write]
    \\ conj_tac
    >- (
      match_mp_tac ag32_stdin_implemented_ffi_write
      \\ fs[ag32_fs_ok_def]
      \\ drule asmPropsTheory.bytes_in_memory_in_domain
      \\ disch_then(qspec_then`0` assume_tac)>>fs[Abbr`md`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w])
    \\ match_mp_tac ag32_cline_implemented_ffi_write
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`ms.R 3w ∈ md` mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`ms.R 3w`
    \\ fs[word_lo_n2w, word_ls_n2w, EVAL``code_start_offset _``,
          FFI_codes_def, LEFT_ADD_DISTRIB, memory_size_def, word_add_n2w])
  \\ rw[]
  \\ simp[ag32_ffi_mem_update_def]
  \\ reverse IF_CASES_TAC
  >- (
    simp[APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      qpat_x_assum`x ∉ ag32_ffi_mem_domain`mp_tac
      \\ rveq
      \\ simp[ag32_ffi_mem_domain_def]
      \\ EVAL_TAC
      \\ fs[word_add_n2w, memory_size_def]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ irule asm_write_bytearray_unchanged_all_words
    \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
    \\ simp []
    \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ imp_res_tac fsFFIPropsTheory.ffi_write_length
    \\ fs[ADD1]
    \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[]
    \\ qpat_x_assum`x ∉ ag32_ffi_mem_domain`mp_tac
    \\ rveq
    \\ simp[ag32_ffi_mem_domain_def]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
  \\ irule asm_write_bytearray_unchanged
  \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
  \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
  \\ qpat_x_assum`_ = w2n (ms.R 2w)`(assume_tac o SYM) \\ fs[]
  \\ fs[word_add_n2w]
  \\ fs[EVAL``output_offset``]
  \\ Cases_on`x` \\ fs[word_lo_n2w, word_ls_n2w]
  \\ qmatch_goalsub_abbrev_tac`LENGTH conf + ll`
  \\ pop_assum mp_tac
  \\ simp[LENGTH_TAKE_EQ]
  \\ reverse IF_CASES_TAC
  >- (
    fs[ADD1]
    \\ fs[fsFFITheory.ffi_write_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[] \\ rveq )
  \\ simp[EVAL``output_buffer_size``]
  \\ `LENGTH conf = 8` by (
    fs[fsFFITheory.ffi_write_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] )
  \\ strip_tac
  \\ simp[Abbr`ll`]
  \\ conj_tac >- simp[MIN_DEF]
  \\ conj_tac
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged_alt
    \\ simp[APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      fs[data_to_word_assignProofTheory.IMP]
      \\ CCONTR_TAC \\ fs[]
      \\ qpat_x_assum`_ ∉ all_words _ _`mp_tac
      \\ simp[]
      \\ once_rewrite_tac[WORD_ADD_COMM]
      \\ irule IN_all_words_add
      \\ simp[] )
    \\ EVAL_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
    \\ rveq \\ EVAL_TAC
    \\ simp[] )
  \\ simp[MIN_DEF]
  \\ fs[data_to_word_assignProofTheory.IMP]
  \\ fs[EVAL``output_buffer_size``]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
  \\ simp[]);

val ag32_ffi_interfer_read = Q.store_thm("ag32_ffi_interfer_read",
  `ag32_ffi_rel ms ffi ∧ (SND ffi.ffi_state = fs) ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "read" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "read" ffi_names = SOME index) ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + index * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_read_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "read") + 4 * k))
         = Encode (EL k ag32_ffi_read_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ { ms.R 3w + n2w i | i < LENGTH bytes } ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)`,
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ last_x_assum(qspec_then`index * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (index * (ffi_offset DIV 4)) = index * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ simp[EL_FLAT_MAP_mk_jump_ag32_code] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_read_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def, ag32_stdin_implemented_def]
    \\ EVAL_TAC \\ fs [markerTheory.Abbrev_def]
    \\ qexists_tac`off` \\ qexists_tac`LENGTH inp`
    \\ fs[EVAL``stdin_size``])
  \\ strip_tac
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_read_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ disch_then drule \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ `∃n1 n0 off1 off0 tll. bytes = n1::n0::off1::off0::tll`
  by ( fs[fsFFITheory.ffi_read_def] \\ fs[CaseEq"list"] )
  \\ rveq
  \\ disch_then drule
  \\ fs[]
  \\ impl_tac
  >- (
    reverse conj_tac
    >- (
      simp[Abbr`md`]
      \\ EVAL_TAC
      \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
      \\ fs[memory_size_def, word_add_n2w]
      \\ simp[PULL_FORALL]
      \\ Cases \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X] )
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
    \\ fs[memory_size_def, word_add_n2w]
    \\ simp[PULL_FORALL]
    \\ Cases \\ Cases
    \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X]
    \\ conj_tac
    >- (
      CCONTR_TAC
      \\ fs[]
      \\ rveq \\ fs[]
      \\ qpat_x_assum`_ MOD _ < _`mp_tac \\ simp[]
      \\ qpat_x_assum`_ ≤ _ MOD _`mp_tac \\ simp[] )
    \\ simp[data_to_word_assignProofTheory.IMP]
    \\ strip_tac
    \\ qx_gen_tac`j`
    \\ Cases_on`j < 420` \\ simp[])
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `EL index ffi_names = "read"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ conj_tac >- (
    fs[]
    \\ conj_tac
    >- (
      irule ag32_ffi_rel_read_mem_update
      \\ fs[]
      \\ reverse conj_tac
      >- ( asm_exists_tac \\ fs[] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_read_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[asmSemTheory.bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_read]
    \\ conj_tac >- (
      match_mp_tac ag32_stdin_implemented_ffi_read
      \\ fs[]
      \\ drule asmPropsTheory.bytes_in_memory_in_domain
      \\ disch_then(qspec_then`0` assume_tac)>>fs[Abbr`md`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC
      \\ fs[FFI_codes_def, EVAL``code_start_offset _``,memory_size_def,LEFT_ADD_DISTRIB]
      \\ Cases_on`ms.R 3w`
      \\ fs[word_lo_n2w, word_ls_n2w])
    \\ match_mp_tac ag32_cline_implemented_ffi_read
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`ms.R 3w ∈ md` mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`ms.R 3w`
    \\ fs[word_lo_n2w, word_ls_n2w, EVAL``code_start_offset _``,
          FFI_codes_def, LEFT_ADD_DISTRIB, memory_size_def, word_add_n2w])
  \\ gen_tac \\ strip_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[ADD1]
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ reverse PURE_TOP_CASE_TAC \\ fs[]
  >- (
    match_mp_tac asm_write_bytearray_unchanged_alt
    \\ qpat_x_assum`x ∉ _` mp_tac
    \\ fs [ag32_ffi_mem_domain_def]
    \\ `startup_code_size < 2**32-1 /\
        (ffi_code_start_offset − 1) < 2**32-1` by EVAL_TAC
    \\ Cases_on `x` \\ fs [WORD_LO,WORD_LS]
    \\ fs [METIS_PROVE [] ``(~b \/ c) <=> (b ==> c)``,NOT_LESS]
    \\ fs [APPLY_UPDATE_THM,bool_case_eq]
    \\ rpt strip_tac
    \\ DISJ2_TAC \\ pop_assum mp_tac \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [] )
  \\ fs[fsFFITheory.ffi_read_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
  \\ conj_tac
  >- (
    fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`ms.R 3w ∈ _`mp_tac
    \\ Cases_on`ms.R 3w`
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_lo_n2w, word_ls_n2w, EVAL``stdin_offset``, memory_size_def, EVAL``code_start_offset _``] )
  \\ DEP_REWRITE_TAC[set_mem_word_neq]
  \\ conj_tac
  >- (
    EVAL_TAC
    \\ qpat_x_assum`x ∉ _`mp_tac
    \\ EVAL_TAC
    \\ Cases_on`x`
    \\ simp[word_ls_n2w, word_lo_n2w] )
  \\ irule asm_write_bytearray_unchanged_alt
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ qpat_x_assum`_ ∉ _`mp_tac
  \\ EVAL_TAC);

val ag32_ffi_interfer_get_arg_count = Q.store_thm("ag32_ffi_interfer_get_arg_count",
  `ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "get_arg_count" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "get_arg_count" ffi_names = SOME index) ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + index * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_count_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg_count") + 4 * k))
         = Encode (EL k ag32_ffi_get_arg_count_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ { ms.R 3w + n2w i | i < LENGTH bytes } ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)`,
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ last_x_assum(qspec_then`index * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (index * (ffi_offset DIV 4)) = index * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ simp[EL_FLAT_MAP_mk_jump_ag32_code] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_get_arg_count_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def, ag32_cline_implemented_def]
    \\ EVAL_TAC \\ fs [markerTheory.Abbrev_def])
  \\ strip_tac
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_get_arg_count_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `EL index ffi_names = "get_arg_count"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ conj_tac >- (
    fs[]
    \\ conj_tac
    >- (
      simp[ag32_ffi_mem_update_def]
      \\ simp[get_output_io_event_def]
      \\ simp[get_ag32_io_event_def, APPLY_UPDATE_THM]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ simp[APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ fs[clFFITheory.ffi_get_arg_count_def]
      \\ rveq \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ Cases_on`ms.R 3w`
      \\ EVAL_TAC
      \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LEFT_ADD_DISTRIB, FFI_codes_def])
    \\ cheat (* stdin and cline remain implemented: prove as lemmas *))
  \\ gen_tac \\ strip_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[ADD1]
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ irule asm_write_bytearray_unchanged_alt
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ qpat_x_assum`_ ∉ _`mp_tac
  \\ EVAL_TAC);

val _ = export_theory();

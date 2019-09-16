(*
  Implement and prove correct monadic version of encoder
*)
open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open asmTheory lab_to_targetTheory monadic_encTheory

val _ = new_theory "monadic_enc32"
val _ = monadsyntax.temp_add_monadsyntax()

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``

(* Data type for the exceptions *)
Datatype:
  state_exn_32 = Fail string | Subscript
End

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

(* 32 BIT IMPLEMENTATION *)

(* The state is just an array *)
Datatype:
  enc_state_32 = <|
       hash_tab_32 : ((32 asm # word8 list) list) list
     |>
End

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn_32`` ``:enc_state_32``;
Overload failwith[local] = ``raise_Fail``

val accessors = define_monad_access_funs ``:enc_state_32``;

val hash_tab_32_accessors = el 1 accessors;
val (hash_tab_32,get_hash_tab_32_def,set_hash_tab_32_def) = hash_tab_32_accessors;

(* Fixed-size array manipulators *)
val arr_manip = define_MFarray_manip_funs
  [hash_tab_32_accessors] sub_exn update_exn;

val hash_tab_32_manip = el 1 arr_manip;

val hash_tab_32_accessor = save_thm("hash_tab_32_accessor",accessor_thm hash_tab_32_manip);

val lookup_ins_table_32_def = Define`
  lookup_ins_table_32 enc n a =
  let v = hash_asm n a MOD n in
  do
    ls <- hash_tab_32_sub v;
    case ALOOKUP ls a of
      NONE =>
      do
        encode <- return (enc a);
        update_hash_tab_32 v ((a,encode)::ls);
        return encode
      od
    | SOME res =>
      return res
  od`

val enc_line_hash_32_def = Define `
  (enc_line_hash_32 enc skip_len n (Label n1 n2 n3) =
    return (Label n1 n2 skip_len)) ∧
  (enc_line_hash_32 enc skip_len n (Asm a _ _) =
    do
      bs <- lookup_ins_table_32 enc n (cbw_to_asm a);
      return (Asm a bs (LENGTH bs))
    od) ∧
  (enc_line_hash_32 enc skip_len n (LabAsm l _ _ _) =
     do
       bs <- lookup_ins_table_32 enc n (lab_inst 0w l);
       return (LabAsm l 0w bs (LENGTH bs))
     od)`

val enc_line_hash_32_ls_def = Define`
  (enc_line_hash_32_ls enc skip_len n [] = return []) ∧
  (enc_line_hash_32_ls enc skip_len n (x::xs) =
  do
    fx <- enc_line_hash_32 enc skip_len n x;
    fxs <- enc_line_hash_32_ls enc skip_len n xs;
    return (fx::fxs)
  od)`

val enc_sec_hash_32_ls_def = Define`
  (enc_sec_hash_32_ls enc skip_len n [] = return []) ∧
  (enc_sec_hash_32_ls enc skip_len n (x::xs) =
  case x of Section k ys =>
  do
    ls <- enc_line_hash_32_ls enc skip_len n ys;
    rest <- enc_sec_hash_32_ls enc skip_len n xs;
    return (Section k ls::rest)
  od)`

val enc_sec_hash_32_ls_full_def = Define`
  enc_sec_hash_32_ls_full enc n xs =
  enc_sec_hash_32_ls enc (LENGTH (enc (Inst Skip))) n xs`

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
val array_fields_names = ["hash_tab_32"];
val run_ienc_state_32_def = define_run ``:enc_state_32``
                                      array_fields_names
                                      "ienc_state_32";

val enc_secs_32_aux_def = Define`
  enc_secs_32_aux enc n xs =
    run_ienc_state_32 (enc_sec_hash_32_ls_full enc n xs) <| hash_tab_32 := (n, []) |>`

val enc_secs_32_def = Define`
  enc_secs_32 enc n xs =
    case enc_secs_32_aux enc (if n = 0 then 1 else n) xs of
      Success xs => xs
    | Failure _ => []`

val msimps = [st_ex_bind_def,st_ex_return_def];

Theorem Msub_eqn[simp]:
    ∀e n ls v.
  Msub e n ls =
  if n < LENGTH ls then Success (EL n ls)
                   else Failure e
Proof
  ho_match_mp_tac Msub_ind>>rw[]>>
  simp[Once Msub_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  Cases_on`n`>>fs[]
QED

Theorem hash_tab_32_sub_eqn[simp]:
    hash_tab_32_sub n s =
  if n < LENGTH s.hash_tab_32 then
    (Success (EL n s.hash_tab_32),s)
  else
    (Failure (Subscript),s)
Proof
  rw[fetch "-" "hash_tab_32_sub_def"]>>
  fs[Marray_sub_def]
QED

Theorem Mupdate_eqn[simp]:
    ∀e x n ls.
  Mupdate e x n ls =
  if n < LENGTH ls then
    Success (LUPDATE x n ls)
  else
    Failure e
Proof
  ho_match_mp_tac Mupdate_ind>>rw[]>>
  simp[Once Mupdate_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[LUPDATE_def]>>
  Cases_on`n`>>fs[LUPDATE_def]
QED

Theorem update_hash_tab_32_eqn[simp]:
    update_hash_tab_32 n t s =
  if n < LENGTH s.hash_tab_32 then
     (Success (),s with hash_tab_32 := LUPDATE t n s.hash_tab_32)
  else
     (Failure (Subscript),s)
Proof
  rw[fetch "-" "update_hash_tab_32_def"]>>
  fs[Marray_update_def]
QED

val good_table_32_def = Define`
  good_table_32 enc n s ⇔
  EVERY (λls. EVERY (λ(x,y). enc x = y) ls) s.hash_tab_32 ∧
  LENGTH s.hash_tab_32 = n`;

val lookup_ins_table_32_correct = Q.prove(`
  good_table_32 enc n s ∧
  0 < n ⇒
  ∃s'.
  lookup_ins_table_32 enc n aa s = (Success (enc aa), s') ∧
  good_table_32 enc n s'`,
  rw[]>>fs[lookup_ins_table_32_def]>>
  simp msimps>>
  reverse IF_CASES_TAC
  >- (
    fs[good_table_32_def]>>
    rfs[])>>
  simp[]>>
  TOP_CASE_TAC
  >- (
    fs[good_table_32_def]>>
    match_mp_tac IMP_EVERY_LUPDATE>>fs[]>>
    drule EL_MEM>>
    metis_tac[EVERY_MEM])
  >>
  fs[good_table_32_def]>>
  drule EL_MEM>>
  drule ALOOKUP_MEM>>
  fs[EVERY_MEM]>>
  rw[]>> first_x_assum drule>>
  disch_then drule>>
  fs[]);

val enc_line_hash_32_correct = Q.prove(‘
  ∀line.
    good_table_32 enc n s ∧ 0 < n ⇒
    ∃s'.
     enc_line_hash_32 enc skip_len n line s =
       (Success (enc_line enc skip_len line),s') ∧
     good_table_32 enc n s'’,
  Cases>>fs[enc_line_hash_32_def,enc_line_def]>>
  fs msimps>>
  qmatch_goalsub_abbrev_tac`lookup_ins_table_32 _ _ aa`>>
  rw[]>>
  old_drule lookup_ins_table_32_correct>>rw[]>>simp[]);

val enc_line_hash_32_ls_correct = Q.prove(`
  ∀xs s.
  good_table_32 enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_line_hash_32_ls enc skip_len n xs s =
  (Success (MAP (enc_line enc skip_len) xs), s') ∧
  good_table_32 enc n s'`,
  Induct>>fs[enc_line_hash_32_ls_def]>>
  fs msimps>>
  rw[]>> simp[]>>
  old_drule enc_line_hash_32_correct>>
  disch_then (qspec_then `h` assume_tac)>>rfs[]>>
  first_x_assum drule>>
  rw[]>>simp[]);

val enc_sec_hash_32_ls_correct = Q.prove(`
  ∀xs s.
  good_table_32 enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_sec_hash_32_ls enc skip_len n xs s =
  (Success (MAP (enc_sec enc skip_len) xs), s') ∧
  good_table_32 enc n s'`,
  Induct>>fs[enc_sec_hash_32_ls_def]>>
  fs msimps>>
  rw[]>> simp[]>>
  TOP_CASE_TAC>>simp[]>>
  old_drule enc_line_hash_32_ls_correct>>
  simp[]>>
  disch_then(qspec_then`l` assume_tac)>>fs[]>>
  first_x_assum drule>>rw[]>>
  simp[enc_sec_def]);

Theorem enc_secs_32_correct:
  enc_secs_32 enc n xs =
  (enc_sec_list enc xs)
Proof
  fs[enc_secs_32_def,enc_secs_32_aux_def]>>
  fs[fetch "-" "run_ienc_state_32_def",run_def]>>
  simp[enc_sec_hash_32_ls_full_def]>>
  qmatch_goalsub_abbrev_tac `_ enc sl nn xs s`>>
  qspecl_then [`sl`,`nn`,`enc`,`xs`,`s`] mp_tac (GEN_ALL enc_sec_hash_32_ls_correct)>>
  impl_tac>-
    (unabbrev_all_tac>>fs[good_table_32_def,EVERY_REPLICATE])>>
  rw[]>>
  fs[enc_sec_list_def]
QED

val _ = export_theory();

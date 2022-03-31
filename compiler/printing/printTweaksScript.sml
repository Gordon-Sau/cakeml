(*
   The top-level printing adjustment, as called by the REPL.
*)

open HolKernel Parse boolLib bossLib BasicProvers;
open addPrintValsTheory addTypePPTheory inferTheory;
local open dep_rewrite in end

val _ = new_theory "printTweaks";

Definition print_failure_message_def:
  print_failure_message s =
  Dlet unknown_loc Pany (App Opapp [Var (Short "print_pp");
        (App Opapp [Var (Long "PrettyPrinter" (Short "failure_message"));
            Lit (StrLit (explode s))])])
End

Definition add_err_message_def:
  add_err_message s decs tn ienv inf_st =
  (* something's gone wrong, try to add a message *)
  let pmsg = [print_failure_message s] in
  case infer_ds ienv pmsg inf_st of
  (Success msg_ienv, inf_st2) =>
      (Success (decs ++ pmsg, (tn, extend_dec_ienv msg_ienv ienv, inf_st2)))
  (* if even that fails, skip it *)
  | (Failure _, _) => Success (decs, (tn, ienv, inf_st))
End

Definition add_print_features_def:
  add_print_features st decs =
  let (tn, ienv, next_id) = st in
  let decs2 = add_pp_decs tn.pp_fixes decs in
  case infer_ds ienv decs2 (init_infer_state <| next_id := next_id |>) of
  (Success decs_ienv, inf_st) =>
  let (prints, tn2) = val_prints tn ienv decs_ienv in
  let ienv2 = extend_dec_ienv decs_ienv ienv in
  (case infer_ds ienv2 prints inf_st of
  (Success prints_ienv, inf_st2) =>
      (Success (decs2 ++ prints, (tn2, extend_dec_ienv prints_ienv ienv2, inf_st2)))
  | (Failure x, _) => add_err_message (strlit "adding val pretty-prints: " ^ SND x)
        decs2 tn2 ienv2 inf_st
  )
  | (Failure x, _) =>
  (* maybe the default pretty-printer decs are the problem *)
  (case infer_ds ienv decs (init_infer_state <| next_id := next_id |>) of
  (Success ienv3, inf_st3) => add_err_message (strlit "adding type pp funs: " ^ SND x)
        decs tn (extend_dec_ienv ienv3 ienv) inf_st3
  | (Failure x, _) => Failure x
  )
End

Definition read_next_dec_def:
  read_next_dec =
    [Dlet (Locs UNKNOWNpt UNKNOWNpt) Pany
       (App Opapp
          [App Opderef [Var (Long "Repl" (Short "readNextString"))];
           Con NONE []])]
End

Definition add_print_then_read_def:
  add_print_then_read types decs =
    case add_print_features types decs of
    | Failure x => Failure x
    | Success (new_decs,(tn,ienv,inf_st)) =>
        case infer_ds ienv read_next_dec inf_st of
        | (Success read_ienv, inf_st2) =>
            (Success (new_decs ++ read_next_dec,
                      (tn,extend_dec_ienv read_ienv ienv, inf_st2.next_id)))
        | (Failure x, _) => Failure x
End

Triviality eq_inf_x =
  ``(v1 with inf_v := v2.inf_v) = v2`` |> REWRITE_CONV [inf_env_component_equality]
    |> GSYM |> MATCH_MP EQ_IMPLIES

Theorem infer_ds_append:
  !xs ys ienv st. infer_ds ienv (xs ++ ys) st =
  (case infer_ds ienv xs st of
    (Failure x, y) => (Failure x, y)
  | (Success ienv2, st2) =>
  (case infer_ds (extend_dec_ienv ienv2 ienv) ys st2 of
    (Failure x, y) => (Failure x, y)
  | (Success ienv3, st3) => (Success (extend_dec_ienv ienv3 ienv2), st3)
  ))
Proof
  Induct
  >- (
    rw [infer_d_def, st_ex_return_def, extend_dec_ienv_def]
    \\ simp [eq_inf_x]
    \\ every_case_tac \\ simp []
  )
  >- (
    rw [infer_d_def, st_ex_return_def, st_ex_bind_def]
    \\ fs [extend_dec_ienv_def]
    \\ every_case_tac \\ fs []
  )
QED

Theorem add_print_features_succ:
  add_print_features st decs = (infer$Success (decs2, st2)) ==>
  ?tn ienv next_id tn2 ienv2 inf_st2.
  st = (tn, ienv, next_id) /\ st2 = (tn2, extend_dec_ienv ienv2 ienv, inf_st2) /\
  infer_ds ienv decs2 (init_infer_state <| next_id := next_id |>) = (Success ienv2, inf_st2)
Proof
  fs [add_print_features_def, add_err_message_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [pairTheory.pair_case_eq, exc_case_eq]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [pairTheory.pair_case_eq, exc_case_eq]
  \\ rpt VAR_EQ_TAC
  \\ simp [infer_ds_append]
  \\ simp [extend_dec_ienv_def]
QED

Theorem add_print_then_read_succ:
  add_print_then_read st decs = (infer$Success (decs2, st2)) ==>
  ?tn ienv next_id tn2 ienv2 inf_st2.
  st = (tn, ienv, next_id) /\ st2 = (tn2, extend_dec_ienv ienv2 ienv, inf_st2.next_id) /\
  infer_ds ienv decs2 (init_infer_state <| next_id := next_id |>) = (Success ienv2, inf_st2)
Proof
  fs [add_print_then_read_def,AllCaseEqs()]
  \\ rw []
  \\ drule add_print_features_succ
  \\ strip_tac
  \\ gvs []
  \\ simp [infer_ds_append]
  \\ simp [extend_dec_ienv_def]
QED

val _ = export_theory ();
(*
  Definition of the FFI type
*)
open HolKernel Parse boolLib bossLib;
open libTheory;

val _ = numLib.prefer_num();

val _ = new_theory "ffi"

(*
  An oracle says how to perform an FFI call based on its internal
  state, represented by the type variable 'ffi.
*)

Datatype:
  ffi_outcome = FFI_failed | FFI_diverged
End

Datatype:
  oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
End

Type oracle_function = “:'ffi -> word8 list -> word8 list -> 'ffi oracle_result”
Type oracle = “:string -> 'ffi oracle_function”

Type read_oracle = “: 'ffi -> 'a word -> num -> word8 list # 'ffi”
Type write_oracle = “: 'ffi -> 'a word -> word8 list -> 'ffi”

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI function s with
 * immutable input bytes and mutable input map fst bytes2,
 * returning map snd bytes2 in the mutable array. *)

Datatype:
  io_event = IO_event string (word8 list) ((word8 # word8) list) |
      Mapped_read ('a word) (word8 list) |
      Mapped_write ('a word) (word8 list)
End

Datatype:
  final_event = Final_event string (word8 list) (word8 list) ffi_outcome
End

Datatype:
  ffi_state =
  <| oracle      : 'ffi oracle
   ; ffi_state   : 'ffi
   ; io_events   : ('a io_event) list
   ; read_oracle : ('a, 'ffi) read_oracle
   ; write_oracle: ('a, 'ffi) write_oracle
   |>
End

Definition initial_ffi_state_def:
  initial_ffi_state oc (ffi:'ffi) ro wo =
    <| oracle := oc; ffi_state := ffi; io_events := [];
    read_oracle := ro; write_oracle := wo |>
End

Datatype:
  ffi_result = FFI_return (('a,'ffi) ffi_state) (word8 list)
             | FFI_final final_event
End

Definition call_FFI_def:
  call_FFI (st: ('a,'ffi) ffi_state) s conf bytes =
    if s ≠ "" then
      case st.oracle s st.ffi_state conf bytes of
        Oracle_return ffi' bytes' =>
          if LENGTH bytes' = LENGTH bytes then
            FFI_return
              (st with
               <|ffi_state := ffi';
                 io_events :=
                   st.io_events ++ [IO_event s conf (ZIP (bytes,bytes'))]|>)
              bytes'
          else FFI_final (Final_event s conf bytes FFI_failed)
      | Oracle_final outcome =>
        FFI_final (Final_event s conf bytes outcome)
    else FFI_return st bytes
End

Definition mapped_read_def:
    mapped_read (st: ('a,'ffi) ffi_state) adr n_bytes =
        let (res, new_state) = st.read_oracle st.ffi_state adr n_bytes in
          (st with
           <| ffi_state := new_state;
              io_events := st.io_events ++ [Mapped_read adr res]|>,
          res)
End

Definition mapped_write_def:
    mapped_write (st: ('a,'ffi) ffi_state) adr v =
        (st with
         <| ffi_state := st.write_oracle st.ffi_state adr v;
            io_events := st.io_events ++ [Mapped_write adr v]|>)
End

Datatype:
  outcome = Success | Resource_limit_hit | FFI_outcome final_event
End

(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)
Datatype:
  behaviour =
    (* There cannot be any non-returning FFI calls in a diverging
       exeuction. The list of I/O events can be finite or infinite,
       hence the llist (lazy list) type. *)
    Diverge (('a io_event) llist)
    (* Terminating executions can only perform a finite number of
       FFI calls. The execution can be terminated by a non-returning
       FFI call. *)
  | Terminate outcome (('a io_event) list)
    (* Failure is a behaviour which we prove cannot occur for any
       well-typed program. *)
  | Fail
End

(* trace-based semantics can be recovered as an instance of oracle-based
 * semantics as follows. *)

Definition trace_oracle_def:
  trace_oracle s io_trace conf input =
    case LHD io_trace of
    | NONE => Oracle_final FFI_failed
    | SOME (IO_event s' conf' bytes2) =>
      if s = s' ∧ MAP FST bytes2 = input ∧ conf = conf' then
        Oracle_return (THE (LTL io_trace)) (MAP SND bytes2)
      else Oracle_final FFI_failed
End

val _ = export_theory()

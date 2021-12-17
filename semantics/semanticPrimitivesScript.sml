(*
  Definitions of semantic primitives (e.g., values, and functions for doing
  primitive operations) used in the semantics.
*)
open HolKernel Parse boolLib bossLib;
open libTheory astTheory namespaceTheory ffiTheory fpSemTheory;

val _ = numLib.prefer_num();

val _ = new_theory "semanticPrimitives"

(* Constructors and exceptions need unique identities, which we represent by stamps. *)
Datatype:
 stamp =
  (* Each type gets a unique number, and the constructor name must be unique
     inside of the type *)
    TypeStamp conN num
  | ExnStamp num
End

Datatype:
  sem_env =
  <| v : (modN, varN, 'v) namespace
   (* Lexical mapping of constructor idents to arity, stamp pairs *)
   ; c : (modN, conN, (num # stamp)) namespace
   |>
End

(* Value forms *)
Datatype:
 v =
    Litv lit
  (* Constructor application. Can be a tuple or a given constructor of a given type *)
  | Conv (stamp option) (v list)
  (* Function closures
     The environment is used for the free variables in the function *)
  | Closure (v sem_env) varN exp
  (* Function closure for recursive functions
   * See Closure and Letrec above
   * The last variable name indicates which function from the mutually
   * recursive bundle this closure value represents *)
  | Recclosure (v sem_env) ((varN # varN # exp) list) varN
  | Loc num
  | Vectorv (v list)
  (* Environment value for Eval, and its numeric identifier *)
  | Env (v sem_env) (num # num)
End

Type env_ctor = ``: (modN, conN, (num # stamp)) namespace``
Type env_val = ``: (modN, varN, v) namespace``

val _ = Define `
 ((bind_stamp:stamp)=  (ExnStamp(( 0 : num))))`;

val _ = Define `
 ((chr_stamp:stamp)=  (ExnStamp(( 1 : num))))`;

val _ = Define `
 ((div_stamp:stamp)=  (ExnStamp(( 2 : num))))`;

val _ = Define `
 ((subscript_stamp:stamp)=  (ExnStamp(( 3 : num))))`;


val _ = Define `
 ((bind_exn_v:v)=  (Conv (SOME bind_stamp) []))`;

val _ = Define `
 ((chr_exn_v:v)=  (Conv (SOME chr_stamp) []))`;

val _ = Define `
 ((div_exn_v:v)=  (Conv (SOME div_stamp) []))`;

val _ = Define `
 ((sub_exn_v:v)=  (Conv (SOME subscript_stamp) []))`;


val _ = Define `
 ((bool_type_num:num)      : num= (( 0 : num)))`;

val _ = Define `
 ((list_type_num:num)      : num= (( 1 : num)))`;

val _ = Define `
 ((option_type_num:num)    : num= (( 2 : num)))`;

val _ = Define `
 ((lit_type_num:num)       : num= (( 3 : num)))`;

val _ = Define `
 ((id_type_num:num)        : num= (( 4 : num)))`;

val _ = Define `
 ((ast_t_type_num:num)     : num= (( 5 : num)))`;

val _ = Define `
 ((pat_type_num:num)       : num= (( 6 : num)))`;

val _ = Define `
 ((lop_type_num:num)       : num= (( 7 : num)))`;

val _ = Define `
 ((opn_type_num:num)       : num= (( 8 : num)))`;

val _ = Define `
 ((opb_type_num:num)       : num= (( 9 : num)))`;

val _ = Define `
 ((opw_type_num:num)       : num= (( 10 : num)))`;

val _ = Define `
 ((shift_type_num:num)     : num= (( 11 : num)))`;

val _ = Define `
 ((word_size_type_num:num) : num= (( 12 : num)))`;

val _ = Define `
 ((fp_uop_type_num:num)    : num= (( 13 : num)))`;

val _ = Define `
 ((fp_bop_type_num:num)    : num= (( 14 : num)))`;

val _ = Define `
 ((fp_top_type_num:num)    : num= (( 15 : num)))`;

val _ = Define `
 ((fp_cmp_type_num:num)    : num= (( 16 : num)))`;

val _ = Define `
 ((op_type_num:num)        : num= (( 17 : num)))`;

val _ = Define `
 ((locn_type_num:num)      : num= (( 18 : num)))`;

val _ = Define `
 ((locs_type_num:num)      : num= (( 19 : num)))`;

val _ = Define `
 ((exp_type_num:num)       : num= (( 20 : num)))`;

val _ = Define `
 ((dec_type_num:num)       : num= (( 21 : num)))`;


(* The result of evaluation *)
Datatype:
  abort =
     Rtype_error
   | Rtimeout_error
   | Rffi_error final_event
End

Datatype:
  error_result =
     Rraise 'a (* Should only be a value of type exn *)
   | Rabort abort
End

Datatype:
  result =
     Rval 'a
   | Rerr ('b error_result)
End

(* Stores *)
Datatype:
 store_v =
  (* A ref cell *)
    Refv 'a
  (* A byte array *)
  | W8array (word8 list)
  (* An array of values *)
  | Varray ('a list)
End

(*val store_v_same_type : forall 'a. store_v 'a -> store_v 'a -> bool*)
val _ = Define `
 ((store_v_same_type:'a store_v -> 'a store_v -> bool) v1 v2=
   ((case (v1,v2) of
    (Refv _, Refv _) => T
  | (W8array _,W8array _) => T
  | (Varray _,Varray _) => T
  | _ => F
  )))`;


(* The nth item in the list is the value at location n *)
Type store = ``: ( 'a store_v) list``

(*val empty_store : forall 'a. store 'a*)
val _ = Define `
 ((empty_store:('a store_v)list)=  ([]))`;


(*val store_lookup : forall 'a. nat -> store 'a -> maybe (store_v 'a)*)
val _ = Define `
 ((store_lookup:num ->('a store_v)list ->('a store_v)option) l st=
   (if l < LENGTH st then
    SOME (EL l st)
  else
    NONE))`;


(*val store_alloc : forall 'a. store_v 'a -> store 'a -> store 'a * nat*)
val _ = Define `
 ((store_alloc:'a store_v ->('a store_v)list ->('a store_v)list#num) v st=
   ((st ++ [v]), LENGTH st))`;


(*val store_assign : forall 'a. nat -> store_v 'a -> store 'a -> maybe (store 'a)*)
val _ = Define `
 ((store_assign:num -> 'a store_v ->('a store_v)list ->(('a store_v)list)option) n v st=
   (if (n < LENGTH st) /\
     store_v_same_type (EL n st) v
  then
    SOME (LUPDATE v n st)
  else
    NONE))`;


(* Compiler checker for Eval. The current design requires the compiler
   to be run (as regular code within the semantics) before Eval is called,
   and these config parameters specify how to interpret the declarations to
   be evaluated and check that the compiler was run correctly. *)
Type compiler_args = ``: ((num # num) # v # dec list)``
Type compiler_fun = ``: compiler_args ->
     (v # word8 list # word64 list)option``

Datatype:
 eval_decs_state =
  <|
    compiler : compiler_fun ;
    (* state must be encoded as v somehow *)
    compiler_state : v ;
    env_id_counter : (num # num # num) ;
    (* decs must also be encoded as v *)
    decode_decs : v ->  ( dec list)option
  |>
End

(* Alternative mode for Eval including an oracle.
   This is only for use in the compiler proof. *)
Type eval_oracle_fun = ``: num -> compiler_args``

Datatype:
 eval_oracle_state =
  <|
    oracle : eval_oracle_fun ;
    custom_do_eval : v list -> eval_oracle_fun ->
         ((num # num) # eval_oracle_fun # dec list)option ;
    envs : ( ( v sem_env)list) list ;
    generation : num
  |>
End

Datatype:
  eval_state =
     EvalDecs eval_decs_state
   | EvalOracle eval_oracle_state
End

Datatype:
  state =
  <| clock : num
   ; refs  : v store
   ; ffi : 'ffi ffi_state
   ; next_type_stamp : num
   ; next_exn_stamp : num
   ; eval_state :  eval_state option
   |>
End

(* Other primitives *)
(* Check that a constructor is properly applied *)
(*val do_con_check : env_ctor -> maybe (id modN conN) -> nat -> bool*)
val _ = Define `
 ((do_con_check:((string),(string),(num#stamp))namespace ->(((string),(string))id)option -> num -> bool) cenv n_opt l=
   ((case n_opt of
      NONE => T
    | SOME n =>
        (case nsLookup cenv n of
            NONE => F
          | SOME (l',_) => l = l'
        )
  )))`;


(*val build_conv : env_ctor -> maybe (id modN conN) -> list v -> maybe v*)
val _ = Define `
 ((build_conv:((string),(string),(num#stamp))namespace ->(((string),(string))id)option ->(v)list ->(v)option) envC cn vs=
   ((case cn of
      NONE =>
        SOME (Conv NONE vs)
    | SOME id =>
        (case nsLookup envC id of
            NONE => NONE
          | SOME (len,stamp) => SOME (Conv (SOME stamp) vs)
        )
  )))`;


(*val lit_same_type : lit -> lit -> bool*)
val _ = Define `
 ((lit_same_type:lit -> lit -> bool) l1 l2=
   ((case (l1,l2) of
      (IntLit _, IntLit _) => T
    | (Char _, Char _) => T
    | (StrLit _, StrLit _) => T
    | (Word8 _, Word8 _) => T
    | (Word64 _, Word64 _) => T
    | _ => F
  )))`;


Datatype:
  match_result =
     No_match
   | Match_type_error
   | Match 'a
End

(*val same_type : stamp -> stamp -> bool*)
 val _ = Define `
 ((same_type:stamp -> stamp -> bool) (TypeStamp _ n1) (TypeStamp _ n2)=  (n1 = n2))
/\ ((same_type:stamp -> stamp -> bool) (ExnStamp _) (ExnStamp _)=  T)
/\ ((same_type:stamp -> stamp -> bool) _ _=  F)`;


(*val same_ctor : stamp -> stamp -> bool*)
val _ = Define `
 ((same_ctor:stamp -> stamp -> bool) stamp1 stamp2=  (stamp1 = stamp2))`;


(*val ctor_same_type : maybe stamp -> maybe stamp -> bool*)
val _ = Define `
 ((ctor_same_type:(stamp)option ->(stamp)option -> bool) c1 c2=
   ((case (c1,c2) of
      (NONE, NONE) => T
    | (SOME stamp1, SOME stamp2) => same_type stamp1 stamp2
    | _ => F
  )))`;


(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)
Definition pmatch_def:
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s Pany v' env=  (Match env))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Pvar x) v' env=  (Match ((x,v')::env)))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Plit l) (Litv l') env=
   (if l = l' then
    Match env
  else if lit_same_type l l' then
    No_match
  else
    Match_type_error))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Pcon (SOME n) ps) (Conv (SOME stamp') vs) env=
   ((case nsLookup envC n of
      SOME (l,stamp) =>
        if same_type stamp stamp' /\ (LENGTH ps = l) then
          if same_ctor stamp stamp' then
            if LENGTH vs = l then
              pmatch_list envC s ps vs env
            else
              Match_type_error
          else
            No_match
        else
          Match_type_error
    | _ => Match_type_error
  )))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Pcon NONE ps) (Conv NONE vs) env=
   (if LENGTH ps = LENGTH vs then
    pmatch_list envC s ps vs env
  else
    Match_type_error))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Pref p) (Loc lnum) env=
   ((case store_lookup lnum s of
      SOME (Refv v) => pmatch envC s p v env
    | SOME _ => Match_type_error
    | NONE => Match_type_error
  )))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Pas p i) v env=
   (pmatch envC s p v ((i,v)::env)))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC s (Ptannot p t) v env=
   (pmatch envC s p v env))
/\
((pmatch:((string),(string),(num#stamp))namespace ->((v)store_v)list -> pat -> v ->(string#v)list ->((string#v)list)match_result) envC _ _ _ env=  Match_type_error)
/\
((pmatch_list:((string),(string),(num#stamp))namespace ->((v)store_v)list ->(pat)list ->(v)list ->(string#v)list ->((string#v)list)match_result) envC s [] [] env=  (Match env))
/\
((pmatch_list:((string),(string),(num#stamp))namespace ->((v)store_v)list ->(pat)list ->(v)list ->(string#v)list ->((string#v)list)match_result) envC s (p::ps) (v::vs) env=
   ((case pmatch envC s p v env of
      Match_type_error => Match_type_error
    | Match env' => pmatch_list envC s ps vs env'
    | No_match =>
        (case pmatch_list envC s ps vs env of
            Match_type_error => Match_type_error
          | _ => No_match
        )
  )))
/\
((pmatch_list:((string),(string),(num#stamp))namespace ->((v)store_v)list ->(pat)list ->(v)list ->(string#v)list ->((string#v)list)match_result) envC s _ _ env=  Match_type_error)
Termination
  WF_REL_TAC
  `inv_image $< (λx. case x of INL (s,a,p,b,c) => pat_size p
                             | INR (s,a,ps,b,c) => list_size pat_size ps)`
End

Definition can_pmatch_all_def:
((can_pmatch_all:((modN),(conN),(num#stamp))namespace ->((v)store_v)list ->(pat)list -> v -> bool) envC refs [] v=  T)
/\
((can_pmatch_all:((modN),(conN),(num#stamp))namespace ->((v)store_v)list ->(pat)list -> v -> bool) envC refs (p::ps) v=
   (if pmatch envC refs p v [] = Match_type_error
  then F else can_pmatch_all envC refs ps v))
End

(* Bind each function of a mutually recursive set of functions to its closure *)
(*val build_rec_env : list (varN * varN * exp) -> sem_env v -> env_val -> env_val*)
val _ = Define `
 ((build_rec_env:(varN#varN#exp)list ->(v)sem_env ->((string),(string),(v))namespace ->((string),(string),(v))namespace) funs cl_env add_to_env=
   (FOLDR
    (\ (f,x,e) env' .  nsBind f (Recclosure cl_env funs f) env')
    add_to_env
    funs))`;


(* Lookup in the list of mutually recursive functions *)
(*val find_recfun : forall 'a 'b. varN -> list (varN * 'a * 'b) -> maybe ('a * 'b)*)
 val _ = Define `
 ((find_recfun:string ->(string#'a#'b)list ->('a#'b)option) n funs=
   ((case funs of
      [] => NONE
    | (f,x,e) :: funs =>
        if f = n then
          SOME (x,e)
        else
          find_recfun n funs
  )))`;


Datatype:
  eq_result =
     Eq_val bool
   | Eq_type_error
End

Definition do_eq_def:
((do_eq:v -> v -> eq_result) (Litv l1) (Litv l2)=
   (if lit_same_type l1 l2 then Eq_val (l1 = l2)
  else Eq_type_error))
/\
((do_eq:v -> v -> eq_result) (Loc l1) (Loc l2)=  (Eq_val (l1 = l2)))
/\
((do_eq:v -> v -> eq_result) (Conv cn1 vs1) (Conv cn2 vs2)=
   (if (cn1 = cn2) /\ (LENGTH vs1 = LENGTH vs2) then
    do_eq_list vs1 vs2
  else if ctor_same_type cn1 cn2 then
    Eq_val F
  else
    Eq_type_error))
/\
((do_eq:v -> v -> eq_result) (Vectorv vs1) (Vectorv vs2)=
   (if LENGTH vs1 = LENGTH vs2 then
    do_eq_list vs1 vs2
  else
    Eq_val F))
/\
((do_eq:v -> v -> eq_result) (Closure _ _ _) (Closure _ _ _)=  (Eq_val T))
/\
((do_eq:v -> v -> eq_result) (Closure _ _ _) (Recclosure _ _ _)=  (Eq_val T))
/\
((do_eq:v -> v -> eq_result) (Recclosure _ _ _) (Closure _ _ _)=  (Eq_val T))
/\
((do_eq:v -> v -> eq_result) (Recclosure _ _ _) (Recclosure _ _ _)=  (Eq_val T))
/\
((do_eq:v -> v -> eq_result) (Env _ (gen1, id1)) (Env _ (gen2, id2))=  (Eq_val ((gen1 = gen2) /\ (id1 = id2))))
/\
((do_eq:v -> v -> eq_result) _ _=  Eq_type_error)
/\
((do_eq_list:(v)list ->(v)list -> eq_result) [] []=  (Eq_val T))
/\
((do_eq_list:(v)list ->(v)list -> eq_result) (v1::vs1) (v2::vs2)=
   ((case do_eq v1 v2 of
      Eq_type_error => Eq_type_error
    | Eq_val r =>
        if ~ r then
          Eq_val F
        else
          do_eq_list vs1 vs2
  )))
/\
((do_eq_list:(v)list ->(v)list -> eq_result) _ _=  (Eq_val F))
Termination
  WF_REL_TAC `inv_image $< (λx. case x of INL (v1,v2) => v_size v1
                                        | INR (vs1,vs2) => list_size v_size vs1)`
End

(* Do an application *)
(*val do_opapp : list v -> maybe (sem_env v * exp)*)
val _ = Define `
 ((do_opapp:(v)list ->((v)sem_env#exp)option) vs=
   ((case vs of
    [Closure env n e; v] =>
      SOME (( env with<| v := (nsBind n v env.v) |>), e)
  | [Recclosure env funs n; v] =>
      if ALL_DISTINCT (MAP (\ (f,x,e) .  f) funs) then
        (case find_recfun n funs of
            SOME (n,e) => SOME (( env with<| v := (nsBind n v (build_rec_env funs env env.v)) |>), e)
          | NONE => NONE
        )
      else
        NONE
  | _ => NONE
  )))`;


(* If a value represents a list, get that list. Otherwise return Nothing *)
Definition v_to_list_def:
 ((v_to_list:v ->((v)list)option) (Conv (SOME stamp) [])=
   (if stamp = TypeStamp "[]" list_type_num then
    SOME []
  else
    NONE))
/\ ((v_to_list:v ->((v)list)option) (Conv (SOME stamp) [v1;v2])=
   (if stamp = TypeStamp "::" list_type_num then
    (case v_to_list v2 of
        SOME vs => SOME (v1::vs)
      | NONE => NONE
    )
  else
    NONE))
/\ ((v_to_list:v ->((v)list)option) _=  NONE)
End

Definition list_to_v_def:
 ((list_to_v:(v)list -> v) []=  (Conv (SOME (TypeStamp "[]" list_type_num)) []))
/\ ((list_to_v:(v)list -> v) (x::xs)=  (Conv (SOME (TypeStamp "::" list_type_num)) [x; list_to_v xs]))
End

Definition v_to_char_list_def:
 ((v_to_char_list:v ->((char)list)option) (Conv (SOME stamp) [])=
   (if stamp = TypeStamp "[]" list_type_num then
    SOME []
  else
    NONE))
/\ ((v_to_char_list:v ->((char)list)option) (Conv (SOME stamp) [Litv (Char c);v])=
   (if stamp = TypeStamp "::" list_type_num then
    (case v_to_char_list v of
        SOME cs => SOME (c::cs)
      | NONE => NONE
    )
  else
    NONE))
/\ ((v_to_char_list:v ->((char)list)option) _=  NONE)
End

Definition vs_to_string_def:
 ((vs_to_string:(v)list ->(string)option) []=  (SOME ""))
/\ ((vs_to_string:(v)list ->(string)option) (Litv(StrLit s1)::vs)=
   ((case vs_to_string vs of
    SOME s2 => SOME ( STRCAT s1 s2)
  | _ => NONE
  )))
/\ ((vs_to_string:(v)list ->(string)option) _=  NONE)
End

(*val maybe_to_v : maybe v -> v*)
 val _ = Define `
 ((maybe_to_v:(v)option -> v) NONE=
   (Conv (SOME (TypeStamp "None" option_type_num)) []))
/\ ((maybe_to_v:(v)option -> v) (SOME v)=
   (Conv (SOME (TypeStamp "Some" option_type_num)) [v]))`;


(*val v_to_id : v -> maybe (id modN varN)*)
 val _ = Define `
 ((v_to_id:v ->(((string),(string))id)option) (Conv (SOME stamp) [Litv (StrLit s)])=
   (if stamp = TypeStamp "Short" id_type_num then
    SOME (Short s)
  else
    NONE))
/\ ((v_to_id:v ->(((string),(string))id)option) (Conv (SOME stamp) [Litv (StrLit s); v])=
   (if stamp = TypeStamp "Long" id_type_num then
    (case v_to_id v of
        SOME id => SOME (Long s id)
      | NONE => NONE
    )
  else
    NONE))
/\ ((v_to_id:v ->(((string),(string))id)option) _=  NONE)`;


(*val enc_pair : v -> v -> v*)
val _ = Define `
 ((enc_pair:v -> v -> v) v1 v2=  (Conv NONE [v1; v2]))`;


Definition enc_list_def:
  ((enc_list:(v)list -> v) []=
     (Conv (SOME (TypeStamp "[]" list_type_num)) []))
/\
  ((enc_list:(v)list -> v) (x::xs)=
     (Conv (SOME (TypeStamp "::" list_type_num)) [x; enc_list xs]))
End

(*val enc_option : maybe v -> v*)
 val _ = Define `

  ((enc_option:(v)option -> v) NONE=
     (Conv (SOME (TypeStamp "None" option_type_num)) []))
/\
  ((enc_option:(v)option -> v) (SOME x)=
     (Conv (SOME (TypeStamp "Some" option_type_num)) [x]))`;


(*val enc_lit : lit -> v*)
 val _ = Define `

  ((enc_lit:lit -> v) (Word64 w)=
     (Conv (SOME (TypeStamp "Word64" lit_type_num)) [Litv (Word64 w)]))
/\
  ((enc_lit:lit -> v) (Word8 b)=
     (Conv (SOME (TypeStamp "Word8" lit_type_num)) [Litv (Word8 b)]))
/\
  ((enc_lit:lit -> v) (StrLit s)=
     (Conv (SOME (TypeStamp "Strlit" lit_type_num)) [Litv (StrLit s)]))
/\
  ((enc_lit:lit -> v) (Char c)=
     (Conv (SOME (TypeStamp "Char" lit_type_num)) [Litv (Char c)]))
/\
  ((enc_lit:lit -> v) (IntLit i)=
     (Conv (SOME (TypeStamp "Intlit" lit_type_num)) [Litv (IntLit i)]))`;


Definition enc_id_def:
  ((enc_id:((string),(string))id -> v) (Short s)=
     (Conv (SOME (TypeStamp "Short" id_type_num)) [Litv (StrLit s)]))
/\
  ((enc_id:((string),(string))id -> v) (Long s i)=
     (Conv (SOME (TypeStamp "Long" id_type_num)) [Litv (StrLit s); enc_id i]))
End

Definition enc_ast_t_def:
  ((enc_ast_t:ast_t -> v) (Atapp x y)=
     (Conv (SOME (TypeStamp "Atapp" ast_t_type_num))
      [enc_list (MAP enc_ast_t x); enc_id y]))
/\
  ((enc_ast_t:ast_t -> v) (Attup x)=
     (Conv (SOME (TypeStamp "Attup" ast_t_type_num))
      [enc_list (MAP enc_ast_t x)]))
/\
  ((enc_ast_t:ast_t -> v) (Atfun x_3 x_2)=
     (Conv (SOME (TypeStamp "Atfun" ast_t_type_num))
      [enc_ast_t x_3; enc_ast_t x_2]))
/\
  ((enc_ast_t:ast_t -> v) (Atvar x_1)=
     (Conv (SOME (TypeStamp "Atvar" ast_t_type_num)) [Litv (StrLit x_1)]))
Termination
  WF_REL_TAC `measure ast_t_size`
End

Definition enc_pat_def:
  ((enc_pat:pat -> v) (Ptannot x_9 x_8)=
     (Conv (SOME (TypeStamp "Ptannot" pat_type_num))
      [enc_pat x_9; enc_ast_t x_8]))
/\
  ((enc_pat:pat -> v) (Pref x_7)=
     (Conv (SOME (TypeStamp "Pref" pat_type_num))
      [enc_pat x_7]))
/\
  ((enc_pat:pat -> v) (Pas x_6 x_5)=
     (Conv (SOME (TypeStamp "Pas" pat_type_num))
      [enc_pat x_6; Litv (StrLit x_5)]))
/\
  ((enc_pat:pat -> v) (Pcon x_4 x_3)=
     (Conv (SOME (TypeStamp "Pcon" pat_type_num))
      [enc_option (OPTION_MAP enc_id x_4); enc_list (MAP enc_pat x_3)]))
/\
  ((enc_pat:pat -> v) (Plit x_2)=
     (Conv (SOME (TypeStamp "Plit" pat_type_num))
      [enc_lit x_2]))
/\
  ((enc_pat:pat -> v) (Pvar x_1)=
     (Conv (SOME (TypeStamp "Pvar" pat_type_num))
      [Litv (StrLit x_1)]))
/\
  ((enc_pat:pat -> v) Pany=
     (Conv (SOME (TypeStamp "Pany" pat_type_num)) []))
Termination
  WF_REL_TAC ‘measure pat_size’
End

(*val enc_lop : lop -> v*)
 val _ = Define `

  ((enc_lop:lop -> v) Or=  (Conv (SOME (TypeStamp "Or" lop_type_num)) []))
/\
  ((enc_lop:lop -> v) And=  (Conv (SOME (TypeStamp "And" lop_type_num)) []))`;


(*val enc_opn : opn -> v*)
 val _ = Define `

  ((enc_opn:opn -> v) Modulo=  (Conv (SOME (TypeStamp "Modulo" opn_type_num)) []))
/\
  ((enc_opn:opn -> v) Divide=  (Conv (SOME (TypeStamp "Divide" opn_type_num)) []))
/\
  ((enc_opn:opn -> v) Times=  (Conv (SOME (TypeStamp "Times" opn_type_num)) []))
/\
  ((enc_opn:opn -> v) Minus=  (Conv (SOME (TypeStamp "Minus" opn_type_num)) []))
/\
  ((enc_opn:opn -> v) Plus=  (Conv (SOME (TypeStamp "Plus" opn_type_num)) []))`;


(*val enc_opb : opb -> v*)
 val _ = Define `

  ((enc_opb:opb -> v) Geq=  (Conv (SOME (TypeStamp "Geq" opb_type_num)) []))
/\
  ((enc_opb:opb -> v) Leq=  (Conv (SOME (TypeStamp "Leq" opb_type_num)) []))
/\
  ((enc_opb:opb -> v) Gt=  (Conv (SOME (TypeStamp "Gt" opb_type_num)) []))
/\
  ((enc_opb:opb -> v) Lt=  (Conv (SOME (TypeStamp "Lt" opb_type_num)) []))`;


(*val enc_opw : opw -> v*)
 val _ = Define `

  ((enc_opw:opw -> v) Sub=  (Conv (SOME (TypeStamp "Sub" opw_type_num)) []))
/\
  ((enc_opw:opw -> v) Add=  (Conv (SOME (TypeStamp "Add" opw_type_num)) []))
/\
  ((enc_opw:opw -> v) Xor=  (Conv (SOME (TypeStamp "Xor" opw_type_num)) []))
/\
  ((enc_opw:opw -> v) Orw=  (Conv (SOME (TypeStamp "Orw" opw_type_num)) []))
/\
  ((enc_opw:opw -> v) Andw=  (Conv (SOME (TypeStamp "Andw" opw_type_num)) []))`;


(*val enc_shift : shift -> v*)
 val _ = Define `

  ((enc_shift:shift -> v) Ror=  (Conv (SOME (TypeStamp "Ror" shift_type_num)) []))
/\
  ((enc_shift:shift -> v) Asr=  (Conv (SOME (TypeStamp "Asr" shift_type_num)) []))
/\
  ((enc_shift:shift -> v) Lsr=  (Conv (SOME (TypeStamp "Lsr" shift_type_num)) []))
/\
  ((enc_shift:shift -> v) Lsl=  (Conv (SOME (TypeStamp "Lsl" shift_type_num)) []))`;


(*val enc_word_size : word_size -> v*)
 val _ = Define `

  ((enc_word_size:word_size -> v) W64=  (Conv (SOME (TypeStamp "W64" word_size_type_num)) []))
/\
  ((enc_word_size:word_size -> v) W8=  (Conv (SOME (TypeStamp "W8" word_size_type_num)) []))`;


(*val enc_fp_uop : fp_uop -> v*)
 val _ = Define `

  ((enc_fp_uop:fp_uop -> v) FP_Sqrt=  (Conv (SOME (TypeStamp "Fp_sqrt" fp_uop_type_num)) []))
/\
  ((enc_fp_uop:fp_uop -> v) FP_Neg=  (Conv (SOME (TypeStamp "Fp_neg" fp_uop_type_num)) []))
/\
  ((enc_fp_uop:fp_uop -> v) FP_Abs=  (Conv (SOME (TypeStamp "Fp_abs" fp_uop_type_num)) []))`;


(*val enc_fp_bop : fp_bop -> v*)
 val _ = Define `

  ((enc_fp_bop:fp_bop -> v) FP_Div=  (Conv (SOME (TypeStamp "Fp_div" fp_bop_type_num)) []))
/\
  ((enc_fp_bop:fp_bop -> v) FP_Mul=  (Conv (SOME (TypeStamp "Fp_mul" fp_bop_type_num)) []))
/\
  ((enc_fp_bop:fp_bop -> v) FP_Sub=  (Conv (SOME (TypeStamp "Fp_sub" fp_bop_type_num)) []))
/\
  ((enc_fp_bop:fp_bop -> v) FP_Add=  (Conv (SOME (TypeStamp "Fp_add" fp_bop_type_num)) []))`;


(*val enc_fp_top : fp_top -> v*)
 val _ = Define `

  ((enc_fp_top:fp_top -> v) FP_Fma=  (Conv (SOME (TypeStamp "Fp_fma" fp_top_type_num)) []))`;


(*val enc_fp_cmp : fp_cmp -> v*)
 val _ = Define `

  ((enc_fp_cmp:fp_cmp -> v) FP_Equal=
     (Conv (SOME (TypeStamp "Fp_equal" fp_cmp_type_num)) []))
/\
  ((enc_fp_cmp:fp_cmp -> v) FP_GreaterEqual=
     (Conv (SOME (TypeStamp "Fp_greaterequal" fp_cmp_type_num)) []))
/\
  ((enc_fp_cmp:fp_cmp -> v) FP_Greater=
     (Conv (SOME (TypeStamp "Fp_greater" fp_cmp_type_num)) []))
/\
  ((enc_fp_cmp:fp_cmp -> v) FP_LessEqual=
     (Conv (SOME (TypeStamp "Fp_lessequal" fp_cmp_type_num)) []))
/\
  ((enc_fp_cmp:fp_cmp -> v) FP_Less=
     (Conv (SOME (TypeStamp "Fp_less" fp_cmp_type_num)) []))`;


(*val nat_to_v : nat -> v*)
val _ = Define `
 ((nat_to_v:num -> v) n=  (Litv (IntLit (int_of_num n))))`;


(*val enc_op : op -> v*)
 val _ = Define `

  ((enc_op:op -> v) Eval=  (Conv (SOME (TypeStamp "Eval" op_type_num)) []))
/\
  ((enc_op:op -> v) Env_id=  (Conv (SOME (TypeStamp "Env_id" op_type_num)) []))
/\
  ((enc_op:op -> v) (FFI x_15)=
     (Conv (SOME (TypeStamp "Ffi" op_type_num)) [Litv (StrLit x_15)]))
/\
  ((enc_op:op -> v) ConfigGC=  (Conv (SOME (TypeStamp "Configgc" op_type_num)) []))
/\
  ((enc_op:op -> v) ListAppend=  (Conv (SOME (TypeStamp "Listappend" op_type_num)) []))
/\
  ((enc_op:op -> v) Aupdate=  (Conv (SOME (TypeStamp "Aupdate" op_type_num)) []))
/\
  ((enc_op:op -> v) Alength=  (Conv (SOME (TypeStamp "Alength" op_type_num)) []))
/\
  ((enc_op:op -> v) Asub=  (Conv (SOME (TypeStamp "Asub" op_type_num)) []))
/\
  ((enc_op:op -> v) AallocEmpty=  (Conv (SOME (TypeStamp "Aallocempty" op_type_num)) []))
/\
  ((enc_op:op -> v) Aalloc=  (Conv (SOME (TypeStamp "Aalloc" op_type_num)) []))
/\
  ((enc_op:op -> v) Aupdate_unsafe=
     (Conv (SOME (TypeStamp "Aupdate_unsafe" op_type_num)) []))
/\
  ((enc_op:op -> v) Asub_unsafe=  (Conv (SOME (TypeStamp "Asub_unsafe" op_type_num)) []))
/\
  ((enc_op:op -> v) Vlength=  (Conv (SOME (TypeStamp "Vlength" op_type_num)) []))
/\
  ((enc_op:op -> v) Vsub=  (Conv (SOME (TypeStamp "Vsub" op_type_num)) []))
/\
  ((enc_op:op -> v) VfromList=  (Conv (SOME (TypeStamp "Vfromlist" op_type_num)) []))
/\
  ((enc_op:op -> v) Strcat=  (Conv (SOME (TypeStamp "Strcat" op_type_num)) []))
/\
  ((enc_op:op -> v) Strlen=  (Conv (SOME (TypeStamp "Strlen" op_type_num)) []))
/\
  ((enc_op:op -> v) Strsub=  (Conv (SOME (TypeStamp "Strsub" op_type_num)) []))
/\
  ((enc_op:op -> v) Explode=  (Conv (SOME (TypeStamp "Explode" op_type_num)) []))
/\
  ((enc_op:op -> v) Implode=  (Conv (SOME (TypeStamp "Implode" op_type_num)) []))
/\
  ((enc_op:op -> v) (Chopb x_14)=
     (Conv (SOME (TypeStamp "Chopb" op_type_num)) [enc_opb x_14]))
/\
  ((enc_op:op -> v) Chr=  (Conv (SOME (TypeStamp "Chr_1" op_type_num)) []))
/\
  ((enc_op:op -> v) Ord=  (Conv (SOME (TypeStamp "Ord" op_type_num)) []))
/\
  ((enc_op:op -> v) CopyAw8Aw8=  (Conv (SOME (TypeStamp "Copyaw8aw8" op_type_num)) []))
/\
  ((enc_op:op -> v) CopyAw8Str=  (Conv (SOME (TypeStamp "Copyaw8str" op_type_num)) []))
/\
  ((enc_op:op -> v) CopyStrAw8=  (Conv (SOME (TypeStamp "Copystraw8" op_type_num)) []))
/\
  ((enc_op:op -> v) CopyStrStr=  (Conv (SOME (TypeStamp "Copystrstr" op_type_num)) []))
/\
  ((enc_op:op -> v) (WordToInt x_13)=
     (Conv (SOME (TypeStamp "Wordtoint" op_type_num)) [enc_word_size x_13]))
/\
  ((enc_op:op -> v) (WordFromInt x_12)=
     (Conv (SOME (TypeStamp "Wordfromint" op_type_num)) [enc_word_size x_12]))
/\
  ((enc_op:op -> v) Aw8update=  (Conv (SOME (TypeStamp "Aw8update" op_type_num)) []))
/\
  ((enc_op:op -> v) Aw8length=  (Conv (SOME (TypeStamp "Aw8length" op_type_num)) []))
/\
  ((enc_op:op -> v) Aw8sub=  (Conv (SOME (TypeStamp "Aw8sub" op_type_num)) []))
/\
  ((enc_op:op -> v) Aw8alloc=  (Conv (SOME (TypeStamp "Aw8alloc" op_type_num)) []))
/\
  ((enc_op:op -> v) Aw8sub_unsafe=  (Conv (SOME (TypeStamp "Aw8sub_unsafe" op_type_num)) []))
/\
  ((enc_op:op -> v) Aw8update_unsafe=
     (Conv (SOME (TypeStamp "Aw8update_unsafe" op_type_num)) []))
/\
  ((enc_op:op -> v) Opderef=  (Conv (SOME (TypeStamp "Opderef" op_type_num)) []))
/\
  ((enc_op:op -> v) Opref=  (Conv (SOME (TypeStamp "Opref" op_type_num)) []))
/\
  ((enc_op:op -> v) Opassign=  (Conv (SOME (TypeStamp "Opassign" op_type_num)) []))
/\
  ((enc_op:op -> v) Opapp=  (Conv (SOME (TypeStamp "Opapp" op_type_num)) []))
/\
  ((enc_op:op -> v) (FP_top x_11)=
     (Conv (SOME (TypeStamp "Fp_top" op_type_num)) [enc_fp_top x_11]))
/\
  ((enc_op:op -> v) (FP_bop x_10)=
     (Conv (SOME (TypeStamp "Fp_bop" op_type_num)) [enc_fp_bop x_10]))
/\
  ((enc_op:op -> v) (FP_uop x_9)=
     (Conv (SOME (TypeStamp "Fp_uop" op_type_num)) [enc_fp_uop x_9]))
/\
  ((enc_op:op -> v) (FP_cmp x_8)=
     (Conv (SOME (TypeStamp "Fp_cmp" op_type_num)) [enc_fp_cmp x_8]))
/\
  ((enc_op:op -> v) Equality=  (Conv (SOME (TypeStamp "Equality" op_type_num)) []))
/\
  ((enc_op:op -> v) (Shift x_7 x_6 x_5)=
     (Conv (SOME (TypeStamp "Shift" op_type_num))
      [enc_word_size x_7; enc_shift x_6; nat_to_v x_5]))
/\
  ((enc_op:op -> v) (Opw x_4 x_3)=
     (Conv (SOME (TypeStamp "Opw" op_type_num)) [enc_word_size x_4; enc_opw x_3]))
/\
  ((enc_op:op -> v) (Opb x_2)=
     (Conv (SOME (TypeStamp "Opb" op_type_num)) [enc_opb x_2]))
/\
  ((enc_op:op -> v) (Opn x_1)=
     (Conv (SOME (TypeStamp "Opn" op_type_num)) [enc_opn x_1]))`;



Definition maybe_all_list_def:
 ((maybe_all_list:('a option)list ->('a list)option) v=
   ((case v of
    [] => SOME []
  | (NONE :: _) => NONE
  | (SOME x :: vs) => (case maybe_all_list vs of
      SOME xs => SOME (x :: xs)
    | NONE => NONE
    )
  )))
End

(*val v_to_word8 : v -> maybe word8*)
val _ = Define `
 ((v_to_word8:v ->(word8)option) v=  ((case v of
    Litv (Word8 w) => SOME w
  | _ => NONE
  )))`;


(*val v_to_word8_list : v -> maybe (list word8)*)
val _ = Define `
 ((v_to_word8_list:v ->((word8)list)option) v=  ((case v_to_list v of
    SOME xs => maybe_all_list (MAP v_to_word8 xs)
  | NONE => NONE
  )))`;


(*val v_to_word64 : v -> maybe word64*)
val _ = Define `
 ((v_to_word64:v ->(word64)option) v=  ((case v of
    Litv (Word64 w) => SOME w
  | _ => NONE
  )))`;


(*val v_to_word64_list : v -> maybe (list word64)*)
val _ = Define `
 ((v_to_word64_list:v ->((word64)list)option) v=  ((case v_to_list v of
    SOME xs => maybe_all_list (MAP v_to_word64 xs)
  | NONE => NONE
  )))`;


(*val lookup_env : eval_oracle_state -> (nat * nat) -> maybe (sem_env v)*)
val _ = Define `
 ((lookup_env:eval_oracle_state -> num#num ->((v)sem_env)option) s (i, j)=  ((case oEL i s.envs of
    NONE => NONE
  | SOME gen_envs => oEL j gen_envs
  )))`;


(*val add_decs_generation : eval_decs_state -> eval_decs_state*)
val _ = Define `
 ((add_decs_generation:eval_decs_state -> eval_decs_state) s=  ((case s.env_id_counter of
    (cur_gen, next_id, next_gen) => ( s with<| env_id_counter :=
        (next_gen,( 0 : num), (next_gen +( 1 : num))) |>)
  )))`;


(*val add_env_generation : eval_oracle_state -> eval_oracle_state*)
val _ = Define `
 ((add_env_generation:eval_oracle_state -> eval_oracle_state) s=  (( s with<|
    generation := (LENGTH s.envs) ;
    envs := ((++) (s.envs) ([[]])) |>)))`;


(*val declare_env : maybe eval_state -> sem_env v -> maybe (v * maybe eval_state)*)
val _ = Define `
 ((declare_env:(eval_state)option ->(v)sem_env ->(v#(eval_state)option)option) es env=  ((case es of
    NONE => NONE
  | SOME (EvalDecs s) => (case s.env_id_counter of
      (cur_gen, next_id, next_gen) => SOME (Env env (cur_gen, next_id),
        SOME (EvalDecs ( s with<| env_id_counter :=
            (cur_gen, (next_id +( 1 : num)), next_gen) |>)))
    )
  | SOME (EvalOracle s) => (case (oEL s.generation s.envs) of
      SOME gen_envs => SOME (Conv NONE
            [nat_to_v s.generation; nat_to_v (LENGTH gen_envs)],
        SOME (EvalOracle ( s with<| envs := (LUPDATE ((++) gen_envs ([env])) s.generation s.envs) |>)))
    | NONE => NONE
    )
  )))`;


(* Concrete, or first-order values, which do not contain code closures and
   are unchanged by many compiler phases. *)
Definition concrete_v_def:
 ((concrete_v:v -> bool) v=  ((case v of
    Litv _ => T
  | Loc _ => T
  | Vectorv vs => concrete_v_list vs
  | Conv _ vs => concrete_v_list vs
  | _ => F
  )))
/\
  ((concrete_v_list:(v)list -> bool) []=  T)
/\
  ((concrete_v_list:(v)list -> bool) (v :: vs)=  (concrete_v v /\ concrete_v_list vs))
Termination
  WF_REL_TAC `measure (λx. case x of INL v => v_size v
                                   | INR vs => list_size v_size vs)`
End

(*val compiler_agrees : compiler_fun -> compiler_args -> v * v * v -> bool*)
val _ = Define `
 ((compiler_agrees:((num#num)#v#(dec)list ->(v#(word8)list#(word64)list)option) ->(num#num)#v#(dec)list -> v#v#v -> bool) f args (st_v, bs_v, ws_v)=  ((case
    (f args, args, v_to_word8_list bs_v, v_to_word64_list ws_v)
  of
    (SOME (st, c_bs, c_ws), (_, prev_st_v, _), SOME bs, SOME ws) =>
    (st = st_v) /\ (c_bs = bs) /\ (c_ws = ws) /\ concrete_v st_v /\
        concrete_v prev_st_v
  | _ => F
  )))`;


(* get the declarations to be evaluated in the various Eval semantics *)
(*val do_eval : list v -> maybe eval_state ->
        maybe (sem_env v * list dec * maybe eval_state)*)
val _ = Define `
 ((do_eval:(v)list ->(eval_state)option ->((v)sem_env#(dec)list#(eval_state)option)option) vs es=
   ((case (es, vs) of
    (SOME (EvalDecs s), [Env env id; st_v; decs_v; st_v2; bs_v; ws_v]) =>
    (case s.decode_decs decs_v of
      SOME decs => if (st_v = s.compiler_state) /\ concrete_v decs_v /\
            compiler_agrees s.compiler (id, st_v, decs) (st_v2, bs_v, ws_v)
        then SOME (env, decs, SOME (EvalDecs
            (add_decs_generation ( s with<| compiler_state := st_v2 |>))))
        else NONE
    | _ => NONE
    )
  | (SOME (EvalOracle s), vs) => (case s.custom_do_eval vs s.oracle of
      SOME (env_id, oracle, decs) => (case lookup_env s env_id of
        SOME env => SOME (env, decs, SOME (EvalOracle
            (add_env_generation ( s with<| oracle := oracle |>))))
      | _ => NONE
      )
    | _ => NONE
    )
  | _ => NONE
  )))`;


(* conclude an Eval generation *)
(*val reset_env_generation : maybe eval_state -> maybe eval_state -> maybe eval_state*)
val _ = Define `
 ((reset_env_generation:(eval_state)option ->(eval_state)option ->(eval_state)option) prior_es es=  ((case (prior_es, es) of
    (SOME (EvalOracle prior_s), SOME (EvalOracle s)) =>
    SOME (EvalOracle ( s with<| generation := (prior_s.generation) |>))
  | (SOME (EvalDecs prior_s), SOME (EvalDecs s)) => (case
        (prior_s.env_id_counter, s.env_id_counter) of
      ((cur_gen, next_id, _), (_, _, next_gen)) =>
    SOME (EvalDecs ( s with<| env_id_counter := (cur_gen, next_id, next_gen) |>))
    )
  | _ => es
  )))`;


(*val copy_array : forall 'a. list 'a * integer -> integer -> maybe (list 'a * integer) -> maybe (list 'a)*)
val _ = Define `
 ((copy_array:'a list#int -> int ->('a list#int)option ->('a list)option) (src,srcoff) len d=
   (if (srcoff <( 0 : int)) \/ ((len <( 0 : int)) \/ (LENGTH src < Num (ABS (I (srcoff + len))))) then NONE else
    let copied = (TAKE (Num (ABS (I len))) (DROP (Num (ABS (I srcoff))) src)) in
    (case d of
      SOME (dst,dstoff) =>
        if (dstoff <( 0 : int)) \/ (LENGTH dst < Num (ABS (I (dstoff + len)))) then NONE else
          SOME ((TAKE (Num (ABS (I dstoff))) dst ++
                copied) ++
                DROP (Num (ABS (I (dstoff + len)))) dst)
    | NONE => SOME copied
    )))`;


(*val ws_to_chars : list word8 -> list char*)
val _ = Define `
 ((ws_to_chars:(word8)list ->(char)list) ws=  (MAP (\ w .  CHR(w2n w)) ws))`;


(*val chars_to_ws : list char -> list word8*)
val _ = Define `
 ((chars_to_ws:(char)list ->(word8)list) cs=  (MAP (\ c .  i2w(int_of_num(ORD c))) cs))`;


(*val opn_lookup : opn -> integer -> integer -> integer*)
val _ = Define `
 ((opn_lookup:opn -> int -> int -> int) n : int -> int -> int=  ((case n of
    Plus => (+)
  | Minus => (-)
  | Times => ( * )
  | Divide => (/)
  | Modulo => (%)
)))`;


(*val opb_lookup : opb -> integer -> integer -> bool*)
val _ = Define `
 ((opb_lookup:opb -> int -> int -> bool) n : int -> int -> bool=  ((case n of
    Lt => (<)
  | Gt => (>)
  | Leq => (<=)
  | Geq => (>=)
)))`;


(*val opw8_lookup : opw -> word8 -> word8 -> word8*)
val _ = Define `
 ((opw8_lookup:opw -> word8 -> word8 -> word8) op=  ((case op of
    Andw => word_and
  | Orw => word_or
  | Xor => word_xor
  | Add => word_add
  | Sub => word_sub
)))`;


(*val opw64_lookup : opw -> word64 -> word64 -> word64*)
val _ = Define `
 ((opw64_lookup:opw -> word64 -> word64 -> word64) op=  ((case op of
    Andw => word_and
  | Orw => word_or
  | Xor => word_xor
  | Add => word_add
  | Sub => word_sub
)))`;


(*val shift8_lookup : shift -> word8 -> nat -> word8*)
val _ = Define `
 ((shift8_lookup:shift -> word8 -> num -> word8) sh=  ((case sh of
    Lsl => word_lsl
  | Lsr => word_lsr
  | Asr => word_asr
  | Ror => word_ror
)))`;


(*val shift64_lookup : shift -> word64 -> nat -> word64*)
val _ = Define `
 ((shift64_lookup:shift -> word64 -> num -> word64) sh=  ((case sh of
    Lsl => word_lsl
  | Lsr => word_lsr
  | Asr => word_asr
  | Ror => word_ror
)))`;


(*val Boolv : bool -> v*)
val _ = Define `
 ((Boolv:bool -> v) b=  (if b
  then Conv (SOME (TypeStamp "True" bool_type_num)) []
  else Conv (SOME (TypeStamp "False" bool_type_num)) []))`;


Datatype:
  exp_or_val = Exp exp | Val v
End

Type store_ffi = ``: 'v store # 'ffi ffi_state``

(*val do_app : forall 'ffi. store_ffi 'ffi v -> op -> list v -> maybe (store_ffi 'ffi v * result v v)*)
val _ = Define `
 ((do_app:((v)store_v)list#'ffi ffi_state -> op ->(v)list ->((((v)store_v)list#'ffi ffi_state)#((v),(v))result)option) ((s: v store),(t: 'ffi ffi_state)) op vs=
   ((case (op, vs) of
      (ListAppend, [x1; x2]) =>
      (case (v_to_list x1, v_to_list x2) of
          (SOME xs, SOME ys) => SOME ((s,t), Rval (list_to_v (xs ++ ys)))
        | _ => NONE
      )
    | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 =( 0 : int)) then
          SOME ((s,t), Rerr (Rraise div_exn_v))
        else
          SOME ((s,t), Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME ((s,t), Rval (Boolv (opb_lookup op n1 n2)))
    | (Opw W8 op, [Litv (Word8 w1); Litv (Word8 w2)]) =>
        SOME ((s,t), Rval (Litv (Word8 (opw8_lookup op w1 w2))))
    | (Opw W64 op, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME ((s,t), Rval (Litv (Word64 (opw64_lookup op w1 w2))))
    | (FP_top t_op, [Litv (Word64 w1); Litv (Word64 w2); Litv (Word64 w3)]) =>
        SOME ((s,t), Rval (Litv (Word64 (fp_top t_op w1 w2 w3))))
    | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME ((s,t),Rval (Litv (Word64 (fp_bop bop w1 w2))))
    | (FP_uop uop, [Litv (Word64 w)]) =>
        SOME ((s,t),Rval (Litv (Word64 (fp_uop uop w))))
    | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME ((s,t),Rval (Boolv (fp_cmp cmp w1 w2)))
    | (Shift W8 op n, [Litv (Word8 w)]) =>
        SOME ((s,t), Rval (Litv (Word8 (shift8_lookup op w n))))
    | (Shift W64 op n, [Litv (Word64 w)]) =>
        SOME ((s,t), Rval (Litv (Word64 (shift64_lookup op w n))))
    | (Equality, [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME ((s,t), Rval (Boolv b))
        )
    | (Opassign, [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s of
            SOME s' => SOME ((s',t), Rval (Conv NONE []))
          | NONE => NONE
        )
    | (Opref, [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME ((s',t), Rval (Loc n))
    | (Opderef, [Loc n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME ((s,t),Rval v)
          | _ => NONE
        )
    | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let (s',lnum) =
            (store_alloc (W8array (REPLICATE (Num (ABS (I n))) w)) s)
          in
            SOME ((s',t), Rval (Loc lnum))
    | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME ((s,t), Rerr (Rraise sub_exn_v))
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    SOME ((s,t), Rerr (Rraise sub_exn_v))
                  else
                    SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8sub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    NONE
                  else
                    SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8length, [Loc n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  SOME ((s,t), Rerr (Rraise sub_exn_v))
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aw8update_unsafe, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  NONE
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (WordFromInt W8, [Litv(IntLit i)]) =>
        SOME ((s,t), Rval (Litv (Word8 (i2w i))))
    | (WordFromInt W64, [Litv(IntLit i)]) =>
        SOME ((s,t), Rval (Litv (Word64 (i2w i))))
    | (WordToInt W8, [Litv (Word8 w)]) =>
        SOME ((s,t), Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (WordToInt W64, [Litv (Word64 w)]) =>
        SOME ((s,t), Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (CopyStrStr, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len)]) =>
        SOME ((s,t),
        (case copy_array (EXPLODE str,off) len NONE of
          NONE => Rerr (Rraise sub_exn_v)
        | SOME cs => Rval (Litv(StrLit(IMPLODE(cs))))
        ))
    | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
        (case store_lookup dst s of
          SOME (W8array ws) =>
            (case copy_array (EXPLODE str,off) len (SOME(ws_to_chars ws,dstoff)) of
              NONE => SOME ((s,t), Rerr (Rraise sub_exn_v))
            | SOME cs =>
              (case store_assign dst (W8array (chars_to_ws cs)) s of
                SOME s' =>  SOME ((s',t), Rval (Conv NONE []))
              | _ => NONE
              )
            )
        | _ => NONE
        )
    | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
      (case store_lookup src s of
        SOME (W8array ws) =>
        SOME ((s,t),
          (case copy_array (ws,off) len NONE of
            NONE => Rerr (Rraise sub_exn_v)
          | SOME ws => Rval (Litv(StrLit(IMPLODE(ws_to_chars ws))))
          ))
      | _ => NONE
      )
    | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
      (case (store_lookup src s, store_lookup dst s) of
        (SOME (W8array ws), SOME (W8array ds)) =>
          (case copy_array (ws,off) len (SOME(ds,dstoff)) of
            NONE => SOME ((s,t), Rerr (Rraise sub_exn_v))
          | SOME ws =>
              (case store_assign dst (W8array ws) s of
                SOME s' => SOME ((s',t), Rval (Conv NONE []))
              | _ => NONE
              )
          )
      | _ => NONE
      )
    | (Ord, [Litv (Char c)]) =>
          SOME ((s,t), Rval (Litv(IntLit(int_of_num(ORD c)))))
    | (Chr, [Litv (IntLit i)]) =>
        SOME ((s,t),
          (if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rerr (Rraise chr_exn_v)
          else
            Rval (Litv(Char(CHR(Num (ABS (I i))))))))
    | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
        SOME ((s,t), Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
    | (Implode, [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME ((s,t), Rval (Litv (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Explode, [v]) =>
          (case v of
            Litv (StrLit str) =>
              SOME ((s,t), Rval (list_to_v (MAP (\ c .  Litv (Char c)) (EXPLODE str))))
          | _ => NONE
          )
    | (Strsub, [Litv (StrLit str); Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n = (Num (ABS (I i))) in
            if n >= STRLEN str then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              SOME ((s,t), Rval (Litv (Char (EL n (EXPLODE str)))))
    | (Strlen, [Litv (StrLit str)]) =>
        SOME ((s,t), Rval (Litv(IntLit(int_of_num(STRLEN str)))))
    | (Strcat, [v]) =>
        (case v_to_list v of
          SOME vs =>
            (case vs_to_string vs of
              SOME str =>
                SOME ((s,t), Rval (Litv(StrLit str)))
            | _ => NONE
            )
        | _ => NONE
        )
    | (VfromList, [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME ((s,t), Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n = (Num (ABS (I i))) in
            if n >= LENGTH vs then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              SOME ((s,t), Rval (EL n vs))
    | (Vlength, [Vectorv vs]) =>
        SOME ((s,t), Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Aalloc, [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME ((s,t), Rerr (Rraise sub_exn_v))
        else
          let (s',lnum) =
            (store_alloc (Varray (REPLICATE (Num (ABS (I n))) v)) s)
          in
            SOME ((s',t), Rval (Loc lnum))
    | (AallocEmpty, [Conv NONE []]) =>
        let (s',lnum) = (store_alloc (Varray []) s) in
          SOME ((s',t), Rval (Loc lnum))
    | (Asub, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME ((s,t), Rerr (Rraise sub_exn_v))
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    SOME ((s,t), Rerr (Rraise sub_exn_v))
                  else
                    SOME ((s,t), Rval (EL n vs))
          | _ => NONE
        )
    | (Asub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    NONE
                  else
                    SOME ((s,t), Rval (EL n vs))
          | _ => NONE
        )
    | (Alength, [Loc n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME ((s,t), Rerr (Rraise sub_exn_v))
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  SOME ((s,t), Rerr (Rraise sub_exn_v))
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aupdate_unsafe, [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  NONE
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (ConfigGC, [Litv (IntLit i); Litv (IntLit j)]) =>
        SOME ((s,t), Rval (Conv NONE []))
    | (FFI n, [Litv(StrLit conf); Loc lnum]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            (case call_FFI t n (MAP (\ c .  n2w(ORD c)) (EXPLODE conf)) ws of
              FFI_return t' ws' =>
               (case store_assign lnum (W8array ws') s of
                 SOME s' => SOME ((s', t'), Rval (Conv NONE []))
               | NONE => NONE
               )
            | FFI_final outcome =>
               SOME ((s, t), Rerr (Rabort (Rffi_error outcome)))
            )
        | _ => NONE
        )
    | (Env_id, [Env env (gen, id)]) => SOME ((s, t),
            Rval (Conv NONE [nat_to_v gen; nat_to_v id]))
    | (Env_id, [Conv NONE [gen; id]]) => SOME ((s, t),
            Rval (Conv NONE [gen; id]))
     | _ => NONE
  )))`;


(* Do a logical operation *)
(*val do_log : lop -> v -> exp -> maybe exp_or_val*)
val _ = Define `
 ((do_log:lop -> v -> exp ->(exp_or_val)option) l v e=
   (if ((l = And) /\ (v = Boolv T)) \/ ((l = Or) /\ (v = Boolv F)) then
    SOME (Exp e)
  else if ((l = And) /\ (v = Boolv F)) \/ ((l = Or) /\ (v = Boolv T)) then
    SOME (Val v)
  else
    NONE))`;


(* Do an if-then-else *)
(*val do_if : v -> exp -> exp -> maybe exp*)
val _ = Define `
 ((do_if:v -> exp -> exp ->(exp)option) v e1 e2=
   (if v = (Boolv T) then
    SOME e1
  else if v = (Boolv F) then
    SOME e2
  else
    NONE))`;


(* Semantic helpers for definitions *)

val _ = Define `
 ((build_constrs:num ->(string#'a list)list ->(string#(num#stamp))list) stamp condefs=
   (MAP
    (\ (conN, ts) .
      (conN, (LENGTH ts, TypeStamp conN stamp)))
    condefs))`;


(* Build a constructor environment for the type definition tds *)
(*val build_tdefs : nat -> list (list tvarN * typeN * list (conN * list ast_t)) -> env_ctor*)
 val _ = Define `
 ((build_tdefs:num ->((tvarN)list#string#(string#(ast_t)list)list)list ->((string),(string),(num#stamp))namespace) next_stamp []=  (alist_to_ns []))
/\ ((build_tdefs:num ->((tvarN)list#string#(string#(ast_t)list)list)list ->((string),(string),(num#stamp))namespace) next_stamp ((tvs,tn,condefs)::tds)=
   (nsAppend
    (build_tdefs (next_stamp +( 1 : num)) tds)
    (alist_to_ns (REVERSE (build_constrs next_stamp condefs)))))`;


(* Checks that no constructor is defined twice in a type *)
(*val check_dup_ctors : list tvarN * typeN * list (conN * list ast_t) -> bool*)
val _ = Define `
 ((check_dup_ctors:(tvarN)list#string#(string#(ast_t)list)list -> bool) (tvs, tn, condefs)=
   (ALL_DISTINCT (let x2 =
  ([]) in  FOLDR (\(n, ts) x2 .  if T then n :: x2 else x2) x2 condefs)))`;


(*val combine_dec_result : forall 'a. sem_env v -> result (sem_env v) 'a -> result (sem_env v) 'a*)
val _ = Define `
 ((combine_dec_result:(v)sem_env ->(((v)sem_env),'a)result ->(((v)sem_env),'a)result) env r=
   ((case r of
      Rerr e => Rerr e
    | Rval env' => Rval <| v := (nsAppend env'.v env.v); c := (nsAppend env'.c env.c) |>
  )))`;


(*val extend_dec_env : sem_env v -> sem_env v -> sem_env v*)
val _ = Define `
 ((extend_dec_env:(v)sem_env ->(v)sem_env ->(v)sem_env) new_env env=
   (<| c := (nsAppend new_env.c env.c); v := (nsAppend new_env.v env.v) |>))`;


(*
val decs_to_types : list dec -> list typeN
let decs_to_types ds =
  List.concat (List.map (fun d ->
        match d with
          | Dtype locs tds -> List.map (fun (tvs,tn,ctors) -> tn) tds
          | _ -> [] end)
     ds)

val no_dup_types : list dec -> bool
let no_dup_types ds =
  List.allDistinct (decs_to_types ds)

val prog_to_mods : list top -> list (list modN)
let prog_to_mods tops =
  List.concat (List.map (fun top ->
        match top with
          | Tmod mn _ _ -> [[mn]]
          | _ -> [] end)
     tops)

val no_dup_mods : list top -> set (list modN) -> bool
let no_dup_mods tops defined_mods =
  List.allDistinct (prog_to_mods tops) &&
  disjoint (Set.fromList (prog_to_mods tops)) defined_mods

val prog_to_top_types : list top -> list typeN
let prog_to_top_types tops =
  List.concat (List.map (fun top ->
        match top with
          | Tdec d -> decs_to_types [d]
          | _ -> [] end)
     tops)

val no_dup_top_types : list top -> set tid_or_exn -> bool
let no_dup_top_types tops defined_types =
  List.allDistinct (prog_to_top_types tops) &&
  disjoint (Set.fromList (List.map (fun tn -> TypeId (Short tn)) (prog_to_top_types tops))) defined_types
  *)
val _ = export_theory()

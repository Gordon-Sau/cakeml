structure reg_alloc = struct
  datatype reg_alloc_tag =  Stemp
  |  Atemp
  |  Fixed of  int;
  datatype 'a sptree_spt =  Bs of  'a sptree_spt *  'a  *  'a sptree_spt
  |  Bn of  'a sptree_spt *  'a sptree_spt
  |  Ls of  'a
   |  Ln;
  datatype reg_alloc_clash_tree =  Seq of  reg_alloc_clash_tree *  reg_alloc_clash_tree
  |  Branch of  unit sptree_spt option *  reg_alloc_clash_tree *  reg_alloc_clash_tree
  |  Set of  unit sptree_spt
  |  Delta of  int list *  int list;
  datatype reg_alloc_algorithm =  Irc
  |  Simple;
  exception  Fail of  char list;
  fun  even v1 =
    if  (v1 = 0)
    then  (0 <= 0)
    else  ((even (let val  k = v1 - 1
                   in
                    if  (k < 0)
                    then  0
                     else  k
                   end)) = (0 < 0));
  fun  map v3 v4 =
    case  v4
    of  []  =>  []
     |   v2::v1 =>  (v3 v2::(map v3 v1));
  fun  fst v3 =  case  v3 of  (v2,v1) =>  v2;
  fun  snd v3 =  case  v3 of  (v2,v1) =>  v1;
  fun  member v4 v3 =
    case  v3
    of  []  =>  (0 < 0)
    |   v2::v1 =>  ((v4 = v2) orelse  (member v4 v1));
  fun  snoc v4 v3 =
    case  v3
    of  []  =>  [v4]
    |   v2::v1 =>  (v2::(snoc v4 v1));
  fun  genlist v1 v2 =
    if  (v2 = 0)
    then  []
     else  (snoc (v1 (let val  k = v2 - 1
                       in
                        if  (k < 0)
                        then  0
                         else  k
                       end)) (genlist v1 (let val  k = v2 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           end)));
  fun  append v3 v4 =
    case  v3
    of  []  =>  v4
    |   v2::v1 =>  (v2::(append v1 v4));
  fun  part v3 v6 v4 v5 =
    case  v6
    of  []  =>  (v4,v5)
    |   v2::v1 =>  (if  (v3 v2)
                    then  (part v3 v1 (v2::v4) v5)
                    else  (part v3 v1 v4 (v2::v5)));
  fun  partition v1 =  (fn  v2 => part v1 v2 [] [] );
  fun  qsort v7 v8 =
    case  v8
    of  []  =>  []
     |   v6::v5 =>  (let val  v3 = partition (fn  v4 => (v7 v4 v6)) v5
                      in
                       case  v3
                       of  (v2,v1) =>  (append (append (qsort v7 v2) [v6]) (qsort v7 v1))
                     end);
  fun  lookup_1 v7 v8 =
  case  v8
  of  Ln =>  NONE
  |   Ls(v1) =>  (if  (v7 = 0)
  then  (SOME(v1))
  else  NONE)
  |   Bn(v3,v2) =>  (if  (v7 = 0)
  then  NONE
   else  (lookup_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) (if  (even v7)
  then  v3
   else  v2)))
  |   Bs(v6,v5,v4) =>  (if  (v7 = 0)
  then  (SOME(v5))
  else  (lookup_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) (if  (even v7)
  then  v6
   else  v4)));
  fun  insert_1 v7 v8 v9 =
  case  v9
  of  Ln =>  (if  (v7 = 0)
  then  (Ls(v8))
  else  (if  (even v7)
  then  (Bn(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln,Ln))
  else  (Bn(Ln,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln))))
  |   Ls(v1) =>  (if  (v7 = 0)
  then  (Ls(v8))
  else  (if  (even v7)
  then  (Bs(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln,v1,Ln))
  else  (Bs(Ln,v1,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln))))
  |   Bn(v3,v2) =>  (if  (v7 = 0)
  then  (Bs(v3,v8,v2))
  else  (if  (even v7)
  then  (Bn(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v3,v2))
  else  (Bn(v3,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v2))))
  |   Bs(v6,v5,v4) =>  (if  (v7 = 0)
  then  (Bs(v6,v8,v4))
  else  (if  (even v7)
  then  (Bs(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v6,v5,v4))
  else  (Bs(v6,v5,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v4))));
  fun  lrnext v1 =
  if  (v1 = 0)
  then  1
   else  (2 * (lrnext ((let val  k = v1 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2)));
  fun  foldi v9 v10 v12 v11 =
  case  v11
  of  Ln =>  v12
  |   Ls(v1) =>  (v9 v10 v1 v12)
  |   Bn(v4,v3) =>  (let val  v2 = lrnext v10
   in
    foldi v9 (v10 + v2) (foldi v9 (v10 + (2 * v2)) v12 v4) v3
   end)
  |   Bs(v8,v7,v6) =>  (let val  v5 = lrnext v10
   in
    foldi v9 (v10 + v5) (v9 v10 v7 (foldi v9 (v10 + (2 * v5)) v12 v8)) v6
   end);
  fun  toalist v4 = 
    foldi (fn  v3 => (fn  v2 => (fn  v1 => ((v3,v2)::v1)))) 0 [] v4;
  fun  map_1 v7 v8 =
  case  v8
  of  Ln =>  Ln
  |   Ls(v1) =>  (Ls(v7 v1))
  |   Bn(v3,v2) =>  (Bn(map_1 v7 v3,map_1 v7 v2))
  |   Bs(v6,v5,v4) =>  (Bs(map_1 v7 v6,v7 v5,map_1 v7 v4));
  fun  count_list_aux v2 v1 =
  if  (v2 = 0)
  then  v1
   else  (count_list_aux (let val  k = v2 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) (let val  k = v2 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end::v1));
  fun  count_list v1 =  count_list_aux v1 [] ;
  fun  list_remap v12 v13 =
  case  v12
  of  []  =>  (case  v13 of  (v4,v3) =>  (case  v3 of  (v2,v1) =>  (v4,(v2,v1))))
  |   v11::v10 =>  (case  v13
  of  (v9,v8) =>  (case  v8
  of  (v7,v6) =>  (case  (lookup_1 v11 v9)
  of  NONE =>  (list_remap v10 (insert_1 v11 v6 v9,(insert_1 v6 v11 v7,v6 + 1)))
  |   (SOME(v5)) =>  (list_remap v10 (v9,(v7,v6))))));
  fun  mk_bij_aux v11 v12 =
  case  v11
  of  Delta(v2,v1) =>  (list_remap v2 (list_remap v1 v12))
  |   Set(v3) =>  (list_remap (map fst (toalist v3)) v12)
  |   Branch(v8,v7,v6) =>  (let val  v5 = mk_bij_aux v6 (mk_bij_aux v7 v12)
  in
    case  v8
  of  NONE =>  v5
  |   SOME(v4) =>  (list_remap (map fst (toalist v4)) v5)
  end)
  |   Seq(v10,v9) =>  (mk_bij_aux v10 (mk_bij_aux v9 v12));
  fun  mk_bij v6 = 
    let val  v5 = mk_bij_aux v6 (Ln,(Ln,0))
    in
      case  v5 of  (v4,v3) =>  (case  v3 of  (v2,v1) =>  (v4,(v2,v1)))
    end;
  fun  is_phy_var v1 =  (v1 mod 2) = 0;
  fun  sp_default v3 = 
    (fn  v2 =>
      case  (lookup_1 v2 v3)
      of  NONE =>  (if  (is_phy_var v2)
      then  (v2 div 2)
      else  v2)
      |   SOME(v1) =>  v1);
  fun  extract_tag v2 = 
    case  v2
    of  Fixed(v1) =>  v1
    |   Atemp =>  0
    |   Stemp =>  0;
  fun  fromalist v5 =
  case  v5
  of  []  =>  Ln
  |   v4::v3 =>  (case  v4 of  (v2,v1) =>  (insert_1 v2 v1 (fromalist v3)));
  fun  sort_moves v7 = 
    qsort (fn  v6 =>
      (case  v6
      of  (v5,v4) =>  (fn  v3 => (case  v3 of  (v2,v1) =>  (v5 > v2))))) v7;
  fun  smerge v10 v9 =
  case  v10
  of  []  =>  v9
  |   v8::v7 =>  (case  v9
  of  []  =>  (v8::v7)
  |   (v6::v5) =>  (case  v6
  of  (v4,v3) =>  (case  v8
  of  (v2,v1) =>  (if  (v2 >= v4)
  then  ((v2,v1)::(smerge v7 ((v4,v3)::v5)))
  else  ((v4,v3)::(smerge ((v2,v1)::v7) v5))))));
  fun  pair_rename v11 = 
    (fn  v9 =>
      (fn  v10 =>
        case  (v9,v10)
        of  (v8,v7) =>  (case  v7
        of  (v6,v5) =>  (case  v5
        of  (v4,v3) =>  (let val  v2 =
          if  (v4 = v8)
          then  v11
           else  v4
            val  v1 =
          if  (v3 = v8)
          then  v11
           else  v3
         in
          (v6,(v2,v1))
        end)))));
  fun  safe_div v2 = 
    (fn  v1 =>
      if  (v1 = 0)
      then  0
       else  (v2 div v1));
  fun  lookup_any v4 = 
    (fn  v3 =>
      (fn  v2 =>
        case  (lookup_1 v4 v3)
        of  NONE =>  v2
        |   SOME(v1) =>  v1));
  fun  tag_col v2 = 
    case  v2
    of  Fixed(v1) =>  v1
    |   Atemp =>  0
    |   Stemp =>  0;
  fun  unbound_colour v3 v4 =
  case  v4
  of  []  =>  v3
  |   v2::v1 =>  (if  (v3 < v2)
  then  v3
   else  (if  (v2 = v3)
  then  (unbound_colour (v3 + 1) v1)
  else  (unbound_colour v3 v1)));
  fun  pri_move_insert v3 = 
    (fn  v4 =>
      (fn  v5 =>
        (fn  v2 =>
          case  (lookup_1 v4 v2)
          of  NONE =>  (insert_1 v4 [(v3,v5)] v2)
          |   SOME(v1) =>  (insert_1 v4 ((v3,v5)::v1) v2))));
  fun  undir_move_insert v2 = 
    (fn  v3 =>
      (fn  v4 =>
        (fn  v1 => pri_move_insert v2 v3 v4 (pri_move_insert v2 v4 v3 v1))));
  fun  moves_to_sp v9 v8 =
  case  v9
  of  []  =>  v8
  |   v7::v6 =>  (let val  v5 = v7
   in
    case  v5
  of  (v4,v3) =>  (case  v3
  of  (v2,v1) =>  (moves_to_sp v6 (undir_move_insert v4 v2 v1 v8)))
  end);
  fun  resort_moves v8 = 
    map_1 (fn  v7 =>
      (map snd (qsort (fn  v6 =>
        (case  v6
        of  (v5,v4) =>  (fn  v3 => (case  v3 of  (v2,v1) =>  (v5 > v2))))) v7))) v8;
  datatype reg_alloc_ira_state =  Recordtypeira_state of  (int *  int list) *  (int *  reg_alloc_tag) *  (int *  int) *  int *  int list *  int list *  int list *  (int *  (int *  int)) list *  (int *  (int *  int)) list *  (int *  int option) *  (int *  bool) *  int list;
  fun  ira_state_adj_ls v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v12;
  fun  ira_state_node_tag v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v11;
  fun  ira_state_degrees v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v10;
  fun  ira_state_dim v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v9;
  fun  ira_state_simp_wl v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v8;
  fun  ira_state_spill_wl v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v7;
  fun  ira_state_freeze_wl v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v6;
  fun  ira_state_avail_moves_wl v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v5;
  fun  ira_state_unavail_moves_wl v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v4;
  fun  ira_state_coalesced v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v3;
  fun  ira_state_move_related v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v2;
  fun  ira_state_stack v13 = 
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v1;
  fun  ira_state_adj_ls_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v13 v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_node_tag_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v13 v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_degrees_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v13 v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_dim_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v13 v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_simp_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v13 v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_spill_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v13 v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_freeze_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v13 v6,v5,v4,v3,v2,v1)));
  fun  ira_state_avail_moves_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v13 v5,v4,v3,v2,v1)));
  fun  ira_state_unavail_moves_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v13 v4,v3,v2,v1)));
  fun  ira_state_coalesced_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v13 v3,v2,v1)));
  fun  ira_state_move_related_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v13 v2,v1)));
  fun  ira_state_stack_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v13 v1)));
  datatype reg_alloc_ra_state =  Recordtypera_state of  int list list *  reg_alloc_tag list *  int list *  int *  int list *  int list *  int list *  (int *  (int *  int)) list *  (int *  (int *  int)) list *  int option list *  bool list *  int list;
  fun  ra_state_adj_ls v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v12;
  fun  ra_state_node_tag v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v11;
  fun  ra_state_degrees v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v10;
  fun  ra_state_dim v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v9;
  fun  ra_state_simp_wl v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v8;
  fun  ra_state_spill_wl v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v7;
  fun  ra_state_freeze_wl v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v6;
  fun  ra_state_avail_moves_wl v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v5;
  fun  ra_state_unavail_moves_wl v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v4;
  fun  ra_state_coalesced v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v3;
  fun  ra_state_move_related v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v2;
  fun  ra_state_stack v13 = 
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v1;
  fun  ra_state_adj_ls_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13 v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_node_tag_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v13 v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_degrees_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v13 v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_dim_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v13 v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_simp_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v13 v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_spill_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v13 v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_freeze_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v13 v6,v5,v4,v3,v2,v1)));
  fun  ra_state_avail_moves_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v13 v5,v4,v3,v2,v1)));
  fun  ra_state_unavail_moves_wl_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v13 v4,v3,v2,v1)));
  fun  ra_state_coalesced_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v13 v3,v2,v1)));
  fun  ra_state_move_related_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v13 v2,v1)));
  fun  ra_state_stack_fupd v13 = 
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v13 v1)));
  datatype ( 'a  ,  'b ) ml_monadBase_exc =  Failure of  'b
   |  Success of  'a ;
  fun  reg_alloc_aux alg = 
    (fn  sc =>
      (fn  k =>
        (fn  mtable =>
          (fn  ct =>
            (fn  forced =>
              (fn  x =>
                let val  move_related = Array.array ( (snd (snd x)), (0 < 0))
                    val  coalesced = Array.array ( (snd (snd x)), NONE)
                    val  degrees = Array.array ( (snd (snd x)), 0)
                    val  node_tag = Array.array ( (snd (snd x)), Atemp)
                    val  adj_ls = Array.array ( (snd (snd x)), [] )
                    val  stack = ref( [] )
                    val  unavail_moves_wl = ref( [] )
                    val  avail_moves_wl = ref( [] )
                    val  freeze_wl = ref( [] )
                    val  spill_wl = ref( [] )
                    val  simp_wl = ref( [] )
                    val  dim = ref( (snd (snd x)))
                    fun  st_ex_foreach v5 v4 =
                case  v5
                of  []  =>  ()
                |   v3::v2 =>  (let val  v1 = v4 v3
                 in
                  st_ex_foreach v2 v4
                 end)
                    fun  st_ex_map v5 v6 =
                case  v6
                of  []  =>  []
                 |   v4::v3 =>  (let val  v2 = v5 v4
                    val  v1 = st_ex_map v5 v3
                 in
                  v2::v1
                 end)
                    fun  st_ex_partition v4 v6 v7 v5 =
                case  v6
                of  []  =>  (v7,v5)
                |   v3::v2 =>  (let val  v1 = v4 v3
                 in
                  if  v1
                 then  (st_ex_partition v4 v2 (v3::v7) v5)
                else  (st_ex_partition v4 v2 v7 (v3::v5))
                end)
                    fun  st_ex_filter v4 v6 v5 =
                case  v6
                of  []  =>  v5
                |   v3::v2 =>  (let val  v1 = v4 v3
                 in
                  if  v1
                 then  (st_ex_filter v4 v2 (v3::v5))
                else  (st_ex_filter v4 v2 v5)
                end)
                    val  dec_deg =
                  (fn  v2 =>
                    let val  v1 = Array.sub ( degrees, v2)
                    in
                      Array.update ( degrees, v2, (let val  k = v1 - 1
                     in
                      if  (k < 0)
                    then  0
                     else  k
                     end))
                    end)
                    val  dec_degree =
                  (fn  v3 =>
                    let val  v2 = !( dim)
                    in
                      if  (v3 < v2)
                    then  (let val  v1 = Array.sub ( adj_ls, v3)
                    in
                      st_ex_foreach v1 dec_deg
                     end)
                    else  ()
                    end)
                    val  add_simp_wl =
                  (fn  v2 =>
                    let val  v1 = !( simp_wl)
                    in
                      simp_wl := (v2 @ v1)
                    end)
                    val  add_freeze_wl =
                  (fn  v2 =>
                    let val  v1 = !( freeze_wl)
                    in
                      freeze_wl := (v2 @ v1)
                    end)
                    val  push_stack =
                  (fn  v4 =>
                    let val  v3 = !( stack)
                        val  v2 = Array.update ( degrees, v4, 0)
                        val  v1 = Array.update ( move_related, v4, (0 < 0))
                    in
                      stack := (v4::v3)
                    end)
                    val  add_unavail_moves_wl =
                  (fn  v2 =>
                    let val  v1 = !( unavail_moves_wl)
                    in
                      unavail_moves_wl := (v2 @ v1)
                    end)
                    val  is_not_coalesced =
                  (fn  v2 =>
                    let val  v1 = Array.sub ( coalesced, v2)
                    in
                      v1 = NONE
                     end)
                    val  split_degree =
                  (fn  v3 =>
                    (fn  v4 =>
                      (fn  v5 =>
                        if  (v5 < v3)
                        then  (let val  v2 = Array.sub ( degrees, v5)
                            val  v1 = is_not_coalesced v5
                         in
                          (v2 < v4) andalso  v1
                         end)
                        else  (0 <= 0))))
                    val  revive_moves =
                  (fn  v16 =>
                    let val  v15 =
                      st_ex_map (fn  v1 => (Array.sub ( adj_ls, v1))) v16
                        val  v14 = !( unavail_moves_wl)
                        val  v13 = !( avail_moves_wl)
                        val  v12 = List.concat v15
                        val  v6 =
                      partition (fn  v11 =>
                        (case  v11
                        of  (v10,v9) =>  (case  v9
                        of  (v8,v7) =>  ((member v8 v12) orelse  (member v7 v12))))) v14
                     in
                      case  v6
                    of  (v5,v4) =>  (let val  v3 = smerge (sort_moves v5) v13
                        val  v2 = avail_moves_wl := v3
                     in
                      unavail_moves_wl := v4
                     end)
                    end)
                    val  unspill =
                  (fn  v13 =>
                    let val  v12 = !( dim)
                        val  v11 = !( spill_wl)
                        val  v10 =
                      st_ex_partition (split_degree v12 v13) v11 [] []
                     in
                      case  v10
                    of  (v9,v8) =>  (let val  v7 = revive_moves v9
                        val  v6 =
                      st_ex_partition (fn  v1 =>
                        (Array.sub ( move_related, v1))) v9 [] []
                     in
                      case  v6
                    of  (v5,v4) =>  (let val  v3 = spill_wl := v8
                        val  v2 = add_simp_wl v4
                     in
                      add_freeze_wl v5
                     end)
                    end)
                    end)
                    val  do_simplify =
                  (fn  v6 =>
                    let val  v5 = !( simp_wl)
                    in
                      if  (null v5)
                    then  (0 < 0)
                    else  (let val  v4 = st_ex_foreach v5 dec_degree
                        val  v3 = st_ex_foreach v5 push_stack
                        val  v2 = simp_wl := []
                         val  v1 = unspill v6
                     in
                      0 <= 0
                     end)
                    end)
                    val  inc_deg =
                  (fn  v3 =>
                    (fn  v2 =>
                      let val  v1 = Array.sub ( degrees, v3)
                      in
                        Array.update ( degrees, v3, (v1 + v2))
                      end))
                    val  insert_edge =
                  (fn  v4 =>
                    (fn  v5 =>
                      let val  v3 = Array.sub ( adj_ls, v4)
                          val  v2 = Array.sub ( adj_ls, v5)
                      in
                        if  (member v5 v3)
                      then  ()
                      else  (let val  v1 = Array.update ( adj_ls, v4, (v5::v3))
                      in
                        Array.update ( adj_ls, v5, (v4::v2))
                      end)
                      end))
                    fun  list_insert_edge v5 v4 =
                case  v4
                of  []  =>  ()
                |   v3::v2 =>  (let val  v1 = insert_edge v5 v3
                 in
                  list_insert_edge v5 v2
                 end)
                    val  do_coalesce_real =
                  (fn  v15 =>
                    (fn  v16 =>
                      let val  v14 =
                        Array.update ( coalesced, v16, (SOME(v15)))
                          val  v13 = !( avail_moves_wl)
                          val  v12 =
                        avail_moves_wl := (map (pair_rename v15 v16) v13)
                          val  v11 = !( unavail_moves_wl)
                          val  v10 =
                        unavail_moves_wl := (map (pair_rename v15 v16) v11)
                          val  v9 = Array.sub ( adj_ls, v15)
                          val  v8 = Array.sub ( adj_ls, v16)
                          val  v6 =
                        partition (fn  v7 => (member v7 v9)) v8
                       in
                        case  v6
                      of  (v5,v4) =>  (let val  v3 =
                        inc_deg v15 (length v4)
                          val  v2 = list_insert_edge v15 v4
                          val  v1 = st_ex_foreach v5 dec_deg
                       in
                        push_stack v16
                       end)
                      end))
                    val  bg_ok =
                  (fn  v21 =>
                    (fn  v22 =>
                      (fn  v23 =>
                        let val  v20 = Array.sub ( adj_ls, v22)
                            val  v19 = Array.sub ( adj_ls, v23)
                            val  v17 =
                          partition (fn  v18 => (member v18 v20)) v19
                         in
                          case  v17
                        of  (v16,v15) =>  (let val  v14 =
                          st_ex_map (fn  v1 => (Array.sub ( degrees, v1))) v15
                            val  v12 =
                          length (filter (fn  v13 => (v13 >= v21)) v14)
                        in
                          if  (v12 = 0)
                        then  (0 <= 0)
                        else  (let val  v10 =
                          filter (fn  v11 =>
                            ((member v11 v19) = (0 < 0))) v20
                            val  v9 =
                          st_ex_map (fn  v2 => (Array.sub ( degrees, v2))) v16
                            val  v8 =
                          st_ex_map (fn  v3 => (Array.sub ( degrees, v3))) v10
                            val  v7 =
                          length (filter (fn  v4 =>
                            ((let val  k = v4 - 1
                             in
                              if  (k < 0)
                            then  0
                             else  k
                             end) >= v21)) v9)
                            val  v6 =
                          length (filter (fn  v5 => (v5 >= v21)) v8)
                        in
                          ((v7 + v12) + v6) < v21
                         end)
                        end)
                        end)))
                    val  is_fixed =
                  (fn  v3 =>
                    let val  v2 = Array.sub ( node_tag, v3)
                    in
                      case  v2
                    of  Fixed(v1) =>  (0 <= 0)
                    |   Atemp =>  (0 < 0)
                    |   Stemp =>  (0 < 0)
                    end)
                    val  consistency_ok =
                  (fn  v6 =>
                    (fn  v7 =>
                      if  (v6 = v7)
                      then  (0 < 0)
                      else  (let val  v5 = !( dim)
                      in
                        if  ((v6 >= v5) orelse  (v7 >= v5))
                      then  (0 < 0)
                      else  (let val  v4 = Array.sub ( adj_ls, v7)
                      in
                        if  (member v6 v4)
                      then  (0 < 0)
                      else  (let val  v3 = is_fixed v6
                          val  v2 = Array.sub ( move_related, v6)
                          val  v1 = Array.sub ( move_related, v7)
                      in
                        (v3 orelse  v2) andalso  v1
                       end)
                      end)
                      end)))
                    fun  st_ex_first v10 v11 v12 v13 =
                case  v12
                of  []  =>  (NONE,v13)
                |   v9::v8 =>  (let val  v7 = v9
                 in
                  case  v7
                of  (v6,v5) =>  (case  v5
                of  (v4,v3) =>  (let val  v2 = v10 v4 v3
                 in
                  if  (v2 = (0 < 0))
                then  (st_ex_first v10 v11 v8 v13)
                else  (let val  v1 = v11 v4 v3
                 in
                  if  v1
                 then  (let val  x = ((v4,v3),v8)
                in
                  SOME(x)
                end,v13)
                else  (st_ex_first v10 v11 v8 (v9::v13))
                end)
                end))
                end)
                    val  do_coalesce =
                  (fn  v15 =>
                    let val  v14 = !( avail_moves_wl)
                        val  v13 =
                      st_ex_first consistency_ok (bg_ok v15) v14 []
                     in
                      case  v13
                    of  (v12,v11) =>  (let val  v10 = add_unavail_moves_wl v11
                     in
                      case  v12
                    of  NONE =>  (let val  v1 = avail_moves_wl := []
                     in
                      0 < 0
                     end)
                    |   SOME(v9) =>  (case  v9
                    of  (v8,v7) =>  (case  v8
                    of  (v6,v5) =>  (let val  v4 = avail_moves_wl := v7
                        val  v3 = do_coalesce_real v6 v5
                        val  v2 = unspill v15
                     in
                      0 <= 0
                     end)))
                    end)
                    end)
                    val  reset_move_related =
                  (fn  v10 =>
                    let val  v9 = !( dim)
                        val  v8 =
                      st_ex_foreach (count_list v9) (fn  v1 =>
                        (Array.update ( move_related, v1, (0 < 0))))
                    in
                      st_ex_foreach v10 (fn  v7 =>
                      (case  v7
                      of  (v6,v5) =>  (case  v5
                      of  (v4,v3) =>  (let val  v2 =
                        Array.update ( move_related, v4, (0 <= 0))
                      in
                        Array.update ( move_related, v3, (0 <= 0))
                      end))))
                    end)
                    val  do_prefreeze =
                  (fn  v21 =>
                    let val  v20 = !( freeze_wl)
                        val  v19 = st_ex_filter is_not_coalesced v20 []
                         val  v18 = !( spill_wl)
                        val  v17 = st_ex_filter is_not_coalesced v18 []
                         val  v16 = spill_wl := v17
                        val  v15 = !( unavail_moves_wl)
                        val  v14 =
                      st_ex_filter (fn  v5 =>
                        (case  v5
                        of  (v4,v3) =>  (case  v3
                        of  (v2,v1) =>  (consistency_ok v2 v1)))) v15 []
                         val  v13 = reset_move_related v14
                        val  v12 = unavail_moves_wl := v14
                        val  v11 =
                      st_ex_partition (fn  v6 =>
                        (Array.sub ( move_related, v6))) v19 [] []
                     in
                      case  v11
                    of  (v10,v9) =>  (let val  v8 = add_simp_wl v9
                        val  v7 = freeze_wl := v10
                     in
                      do_simplify v21
                     end)
                    end)
                    val  do_freeze =
                  (fn  v8 =>
                    let val  v7 = !( freeze_wl)
                    in
                      if  (null v7)
                    then  (0 < 0)
                    else  (case  v7
                    of  []  =>  (0 < 0)
                    |   (v6::v5) =>  (let val  v4 = dec_degree v6
                        val  v3 = push_stack v6
                        val  v2 = freeze_wl := v5
                        val  v1 = unspill v8
                     in
                      0 <= 0
                     end))
                    end)
                    fun  st_ex_list_min_cost v10 v9 v7 v8 v5 v6 =
                case  v9
                of  []  =>  (v8,v6)
                |   v4::v3 =>  (if  (v4 < v7)
                then  (let val  v2 = Array.sub ( degrees, v4)
                    val  v1 = safe_div (lookup_any v4 v10 0) v2
                 in
                  if  (v5 > v1)
                then  (st_ex_list_min_cost v10 v3 v7 v4 v1 (v8::v6))
                else  (st_ex_list_min_cost v10 v3 v7 v8 v5 (v4::v6))
                end)
                else  (st_ex_list_min_cost v10 v3 v7 v8 v5 v6))
                    val  do_spill =
                  (fn  v14 =>
                    (fn  v13 =>
                      let val  v12 = !( spill_wl)
                          val  v11 = !( dim)
                      in
                        case  v12
                      of  []  =>  (0 < 0)
                      |   v10::v9 =>  (if  (v10 >= v11)
                      then  (0 <= 0)
                      else  (let val  v8 = Array.sub ( degrees, v10)
                          val  v7 =
                        st_ex_list_min_cost v14 v9 v11 v10 (safe_div (lookup_any v10 v14 0) v8) []
                       in
                        case  v7
                      of  (v6,v5) =>  (let val  v4 = dec_deg v6
                          val  v3 = push_stack v6
                          val  v2 = spill_wl := v5
                          val  v1 = unspill v13
                       in
                        0 <= 0
                       end)
                      end))
                      end))
                    val  do_step =
                  (fn  v7 =>
                    (fn  v6 =>
                      let val  v5 = do_simplify v6
                       in
                        if  v5
                       then  ()
                      else  (let val  v4 = do_coalesce v6
                       in
                        if  v4
                       then  ()
                      else  (let val  v3 = do_prefreeze v6
                       in
                        if  v3
                       then  ()
                      else  (let val  v2 = do_freeze v6
                       in
                        if  v2
                       then  ()
                      else  (let val  v1 = do_spill v7 v6
                       in
                        ()
                      end)
                      end)
                      end)
                      end)
                      end))
                    fun  rpt_do_step v4 v2 v3 =
                if  (v3 = 0)
                then  ()
                else  (let val  v1 = do_step v4 v2
                 in
                  rpt_do_step v4 v2 (let val  k = v3 - 1
                 in
                  if  (k < 0)
                then  0
                 else  k
                 end)
                end)
                    fun  remove_colours v10 v9 =
                case  v9
                of  []  =>  []
                 |   v8::v7 =>  (case  v10
                of  []  =>  (v8::v7)
                |   (v6::v5) =>  (let val  v4 = Array.sub ( node_tag, v6)
                    val  v3 =
                  case  v4
                  of  Fixed(v2) =>  (remove_colours v5 (filter (fn  v1 =>
                    ((v1 = v2) = (0 < 0))) (v8::v7)))
                  |   Atemp =>  (remove_colours v5 (v8::v7))
                  |   Stemp =>  (remove_colours v5 (v8::v7))
                in
                  v3
                 end))
                    val  assign_atemp_tag =
                  (fn  v11 =>
                    (fn  v10 =>
                      (fn  v9 =>
                        let val  v8 = Array.sub ( node_tag, v9)
                        in
                          case  v8
                        of  Fixed(v1) =>  ()
                        |   Atemp =>  (let val  v7 = Array.sub ( adj_ls, v9)
                            val  v6 = remove_colours v7 v11
                         in
                          case  v6
                        of  []  =>  (Array.update ( node_tag, v9, Stemp))
                        |   v5::v4 =>  (let val  v3 = v10 v9 v6
                         in
                          case  v3
                        of  NONE =>  (Array.update ( node_tag, v9, (Fixed(v5))))
                        |   SOME(v2) =>  (Array.update ( node_tag, v9, (Fixed(v2))))
                        end)
                        end)
                        |   Stemp =>  ()
                        end)))
                    val  assign_atemps =
                  (fn  v11 =>
                    (fn  v9 =>
                      (fn  v10 =>
                        let val  v8 = !( dim)
                            val  v7 = filter (fn  v1 => (v1 < v8)) v9
                            val  v6 = genlist (fn  v2 => v2) v11
                            val  v5 = genlist (fn  v3 => v3) v8
                            val  v4 =
                          st_ex_foreach v7 (assign_atemp_tag v6 v10)
                        in
                          st_ex_foreach v5 (assign_atemp_tag v6 v10)
                        end)))
                    val  assign_stemp_tag =
                  (fn  v10 =>
                    (fn  v9 =>
                      let val  v8 = Array.sub ( node_tag, v9)
                      in
                        case  v8
                      of  Fixed(v1) =>  ()
                      |   Atemp =>  ()
                      |   Stemp =>  (let val  v7 = Array.sub ( adj_ls, v9)
                          val  v6 =
                        st_ex_map (fn  v2 => (Array.sub ( node_tag, v2))) v7
                          val  v5 =
                        unbound_colour v10 (qsort (fn  v4 =>
                          (fn  v3 => (v4 <= v3))) (map tag_col v6))
                      in
                        Array.update ( node_tag, v9, (Fixed(v5)))
                      end)
                      end))
                    val  assign_stemps =
                  (fn  v4 =>
                    let val  v3 = !( dim)
                        val  v2 = genlist (fn  v1 => v1) v3
                     in
                      st_ex_foreach v2 (assign_stemp_tag v4)
                    end)
                    fun  first_match_col v5 v6 =
                case  v6
                of  []  =>  NONE
                |   v4::v3 =>  (let val  v2 = Array.sub ( node_tag, v4)
                in
                  case  v2
                of  Fixed(v1) =>  (if  (member v1 v5)
                then  (SOME(v1))
                else  (first_match_col v5 v3))
                |   Atemp =>  (first_match_col v5 v3)
                |   Stemp =>  (first_match_col v5 v3)
                end)
                    val  biased_pref =
                  (fn  v6 =>
                    (fn  v7 =>
                      (fn  v5 =>
                        let val  v4 = !( dim)
                        in
                          if  (v7 < v4)
                        then  (let val  v3 = Array.sub ( coalesced, v7)
                        in
                          case  v3
                        of  NONE =>  (case  (lookup_1 v7 v6)
                        of  NONE =>  NONE
                        |   (SOME(v1)) =>  ((first_match_col v5 v1)
                        handle  Subscript =>  NONE))
                        |   SOME(v2) =>  ((first_match_col v5 [v2])
                        handle  Subscript =>  NONE)
                        end)
                        else  NONE
                         end)))
                    fun  clique_insert_edge v4 =
                case  v4
                of  []  =>  ()
                |   v3::v2 =>  (let val  v1 = list_insert_edge v3 v2
                 in
                  clique_insert_edge v2
                 end)
                    fun  extend_clique v5 v4 =
                case  v5
                of  []  =>  v4
                |   v3::v2 =>  (if  (member v3 v4)
                then  (extend_clique v2 v4)
                else  (let val  v1 = list_insert_edge v3 v4
                 in
                  extend_clique v2 (v3::v4)
                end))
                    fun  mk_graph v26 v25 v24 =
                case  v25
                of  Delta(v8,v7) =>  (let val  v6 = map v26 v8
                    val  v5 = map v26 v7
                    val  v4 = extend_clique v6 v24
                    val  v3 =
                  filter (fn  v1 => ((member v1 v6) = (0 < 0))) v4
                    val  v2 = extend_clique v5 v3
                 in
                  v2
                 end)
                |   Set(v11) =>  (let val  v10 =
                  map v26 (map fst (toalist v11))
                    val  v9 = clique_insert_edge v10
                 in
                  v10
                 end)
                |   Branch(v20,v19,v18) =>  (let val  v17 =
                  mk_graph v26 v19 v24
                    val  v16 = mk_graph v26 v18 v24
                 in
                  case  v20
                of  NONE =>  (let val  v12 = extend_clique v17 v16
                 in
                  v12
                 end)
                |   SOME(v15) =>  (let val  v14 =
                  map v26 (map fst (toalist v15))
                    val  v13 = clique_insert_edge v14
                 in
                  v14
                 end)
                end)
                |   Seq(v23,v22) =>  (let val  v21 = mk_graph v26 v22 v24
                 in
                  mk_graph v26 v23 v21
                 end)
                    fun  extend_graph v6 v7 =
                case  v7
                of  []  =>  ()
                |   v5::v4 =>  (case  v5
                of  (v3,v2) =>  (let val  v1 = insert_edge (v6 v3) (v6 v2)
                in
                  extend_graph v6 v4
                 end))
                    val  mk_tags =
                  (fn  v7 =>
                    (fn  v6 =>
                      let val  v5 = genlist (fn  v1 => v1) v7
                       in
                        st_ex_foreach v5 (fn  v4 =>
                        (let val  v3 = v6 v4
                            val  v2 = v3 mod 4
                         in
                          if  (v2 = 1)
                        then  (Array.update ( node_tag, v4, Atemp))
                        else  (if  (v2 = 3)
                        then  (Array.update ( node_tag, v4, Stemp))
                        else  (Array.update ( node_tag, v4, (Fixed(v3 div 2)))))
                        end))
                      end))
                    val  init_ra_state =
                  (fn  v11 =>
                    (fn  v9 =>
                      (fn  v10 =>
                        case  (v9,v10)
                        of  (v8,v7) =>  (case  v7
                        of  (v6,v5) =>  (case  v5
                        of  (v4,v3) =>  (let val  v2 =
                          mk_graph (sp_default v6) v11 []
                             val  v1 = extend_graph (sp_default v6) v8
                         in
                          mk_tags v3 (sp_default v4)
                        end))))))
                    val  is_atemp =
                  (fn  v2 =>
                    let val  v1 = Array.sub ( node_tag, v2)
                    in
                      v1 = Atemp
                     end)
                    val  init_alloc1_heu =
                  (fn  v28 =>
                    (fn  v26 =>
                      (fn  v27 =>
                        let val  v25 = count_list v26
                            val  v24 =
                          st_ex_foreach v25 (fn  v2 =>
                            (let val  v1 = Array.sub ( adj_ls, v2)
                            in
                              Array.update ( degrees, v2, (length v1))
                            end))
                            val  v23 = st_ex_filter is_atemp v25 []
                             val  v22 =
                          st_ex_foreach v23 (fn  v3 =>
                            (Array.update ( move_related, v3, (0 <= 0))))
                            val  v21 =
                          st_ex_filter (fn  v8 =>
                            (case  v8
                            of  (v7,v6) =>  (case  v6
                            of  (v5,v4) =>  (consistency_ok v5 v4)))) v28 []
                             val  v20 = avail_moves_wl := (sort_moves v21)
                            val  v19 = reset_move_related v21
                            val  v18 =
                          st_ex_partition (split_degree v26 v27) v23 [] []
                         in
                          case  v18
                        of  (v17,v16) =>  (let val  v15 =
                          st_ex_partition (fn  v9 =>
                            (Array.sub ( move_related, v9))) v17 [] []
                         in
                          case  v15
                        of  (v14,v13) =>  (let val  v12 = spill_wl := v16
                            val  v11 = simp_wl := v13
                            val  v10 = freeze_wl := v14
                         in
                          length v23
                         end)
                        end)
                        end)))
                    val  do_alloc1 =
                  (fn  v6 =>
                    (fn  v7 =>
                      (fn  v5 =>
                        let val  v4 = !( dim)
                            val  v3 = init_alloc1_heu v6 v4 v5
                            val  v2 = rpt_do_step v7 v5 v3
                            val  v1 = !( stack)
                        in
                          v1
                         end)))
                    val  extract_color =
                  (fn  v7 =>
                    let val  v6 = toalist v7
                        val  v5 =
                      st_ex_map (fn  v4 =>
                        (case  v4
                        of  (v3,v2) =>  (let val  v1 =
                          Array.sub ( node_tag, v2)
                        in
                          (v3,extract_tag v1)
                        end))) v6
                     in
                      fromalist v5
                     end)
                    val  do_reg_alloc =
                  (fn  v26 =>
                    (fn  v27 =>
                      (fn  v28 =>
                        (fn  v29 =>
                          (fn  v30 =>
                            (fn  v31 =>
                              (fn  v32 =>
                                case  (v27,(v28,(v29,(v30,(v31,v32)))))
                                of  (v25,v24) =>  (case  v24
                                of  (v23,v22) =>  (case  v22
                                of  (v21,v20) =>  (case  v20
                                of  (v19,v18) =>  (case  v18
                                of  (v17,v16) =>  (case  v16
                                of  (v15,v14) =>  (case  v14
                                of  (v13,v12) =>  (let val  v11 =
                                  init_ra_state v19 v17 (v15,(v13,v12))
                                    val  v10 =
                                  map (fn  v5 =>
                                    (case  v5
                                    of  (v4,v3) =>  (case  v3
                                    of  (v2,v1) =>  (v4,(sp_default v15 v2,sp_default v15 v1))))) v21
                                    val  v9 =
                                  do_alloc1 (if  (v26 = Simple)
                                  then  []
                                   else  v10) v25 v23
                                    val  v8 =
                                  assign_atemps v23 v9 (biased_pref (resort_moves (moves_to_sp v10 Ln)))
                                    val  v7 = assign_stemps v23
                                    val  v6 = extract_color v15
                                 in
                                  v6
                                 end))))))))))))))
                in
                  (Success(do_reg_alloc alg sc k mtable ct forced x))
                handle  e =>  Failure(e)
                end))))));
  fun  reg_alloc v1 = 
    (fn  v6 =>
      (fn  v4 =>
        (fn  v5 =>
          (fn  v2 => (fn  v3 => reg_alloc_aux v1 v6 v4 v5 v2 v3 (mk_bij v2))))));
end

#use "semantic-analyser.ml";;

open Reader;;
open Tag_Parser;;
open Semantics;;
open PC;;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : int -> int -> (constant * (int * string)) list -> (string * int) list -> expr' -> string
  val primitive_names_to_labels : (string * string) list
  val inc_ref : int ref -> int
  val lables_ref : int ref
end;;

module Code_Gen : CODE_GEN = struct

exception Exp of string;;

(*let constant_eq c1 c2*)

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
   "car", "car"; "cdr", "cdr"; "set-car!", "set_car"; "set-cdr!", "set_cdr"; "cons", "cons"; "apply", "apply"
  ];;

  (********* constant table *********)

  let string_to_list str =
    let rec loop i limit =
      if i = limit then []
      else (String.get str i) :: (loop (i + 1) limit)
    in
    loop 0 (String.length str);;

  let make_sexpr x =
    Sexpr(x)
 
  let rec remove_duplications lst = 
    let reverse = (List.rev lst) in 
    (List.rev (remove_reversed reverse))

  and remove_reversed lst =
    match lst with
    | [] -> []
    | [x] -> [x]
    | hd::tl ->
      if (List.mem hd tl) 
        then (remove_reversed tl)
        else (List.append [hd] (remove_reversed tl))

  let remove_first_4_elements lst =
  match lst with
  | a::b::c::d::tl -> tl
  | _ -> lst

  let add_const_to_list const sexp_lst = 
    if((List.mem const sexp_lst)=true)
    then sexp_lst
    else (List.append sexp_lst [const]);;

  let rec get_sexpr sexp_lst ast  =
    match ast with
    | Const'(x) -> (add_const_to_list x sexp_lst)
    | BoxSet'(v,e) -> (get_sexpr sexp_lst e)
    | If'(c,t,e) -> 
        let cond = (get_sexpr sexp_lst c) in
        let dit = (get_sexpr cond t) in
        (get_sexpr dit e)
    | Seq'(x) -> (List.fold_left get_sexpr sexp_lst x)
    | Set'(n,v) ->
        let name = (get_sexpr sexp_lst n) in
        (get_sexpr name v)
    | Def'(n,v) ->
        let name = (get_sexpr sexp_lst n) in
        (get_sexpr name v)
    | Or'(x) -> (List.fold_left get_sexpr sexp_lst x)
    | LambdaSimple'(args, body) -> (get_sexpr sexp_lst body)
    | LambdaOpt'(args,opt,body) -> (get_sexpr sexp_lst body)
    | Applic'(rator, rands) -> 
        let operator = (get_sexpr sexp_lst rator) in
        (List.fold_left get_sexpr operator rands)
    | ApplicTP'(rator, rands) -> 
        let operator = (get_sexpr sexp_lst rator) in
        (List.fold_left get_sexpr operator rands)
    | _ -> sexp_lst;;

  let rec expand_pairs sexp_list =
    match sexp_list with
    | [] -> []
    | [x] -> (expand_if_pair x)
    | hd::tl -> (List.append (expand_if_pair hd) (expand_pairs tl))

  and expand_if_pair sexp =
    match sexp with
    | Sexpr(Pair(car, cdr)) -> (List.append (expand_if_pair (make_sexpr car)) (List.append (expand_if_pair (make_sexpr cdr)) [sexp]))
    | Sexpr(Vector(args)) -> (List.append (expand_pairs (List.map make_sexpr args)) [sexp])
    | _ -> [sexp];;

  let rec create_const_table base lst =
    (List.fold_left create_row base lst)
  
  and create_row tbl element =
    let next_offset = (get_next_offset tbl) in
    match element with
    | Sexpr(Pair(car,cdr)) -> List.append tbl [(element, (next_offset, (make_pair_string car cdr tbl)))]
    | Sexpr(Symbol(x)) -> (handle_symbol x tbl)

    | Sexpr(Number(Int(x))) -> List.append tbl [(element, (next_offset, "MAKE_LITERAL_INT(" ^ (string_of_int x) ^ ")"))]
    | Sexpr(Number(Float(x))) -> List.append tbl [(element, (next_offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^ ")"))]
    | Sexpr(Char(x)) -> List.append tbl [(element, (next_offset, "MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code x)) ^ ")"))]
    | Sexpr(String(x)) -> List.append tbl [(element, (next_offset, (handle_string x)))] 
    | Sexpr(Vector(args)) -> (handle_vector args tbl)
    | _ -> tbl

  (* returns -1 if e doesn't have instance in tbl, otherwise it return the offset of e *)
  and get_offset e tbl =
    let filterd = (List.filter (fun(x) -> ((fst x) = e)) tbl) in
    if (filterd = []) 
    then -1
    else fst (snd (List.hd filterd))

  and make_pair_string car cdr tbl =
    let car_offset = get_offset (make_sexpr car) tbl in 
    let cdr_offset = get_offset (make_sexpr cdr) tbl in 
    "MAKE_LITERAL_PAIR(const_tbl+" ^ (string_of_int car_offset) ^ ",const_tbl+" ^ (string_of_int cdr_offset) ^ ")"

  and handle_symbol e tbl =
    let e_offset = get_offset (Sexpr(String(e))) tbl in
    let next_offset = get_next_offset tbl in
    if (e_offset = -1)
      then let new_tbl = (create_row tbl (Sexpr(String(e)))) in
           (handle_symbol e new_tbl)
      else (List.append tbl [(Sexpr(Symbol(e)), (next_offset, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int e_offset) ^ ")" ))])

  and handle_vector args tbl =
    let add_missing_args = (List.fold_left handle_vactor_arg tbl (List.map make_sexpr args)) in
    let string_offsets = (List.map (get_vec_string add_missing_args) (List.map make_sexpr args)) in
    let offsets_as_string = handle_string_offsets string_offsets in
    List.append add_missing_args [(Sexpr(Vector(args)), ((get_next_offset add_missing_args),"MAKE_LITERAL_VECTOR " ^ offsets_as_string ^ ""))]

  and handle_vactor_arg tbl arg =
    let arg_offset = get_offset arg tbl in
    if (arg_offset = -1)
      then (create_row tbl arg)
      else tbl

  and get_vec_string tbl arg = 
    "const_tbl+" ^ (string_of_int (get_offset arg tbl))

  and handle_string_offsets string_offsets = 
  match string_offsets with
  | [] -> ""
  | [x] -> x
  | hd::tl -> hd ^ ", " ^ (handle_string_offsets tl)

  and handle_string s = 
    let lst = string_to_list s in
    let fixed_lst = (List.map (fun (c) -> (string_of_int (Char.code c))) lst) in
    let s_as_char_vector = handle_string_offsets fixed_lst in
    "MAKE_LITERAL_STRING " ^ s_as_char_vector ^ ""

  and get_next_offset tbl = 
    let last_row = (List.hd (List.rev tbl)) in
    let last_offset = (fst (snd last_row)) in
    let last_type = (fst last_row) in
    match last_type with
    | Void -> last_offset+1 
    | Sexpr(Nil) -> last_offset+1
    | Sexpr(Bool(x)) -> last_offset+2
    | Sexpr(Char(x)) -> last_offset+2
    | Sexpr(Number(x)) -> last_offset+9
    | Sexpr(String(x)) -> last_offset+1+8+(String.length x)
    | Sexpr(Symbol(x)) -> last_offset+9
    | Sexpr(Pair(car,cdr)) -> last_offset+1+8+8
    | Sexpr(Vector(args)) -> last_offset+1+8+(8*(List.length args))
    
  let make_consts_tbl asts =
    let const_list_head = 
           [(Void, (0, "MAKE_VOID"));
            (Sexpr(Nil), (1, "MAKE_NIL"));
            (Sexpr(Bool false), (2, "MAKE_BOOL(0)"));
            (Sexpr(Bool true), (4, "MAKE_BOOL(1)"));] in
    let sexpr_list = (List.fold_left get_sexpr [Void; Sexpr(Nil); Sexpr(Bool false); Sexpr(Bool true)] asts) in
    let expanded_sexpr_list = (remove_duplications (expand_pairs sexpr_list)) in (* expand sub-constants of all Pairs *)
    (create_const_table  const_list_head (remove_first_4_elements expanded_sexpr_list))


  let print_tbl tbl =
    String.concat "\n" (List.map (fun(a, (b,c)) -> c) tbl);;

  (********* end of constant table *********)
    
  (********* fvars table *********)
  let rec get_fvars base expr =
    match expr with
    | Var'(VarFree(x)) -> 
        if(List.mem x base) 
            then base
            else (List.append base [x])
    | BoxSet'(v,e) -> (get_fvars base e)
    | If'(c,t,e) -> 
        let cond = (get_fvars base c) in
        let dit = (get_fvars cond t) in
        (get_fvars dit e)
    | Seq'(x) -> (List.fold_left get_fvars base x)
    | Set'(v,e) -> (get_fvars (get_fvars base v) e)
    | Def'(v,e) -> (get_fvars (get_fvars base v) e)
    | Or'(x)-> (List.fold_left get_fvars base x)
    | LambdaSimple'(args, body) -> (get_fvars base body)
    | LambdaOpt'(args,opt, body) -> (get_fvars base body)
    | Applic'(rator, rands) -> 
        let operator = (get_fvars base rator) in
        (List.fold_left get_fvars operator rands)
    | ApplicTP'(rator, rands) -> 
        let operator = (get_fvars base rator) in
        (List.fold_left get_fvars operator rands)
    | _ -> base
  
  let rec make_fvar_tuples lst index = 
    match lst with 
    | [] -> []
    | [x] -> [(x, index)]
    | hd :: tl -> (List.append [(hd, index)] (make_fvar_tuples tl (index+1)))
  
  let make_fvars_tbl asts = 
    let prim_fvars = (List.map (fun(prim,label) -> prim) primitive_names_to_labels) in
    let fvars_list = (List.fold_left get_fvars prim_fvars asts) in
    (make_fvar_tuples fvars_list 0)
    
  (********* end of fvars table *********)

  (********* generate consts fvars *********)

  let find_indx_of_fvar fvars name =
  try
    (snd (List.hd (List.filter ( fun((var,idx)) -> var = name ) fvars)))
  with e -> raise (Exp (Printf.sprintf "var %s wasnt found on fvar-table" name))

  let lables_ref = {contents = 0};;

  let inc_ref counter =
    let helper = {contents = 0} in
      if((counter := !counter + 1) = (helper := !helper + 1)) 
      then !counter
      else !counter;;

  let rec generate depth width consts fvars e = (* num of arsgs of current lambda *)
    match e with
      | Const'(x) -> 
          let debug_start = Printf.sprintf 
            ";;Generate Const':\n\n" in
          let const_row = List.find (fun (const, (_, _)) -> expr'_eq (Const' x) (Const' const)) consts in
          let offset = (fun (_, (off, _)) -> off) const_row in
          let code = Printf.sprintf 
            "mov rax, const_tbl+%d\n\n" offset in
          let debug_end = Printf.sprintf
            ";;end of Generate Const' \n\n" in
          debug_start ^ code ^ debug_end

      | Var'(VarFree(name)) -> 
          let debug_start = Printf.sprintf 
            ";;Generate VarFree(%s):\n\n" name in
          let index = (find_indx_of_fvar fvars name) in
          let code = Printf.sprintf 
            "mov rax, FVAR(%d)\n\n" index in
          let debug_end = Printf.sprintf
            ";;end of Generate VarFree \n\n" in
          debug_start ^ code ^ debug_end
          
      | Var'(VarParam(name, minor)) ->
          let debug_start = Printf.sprintf 
            ";;Generate VarParam(%s,%d):\n\n" name minor in
          let code = Printf.sprintf 
            "mov rax, qword[rbp+8*(4+%d)]\n\n" minor in
          let debug_end = Printf.sprintf
            ";;end of Generate VarParam \n\n" in
          debug_start ^ code ^ debug_end
      
      | Var'(VarBound(name, major, minor)) ->
          let debug_start = Printf.sprintf 
            ";;Generate VarBound(%s,%d,%d):\n\n" name major minor in
          let code = Printf.sprintf
            "
            mov rax, qword[rbp+8*2]
            mov rax, qword[rax+8*%d]
            mov rax, qword[rax+8*%d]\n\n" major minor in
          let debug_end = Printf.sprintf
            ";;end of Generate VarBound \n\n" in
          debug_start ^ code ^ debug_end

      | Set'(Var'(VarParam(name, minor)),exp) ->
          let debug_start = Printf.sprintf 
            ";;Generate Set'(Var'(VarParam(%s, %d)),exp):\n\n" name minor in
          let generate_exp = (generate depth width consts fvars exp) in
          let code = generate_exp ^ Printf.sprintf
            "
            mov qword[rbp+8*(4+%d)], rax
            mov rax, SOB_VOID_ADDRESS\n\n" minor in
          let debug_end = Printf.sprintf
            ";;end of Generate Set(VarParam) \n\n" in
          debug_start ^ code ^ debug_end

      | Set'(Var'(VarBound(name, major, minor)),exp) ->
        let debug_start = Printf.sprintf 
          ";;Generate Set'(Var'(VarBound(%s, %d, %d)),exp):\n\n" name major minor in
        let generate_exp = (generate depth width consts fvars exp) in
        let code = generate_exp ^ Printf.sprintf
          "
          mov rbx, qword [rbp + 8 * 2]
          mov rbx, qword [rbx + 8 * %d]
          mov qword [rbx + 8 * %d], rax
          mov rax, SOB_VOID_ADDRESS\n\n" major minor in
        let debug_end = Printf.sprintf
          ";;end of Generate Set(VarBound) \n\n" in
        debug_start ^ code ^ debug_end

      
      | Set'(Var'(VarFree(name)),exp) ->
        let debug_start = Printf.sprintf 
          ";;Generate Set'(Var'(VarFree(%s)),exp):\n\n" name in
        let generate_exp = (generate depth width consts fvars exp) in
        let index = (find_indx_of_fvar fvars name) in
        let code = generate_exp ^ Printf.sprintf
          "
          mov qword FVAR(%d), rax
          mov rax, SOB_VOID_ADDRESS\n\n" index in
        let debug_end = Printf.sprintf
          ";;end of Generate Set(VarFree)\n\n" in
        debug_start ^ code ^ debug_end

      | Seq'(seq) ->
        let debug_start = Printf.sprintf 
          ";;Generate Seq'(seq):\n\n" in
        let code = 
          (List.fold_left (^) "" (List.map (generate depth width consts fvars) seq)) in
        let debug_end = Printf.sprintf
          ";;end of Generate Seq'(seq)\n\n" in
        debug_start ^ code ^ debug_end

      | Or'(seq) -> 
        let or_exit_lbl = 
          "ORexit" ^ (string_of_int (inc_ref lables_ref)) in
        let debug_start = Printf.sprintf 
          ";;Generate Or'(seq):\n\n" in
        let generate_exps = (List.map (generate depth width consts fvars) seq) in
        let str_to_add = Printf.sprintf 
          "
          cmp rax, SOB_FALSE_ADDRESS
          jne %s\n" or_exit_lbl in
        let final_string = (List.map (fun (s) -> s ^ str_to_add) generate_exps) in
        let code = 
          (List.fold_left (^) "" final_string) ^ Printf.sprintf "%s:\n\n" or_exit_lbl in
        let debug_end = Printf.sprintf
          ";;end of Generate Or'(seq)\n\n" in
        debug_start ^ code ^ debug_end

      | If'(c,t,e) ->
        let if_exit_lbl = "IFexit" ^ (string_of_int (inc_ref lables_ref)) in
        let else_lbl = "Lelse" ^ (string_of_int (inc_ref lables_ref)) in
        let debug_start = Printf.sprintf 
          ";;Generate If'(cond,dit,dif):\n\n" in
        let cond = 
          ";;generate condition:\n\n" ^
          (generate depth width consts fvars c) ^ Printf.sprintf
          "cmp rax, SOB_FALSE_ADDRESS
          je %s\n\n" else_lbl in
        let dit = 
          ";;generate dit:\n\n" ^
          (generate depth width consts fvars t) ^ Printf.sprintf
          "jmp %s\n%s:\n" if_exit_lbl else_lbl in
        let dif = 
          ";;generate dif:\n\n" ^
          (generate depth width consts fvars e) ^ Printf.sprintf
          "%s:\n\n" if_exit_lbl in
        let code = 
          cond ^ dit ^ dif in
        let debug_end = Printf.sprintf
          ";;end of Generate If'(cond,dit,dif)\n\n" in
        debug_start ^ code ^ debug_end

      | BoxGet'(v) ->
        let debug_start = Printf.sprintf 
          ";;Generate BoxGet'(var):\n\n" in
        let generate_var = (generate depth width consts fvars (Var' v)) in
        let code = 
          generate_var ^ 
          "mov rax, qword[rax]\n\n" in
        let debug_end = Printf.sprintf
          ";;end of Generate BoxGet'(var)\n\n" in
          debug_start ^ code ^ debug_end

      | BoxSet'(v,e) ->
        let debug_start = Printf.sprintf 
          ";;Generate BoxSet'(var, exp):\n\n" in
        let generate_exp = (generate depth width consts fvars e) in
        let generate_var = (generate depth width consts fvars (Var' v)) in
        let code = 
          generate_exp ^ "push rax\n" ^
          generate_var ^ 
          "
          pop qword[rax]
          mov rax, SOB_VOID_ADDRESS\n\n" in
        let debug_end = Printf.sprintf
          ";;end of Generate BoxSet'(var, exp)\n\n" in
        debug_start ^ code ^ debug_end

      | Box'(VarParam(var, minor)) ->
        let debug_start = Printf.sprintf 
          ";;Generate Box'(Var'(VarParam(%s,%d))):\n\n" var minor in
        let code = Printf.sprintf
          "
          mov r8, qword[rbp+8*(4+%d)] ;;save the address of var at r8
          MALLOC r9, 8                ;;allocate 8 bytes (save address in r9) for address of sob
          mov qword[r9], r8           ;;put the value of r8 (the saved value of var) inside the adress that allocated at r9
          mov rax, r9
          " minor in
        let debug_end = Printf.sprintf
          ";;end of Generate Box'(Var'(VarParam(%s,%d)))\n\n" var minor in
        debug_start ^ code ^ debug_end

      | Def'(Var'(v), value) ->
        let generate_value = (generate depth width consts fvars value) in
        (match v with
          | VarFree(var) ->
            let debug_start = Printf.sprintf 
              ";;Generate Def'(VarFree(%s), value):\n\n" var in
            let index_of_fvar = (find_indx_of_fvar fvars var) in
            let addres = Printf.sprintf "fvar_tbl+8*%d" index_of_fvar in
            let code = generate_value ^ Printf.sprintf
              "
              mov [%s], rax
              mov rax, SOB_VOID_ADDRESS\n\n" addres in
            let debug_end = Printf.sprintf
              ";;end of Generate Def'(VarFree(%s), value)\n\n" var in
            debug_start ^ code ^ debug_end

          | VarParam(var, minor) ->
            let debug_start = Printf.sprintf 
              ";;Generate Def'(VarParam(%s,%d), value):\n\n" var minor in
            let addres = Printf.sprintf "rbp+8∗(4+%d)" minor in
            let code = generate_value ^ Printf.sprintf
              "
              mov [%s], rax
              mov rax, SOB_VOID_ADDRESS\n\n" addres in
            let debug_end = Printf.sprintf
              ";;end of Generate Def'(VarParam(%s,%d), value)\n\n" var minor in
            debug_start ^ code ^ debug_end

          | VarBound(var, major, minor) ->
            let debug_start = Printf.sprintf 
              ";;Generate Def'(VarBound(%s,%d,%d), value):\n\n" var major minor in
            let code = generate_value ^ Printf.sprintf
              "
              mov rbx, qword [rbp+8*2]
              mov rbx, qword [rbx+8*%d]
              mov qword [rbx+8*%d], rax
              mov rax, SOB_VOID_ADDRESS\n\n" major minor in
            let debug_end = Printf.sprintf
              ";;end of Generate Def'(VarBound(%s,%d,%d), value)\n\n" var major minor in
            debug_start ^ code ^ debug_end
        )
      
      | LambdaSimple'(args,body) ->
        let debug_start = Printf.sprintf 
          ";;Generate LambdaSimple'(args,body):\n\n" in
        let generate_body = (generate (depth+1) (List.length args) consts fvars body) in

        let code_lbl = "Lcode" ^ (string_of_int (inc_ref lables_ref)) in
        let cont_lbl = "Lcont" ^ (string_of_int (inc_ref lables_ref)) in
        let ext_env = Printf.sprintf
        "
        ;;allocate new env: |new_env| = 1+|old_env|
        MALLOC r8, 8*(1+%d)       ;;r8 = ext_env
        mov r9, qword[rbp+8*2]    ;;r9 = old_env

        EXT_ENV_STEP_1 %d, r8, r9 ;;ext_env[i+1] <-- old_env[i]

        MALLOC r12, 8*%d          ;;r12 = target array for ext_env[0]

        EXT_ENV_STEP_2 %d, r12    ;;ext_env[0] <-- qword[rbp+8*i]

        mov [r8], r12

        ;;PSAUDO CODE:
        ;; for i = 0 to |old_env|:
        ;;    new_env[i+1] <-- old_env[i]  (* every cell is 8 bytes, address of array of parameters! *)
        ;;
        ;; allocate array in size n (rbp+ + 8*3) - the amount of paramaters of the current stack
        ;; for i = 0 to n-1:
        ;;    new_env[0] <-- qword[rbp+8*i]
        ;;
        ;; finally - save the addres of new_env at r8!!!
        " depth depth width width in
        let make_closure = Printf.sprintf
        "
        MAKE_CLOSURE(rax,r8,%s)
        jmp %s
        " code_lbl cont_lbl in
        let closure_body = Printf.sprintf
          "
          %s:
            push rbp
            mov rbp, rsp
            ;;body:
            %s
            ;;end body   
            leave
            ret
          " code_lbl generate_body in
        let continue = cont_lbl ^ ":\n\n" in

        let code = ext_env ^ make_closure ^ closure_body ^ continue in
        let debug_end = Printf.sprintf
          ";;end of Generate LambdaSimple'(args,body)\n\n" in
        debug_start ^ code ^ debug_end

      | LambdaOpt'(args,opt,body) -> 
        let debug_start = Printf.sprintf 
          ";;Generate LambdaOpt'(args,opt,body):\n\n" in
        let generate_body = (generate (depth+1) ((List.length args)+1) consts fvars body) in

        let code_lbl = "Lcode" ^ (string_of_int (inc_ref lables_ref)) in
        let cont_lbl = "Lcont" ^ (string_of_int (inc_ref lables_ref)) in
        let ext_env = Printf.sprintf
        "
        ;;allocate new env: |new_env| = 1+|old_env|
        MALLOC r8, 8*(1+%d)       ;;r8 = ext_env
        mov r9, qword[rbp+8*2]    ;;r9 = old_env

        EXT_ENV_STEP_1 %d, r8, r9 ;;ext_env[i+1] <-- old_env[i]

        MALLOC r12, 8*%d          ;;r12 = target array for ext_env[0]

        EXT_ENV_STEP_2 %d, r12    ;;ext_env[0] <-- qword[rbp+8*i]

        mov [r8], r12

        ;;PSAUDO CODE:
        ;; for i = 0 to |old_env|:
        ;;    new_env[i+1] <-- old_env[i]  (* every cell is 8 bytes, address of array of parameters! *)
        ;;
        ;; allocate array in size n (rbp+ + 8*3) - the amount of paramaters of the current stack
        ;; for i = 0 to n-1:
        ;;    new_env[0] <-- qword[rbp+8*i]
        ;;
        ;; finally - save the addres of new_env at r8!!!
        " depth depth width width in
        let make_closure = Printf.sprintf
        "
        MAKE_CLOSURE(rax,r8,%s)
        jmp %s
        " code_lbl cont_lbl in
        let arg_len = (List.length args) in
        let loop_lbl = "Lopt" ^ (string_of_int (inc_ref lables_ref)) in
        let end_loop_lbl = "Lopt_end" ^ (string_of_int (inc_ref lables_ref)) in
        let adjust_stack = Printf.sprintf
        "
        ;;PSAUDO CODE:
        ;; n <- [rbp +8*3]
        ;; m <- Length(args)
        ;;
        ;; while (n-m > 0)
        ;;    [rbp+8*(4+n)] <- Pair([rbp+8*(4+n)],[rbp+8*(5+n)])
        ;;    n--

        mov r11, qword[rbp+8*3]   ;; r10 <- n
        cmp r11, %d
        je %s
 
        dec r11                   ;; r11 <- n-1

        mov rcx, qword[rbp+8*3]   ;; rcx <- n
        sbb rcx, %d               ;; rcx <- n-m

        %s:
          LAMBDA_OPT_MAKE_PAIRS r11, r12, 4
          mov r14, [r12]

          LAMBDA_OPT_MAKE_PAIRS r11, r13, 5
          mov r13, [r13]

          MAKE_PAIR(r9, r14, r13)
          mov [r12], r9
          dec r11
          dec rcx
          jnz %s
        %s:
        " arg_len end_loop_lbl arg_len loop_lbl loop_lbl end_loop_lbl in
        let closure_body = Printf.sprintf
          "
          %s:
            push rbp
            mov rbp, rsp
            ;;adjust stack
            %s
            ;;end adjust stack
            ;;body:
            %s
            ;;end body   
            leave
            ret
          " code_lbl adjust_stack generate_body in
        let continue = cont_lbl ^ ":\n\n" in

        let code = ext_env ^ make_closure ^ closure_body ^ continue in
        let debug_end = Printf.sprintf
          ";;end of Generate LambdaSimple'(args,body)\n\n" in
        debug_start ^ code ^ debug_end

      | Applic'(rator, rands) ->
        let debug_start = Printf.sprintf 
          ";;Generate Applic'(rator, rands):\n\n" in
        let push_magic = "push SOB_NIL_ADDRESS\n\n" in
        let push_args = 
          (List.fold_left 
            (fun acc exp ->
                acc ^ 
                ";;generate arg:\n" ^
                (generate depth width consts fvars exp) ^
                "push rax
                ;;end of generate arg\n")
            ""
            (List.rev rands)) in
        let generate_rator = (generate depth width consts fvars rator) in
        let call = Printf.sprintf
          "
          push %d
          CLOSURE_ENV rbx, rax  ;;rax contains closure object, CLOSURE_ENV preform: rbx <-- rax+1    i.e the address to the env
          push rbx
          CLOSURE_CODE rbx, rax ;;rax contains closure object, CLOSURE_CODE preform: rax <-- rax+1+8    i.e the address to the code
          call rbx
          " (List.length rands) in
        let restore_stack = 
          "
          add rsp, 8*1    ;; pop env
          pop rbx         ;; pop arg count
          add rbx, 1      ;; add 1 for magic
          shl rbx, 3      ;; rbx = rbx * 8
          add rsp, rbx    ;; pop args
          \n\n" in
        let code = push_magic ^ push_args ^ generate_rator ^ call ^ restore_stack in
        let debug_end = Printf.sprintf
          ";;end of Generate Applic'(rator, rands)\n\n" in
        debug_start ^ code ^ debug_end

      | ApplicTP'(rator, rands) -> 
        let debug_start = Printf.sprintf 
          ";;Generate ApplicTP'(rator, rands):\n\n" in
        let push_magic = "push SOB_NIL_ADDRESS\n\n" in
        let push_args = 
          (List.fold_left 
            (fun acc exp ->
                acc ^ 
                ";;generate arg:\n" ^
                (generate depth width consts fvars exp) ^
                "push rax
                ;;end of generate arg\n")
            ""
            (List.rev rands)) in
        let generate_rator = (generate depth width consts fvars rator) in
        let new_frame_size = (4 + (List.length rands)) in
        let call = Printf.sprintf
          "
          push %d                 ;; push n
          CLOSURE_ENV rbx, rax    ;; rbx <-- rax+1 (Closure.env) 
          push rbx                ;; push env
          push qword[rbp+8]       ;; push return address
          
          CLOSURE_CODE rbx, rax   ;; rbx <-- rax+9 (Closure.code) 
          mov r10, qword[rbp]     ;; r10 <-- backup rbp
          mov r13, PARAM_COUNT    ;; r13 <--backup old n
          
          SHIFT_FRAME %d          ;; overwrite old frame

          add r13, 5              ;; calculate new rsp
          MUL8 r13                ;; calculate new rsp
          add rsp, r13            ;; set new rsp

          mov rbp, r10            ;; set rbp
          jmp rbx                 ;; call code
          " (List.length rands) new_frame_size  in
        let code = push_magic ^ push_args ^ generate_rator ^ call in
        let debug_end = Printf.sprintf
          ";;end of Generate ApplicTP'(rator, rands)\n\n" in
        debug_start ^ code ^ debug_end

      | _ -> "un-handled"
  
  (********* end of generate consts fvars *********)

  (* REMOVE *)
  (* returns suitable expr' for string s *)
 (* let test s = run_semantics (tag_parse_expression (read_sexpr s)) *)
  let test s = annotate_lexical_addresses (tag_parse_expression (read_sexpr s))
end;;


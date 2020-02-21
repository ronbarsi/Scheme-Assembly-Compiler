(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

(* -------- helpers --------*)

let inc_counter_ref counter =
  let helper = {contents = 0} in
  if((counter := !counter + 1) = (helper := !helper + 1)) 
  then !counter
  else !counter;;

(* -------- helpers --------*)

(* -------lexical addresses--------- *)

let rec get_index obj lst len = (* returns -1 if obj is not member of lst. otherwise, returns it's index *)
  match lst with
  | [] -> -len -1
  | head :: tail when obj = head -> 0
  | head :: tail -> 1 + (get_index obj tail len)
  (* -> if (obj = head) then 0 else (get_index obj tail) + 1 *)

let rec handle_vars e = 
  match e with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(VarFree(x)) (* TODO: check if its ok!!!! *)
  | If(c,t,e) -> If'((handle_vars c), (handle_vars t), (handle_vars e))
  | Seq(x) -> Seq'(List.map handle_vars x)
  | Set(v,exp) -> Set'((handle_vars v), (handle_vars exp))
  | Def(v,exp) -> Def'((handle_vars v), (handle_vars exp))
  | Or(x) -> Or'(List.map handle_vars x)
  | LambdaSimple(args, body) -> LambdaSimple'(args, (handle_lambda_vars args body))
  | LambdaOpt(args, opt, body) -> LambdaOpt'(args, opt, (handle_lambda_vars (List.append args [opt]) body))
  | Applic(rator, rands) -> Applic'((handle_vars rator), (List.map handle_vars rands))

and handle_lambda_vars args body = (* return body as expr' *)
  let body_with_params = (handle_params args body) in
  (handle_bounds args body_with_params)

and handle_params args body = (* body is expr *)
  match body with
  | Const(x) -> Const'(x)
  | Var(x) -> if (List.mem x args) then Var'(VarParam(x, (get_index x args (List.length args)))) else Var'(VarFree(x))
  | If(c,t,e) -> If'((handle_params args c), (handle_params args t), (handle_params args e))
  | Seq(x) -> Seq'(List.map (handle_params args) x)
  | Set(v,exp) -> Set'((handle_params args v), (handle_params args exp))
  | Def(v,exp) -> Def'((handle_params args v), (handle_params args exp))
  | Or(x) -> Or'(List.map (handle_params args) x)
  | LambdaSimple(args, body) -> LambdaSimple'(args, (handle_lambda_vars args body))
  | LambdaOpt(args, opt, body) -> LambdaOpt'(args, opt, (handle_lambda_vars (List.append args [opt]) body))
  | Applic(rator, rands) -> Applic'((handle_params args rator), (List.map (handle_params args) rands))


and handle_bounds args body = (* body is expr' *)
  (* step 1 - for each arg at args - search for it's bound insances *)
  let step_1 = (List.fold_left (find_bound (-1)  args) body args) in
  (* step 2 - for each inner lambda instance - call handle_bounds *)
  let step_2 = (inner_lambda_handler step_1) in
  step_2

and find_bound major_index arg_list body arg = (* mark all the bound instances of arg*)
  let minor_index = (get_index arg arg_list (List.length arg_list)) in
  match body with
 
  | Var'(VarFree(x)) when x = arg -> Var'(VarBound(x, major_index, minor_index))
  | LambdaSimple'(inner_args, inner_body) -> 
          LambdaSimple'(inner_args, (handle_lambda_bound_vars inner_args inner_body arg major_index minor_index arg_list))
  | LambdaOpt'(inner_args, opt, inner_body) -> 
          LambdaOpt'(inner_args, opt, (handle_lambda_bound_vars inner_args inner_body arg major_index minor_index arg_list))

  | If'(c,t,e) -> If'((find_bound major_index arg_list c arg),
                      (find_bound major_index arg_list t arg),
                      (find_bound major_index arg_list e arg))
  | Set'(v,e) -> Set'((find_bound major_index arg_list v arg),
                      (find_bound major_index arg_list e arg))
  | Def'(v,e) -> Def'((find_bound major_index arg_list v arg),
                      (find_bound major_index arg_list e arg))
  | Seq'(x) -> Seq'((List.map (find_bound_helper major_index arg_list arg)  x))
  | Or'(x) -> Or'((List.map (find_bound_helper major_index arg_list arg)  x))
  | Applic'(rator, rands) -> Applic'((find_bound major_index arg_list rator arg),
                                     (List.map (find_bound_helper major_index arg_list arg) rands))
  | _ -> body

(* switch the order of the parameters - only for use List.map *)
and find_bound_helper major_index arg_list arg body = (find_bound major_index arg_list body arg)

(* 
instead of duplicate code for lambdaOpt and lambdaSimple.
arg_list - args of the inner lambda
body - body of the inner lambda
arg - the variable we search for
orig_args - the original arg_list, just for calling find_bound again
 *)
and handle_lambda_bound_vars arg_list body arg major_index minor_index orig_args =
  if (List.mem arg arg_list)
  then body
  else (find_bound (major_index +1) orig_args body arg)

and inner_lambda_handler body =
  match body with
  | LambdaSimple'(inner_args, inner_body) -> 
          LambdaSimple'(inner_args, (handle_bounds inner_args inner_body))
  | LambdaOpt'(inner_args, opt, inner_body) -> 
          LambdaOpt'(inner_args, opt, (handle_bounds (List.append inner_args [opt]) inner_body))
  | If'(c,t,e) -> If'((inner_lambda_handler c),
                      (inner_lambda_handler t),
                      (inner_lambda_handler e))
  | Set'(v,e) -> Set'((inner_lambda_handler v),
                      (inner_lambda_handler e))
  | Def'(v,e) -> Def'((inner_lambda_handler v),
                      (inner_lambda_handler e))
  | Seq'(x) -> Seq'((List.map inner_lambda_handler x))
  | Or'(x) -> Or'((List.map inner_lambda_handler x))
  | Applic'(rator, rands) -> Applic'((inner_lambda_handler rator),
                                     (List.map inner_lambda_handler rands))
  | _ -> body


(* -------lexical addresses--------- *)

(* -------tail calls--------- *)

let get_last lst =
  let reversed = (List.rev lst) in
  List.hd reversed

let remove_last lst =
  let reversed = (List.rev lst) in
  List.rev (List.tl reversed)

let rec handle_tail_calls in_tp exp = (* TODO - if exp is from the start not-lambda expresion, in_tp = true? *)
  match exp with
  | If'(c,t,e) -> If'((handle_tail_calls false c), (handle_tail_calls in_tp t), (handle_tail_calls in_tp e))
  (* for lists like in Or' and Seq':
     we call handle_tail_calls with false on the first n-1 elements of the list, and with in_tp to the last element of the list*)
  | Or'(x) -> Or'((List.append
                      (List.map (handle_tail_calls false) (remove_last x))
                      ([(handle_tail_calls in_tp (get_last x))])))
  | Seq'(x) -> Seq'((List.append
                      (List.map (handle_tail_calls false) (remove_last x))
                      ([(handle_tail_calls in_tp (get_last x))])))
  | Set'(v,e) -> Set'((handle_tail_calls false v), (handle_tail_calls false e))
  | Def'(v,e) -> Def'((handle_tail_calls false v), (handle_tail_calls false e))
  | LambdaSimple'(args, body) -> LambdaSimple'(args, (handle_tail_calls true body))
  | LambdaOpt'(args, opt, body)-> LambdaOpt'(args, opt, (handle_tail_calls true body))
  | Applic'(rator, rands) -> 
      if (in_tp = true) 
      then ApplicTP'((handle_tail_calls false rator), (List.map (handle_tail_calls false) rands))
      else Applic'((handle_tail_calls false rator), (List.map (handle_tail_calls false) rands))
  | _ -> exp


(* -------tail calls--------- *)

(* -------box--------- *)

(* returns expr' list of lambdas which x has read instance inside them *)
let rec read_check is_first_lambda counter v body = (* v is Var' and body is expr' *) 
  match body with
  | Var'(VarBound(x, _, _)) when (x = v) -> [!counter] (* indicator of Var' *)
  | Var'(VarParam(x, _)) when (x = v) -> if(is_first_lambda = true) then [0] else []
  | If'(c,t,e) -> (List.append (read_check is_first_lambda counter v c) 
                    (List.append (read_check is_first_lambda counter v t) (read_check is_first_lambda counter v e)))
  | Or'(x) -> (List.fold_left List.append [] (List.map (read_check is_first_lambda counter v) x))                    
  | Seq'(x) -> (List.fold_left List.append [] (List.map (read_check is_first_lambda counter v) x))
  | Set'(n,e) -> (read_check_set is_first_lambda counter v n e)
  | Applic'(rator, rands) -> (List.append (read_check is_first_lambda counter v rator) (List.fold_left List.append [] 
                            (List.map (read_check is_first_lambda counter v) rands)))
  | ApplicTP'(rator, rands) -> (List.append (read_check is_first_lambda counter v rator) (List.fold_left List.append [] 
                            (List.map (read_check is_first_lambda counter v) rands)))
  | LambdaSimple'(args, b) -> (read_check_lambda args is_first_lambda counter v b body)
  | LambdaOpt'(args, opt, b)-> (read_check_lambda (List.append args [opt]) is_first_lambda counter v b body)
  | BoxSet'(n,e) -> (read_check is_first_lambda counter v e)
  | Def'(n,e) -> raise X_syntax_error
  | _ -> []

and read_check_set is_first_lambda counter v n e =
  match n with
  | Var'(VarBound(x, _, _)) when (x = v) -> (read_check is_first_lambda counter v e)
  | Var'(VarParam(x, _)) when (x = v) -> (read_check is_first_lambda counter v e)
  | _ -> (List.append (read_check is_first_lambda counter v n) (read_check is_first_lambda counter v e)) 

and read_check_lambda args is_first_lambda counter v inner_body body = 
  if(List.mem v args) 
  then []
  else
    let new_counter_val = (inc_counter_ref counter) in
    if ((read_check false counter v inner_body) = [])
    then []
    else [new_counter_val]
  
let rec write_check is_first_lambda counter v body = (* v is Var' and body is expr' *) 
  match body with
  | If'(c,t,e) -> (List.append (write_check is_first_lambda counter v c) 
                (List.append (write_check is_first_lambda counter v t) (write_check is_first_lambda counter v e)))
  | Or'(x) -> (List.fold_left List.append [] (List.map (write_check is_first_lambda counter v) x)) 
  | Seq'(x) -> (List.fold_left List.append [] (List.map (write_check is_first_lambda counter v) x))
  | Set'(Var'(VarBound(x, _, _)), e) when (x = v) -> (List.append [!counter] (write_check is_first_lambda counter v e))
  | Set'(Var'(VarParam(x, _)), e) when (x = v) -> 
              let rec_call = (write_check is_first_lambda counter v e) in
              if(is_first_lambda = true) then (List.append [0] rec_call) else rec_call
  | Set'(n,e) -> (List.append (write_check is_first_lambda counter v n) (write_check is_first_lambda counter v e))
  | Applic'(rator, rands) -> (List.append (write_check is_first_lambda counter v rator) 
                    (List.fold_left List.append [] (List.map (write_check is_first_lambda counter v) rands)))
  | ApplicTP'(rator, rands) -> (List.append (write_check is_first_lambda counter v rator) 
                        (List.fold_left List.append [] (List.map (write_check is_first_lambda counter v) rands)))
  | LambdaSimple'(args, b) -> (write_check_lambda args is_first_lambda counter v b body)
  | LambdaOpt'(args, opt, b)-> (write_check_lambda (List.append args [opt]) is_first_lambda counter v b body)
  | BoxSet'(n,e) -> (write_check is_first_lambda counter v e)
  | Def'(n,e) -> raise X_syntax_error
  | _ -> [] 

and write_check_lambda args is_first_lambda counter v inner_body body =
  if(List.mem v args) then []
  else 
    let new_counter_val = (inc_counter_ref counter) in
    if ((write_check false counter v inner_body) = [])
        then []
        else [new_counter_val]
  
(* in case that the two lists are not empty the function checks if there are vars that should be boxed*)
let check_lists read_list write_list = 
  let cartesian_product = List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) write_list) read_list) in
  let lst = (List.map (fun e -> if ((fst e) = (snd e)) then false else true) cartesian_product) in
  if (List.mem true lst) then true else false
  
(* returns true if v should be boxed in body (function B) *)
let should_be_boxed body v =
  let r_counter = {contents = 0} in
  let w_counter = {contents = 0} in
  let read_list =  (read_check true r_counter v body) in
  let write_list =  (write_check true w_counter v body) in
  if((read_list = []) || (write_list = []))
  then false
  else (check_lists read_list write_list)
    
let rec handle_box exp = 
  match exp with
  | If'(c,t,e) -> If'((handle_box c), (handle_box t), (handle_box e))
  | Or'(x) -> Or'((List.map handle_box x))            
  | Seq'(x) -> Seq'((List.map handle_box x))
  | Set'(n,e) -> Set'((handle_box n), (handle_box e))
  | Def'(n,e) -> Def'((handle_box n), (handle_box e))
  | Applic'(rator, rands) -> Applic'((handle_box rator), (List.map handle_box rands))
  | ApplicTP'(rator, rands) -> ApplicTP'((handle_box rator), (List.map handle_box rands))
  | BoxSet'(n,e) -> BoxSet'(n, (handle_box e))
  | LambdaSimple'(args, b) -> LambdaSimple'(args,(handle_box_lambda args b))
  | LambdaOpt'(args, opt, b)-> LambdaOpt'(args, opt,(handle_box_lambda (List.append args [opt]) b))
 
  | _ -> exp

(* 
step 1 - box-get all the read-occurrnesses of vars that should be boxed in the lambda andbox-set the write-occurrnesses as well.
important: if var x should be boxed and x is member in arglist of inner lambda - step 1 will skip it!

step 2 - for each var x that should be boxed: add the expr "Set'(x, Box'(x))" at the beggining of the body.

step 3 - handle_box_lambda for each inner lambda in the body.

*)
and handle_box_lambda args body = 
  let target_box_list = (get_var_list args body) in
  let step1 = (List.fold_left box_top_level_var body target_box_list) in
  let step2 = (add_set_expressions step1 target_box_list args) in
  let step3 = (activate_on_inner_lambdas step2) in
  step3

and box_top_level_var body v =
  match body with 
  | Var'(VarBound(x, major, minor)) when (x = v) -> BoxGet'(VarBound(x, major, minor))
  | Var'(VarParam(x, minor)) when (x = v) -> BoxGet'(VarParam(x, minor))

  | Set'(Var'(VarParam(x, minor)), e) when x = v -> BoxSet'(VarParam(x, minor), (box_top_level_var e v))
  | Set'(Var'(VarBound(x, major, minor)), e) when x = v -> BoxSet'(VarBound(x, major, minor), (box_top_level_var e v))
  | Set'(n, e) -> Set'((box_top_level_var n v), (box_top_level_var e v))
  | BoxSet'(n,e) -> BoxSet'(n, (box_top_level_var e v)) 

  | LambdaSimple'(args, b) -> 
      if (List.mem v args)
      then body
      else LambdaSimple'(args, (box_top_level_var b v))
  | LambdaOpt'(args, opt, b)-> 
      if (List.mem v (List.append args [opt]))
      then body
      else LambdaOpt'(args, opt, (box_top_level_var b v))
   
  | If'(c,t,e) -> If'((box_top_level_var c v), (box_top_level_var t v), (box_top_level_var e v))
  | Def'(n,e) -> Def'((box_top_level_var n v), (box_top_level_var e v))
  | Or'(x) -> Or'((List.map (box_top_level_var_helper v) x))            
  | Seq'(x) -> Seq'((List.map (box_top_level_var_helper v) x))
  | Applic'(rator, rands) -> Applic'((box_top_level_var rator v), (List.map (box_top_level_var_helper v) rands))
  | ApplicTP'(rator, rands) -> ApplicTP'((box_top_level_var rator v), (List.map (box_top_level_var_helper v) rands))
 
  | _ -> body 

and box_top_level_var_helper v body = (box_top_level_var body v)

and add_set_expressions body args_to_box orig_args =
  let set_list = (generate_set_list args_to_box orig_args) in
  if(set_list = [])
  then body
  else Seq'(List.append set_list [body])

and generate_set_list args_to_box orig_args =
  (List.map (generate_set orig_args) args_to_box)

and generate_set orig_args v =
  let var_param = VarParam(v, (get_index v orig_args (List.length orig_args))) in
  Set'(Var'(var_param), Box'(var_param))

and activate_on_inner_lambdas body = 
  match body with
  | LambdaSimple'(inner_args, inner_body) -> 
          LambdaSimple'(inner_args, (handle_box_lambda inner_args inner_body))
  | LambdaOpt'(inner_args, opt, inner_body) -> 
          LambdaOpt'(inner_args, opt, (handle_box_lambda (List.append inner_args [opt]) inner_body))

  | If'(c,t,e) -> If'((activate_on_inner_lambdas c),
                      (activate_on_inner_lambdas t),
                      (activate_on_inner_lambdas e))
  | Set'(v,e) -> Set'((activate_on_inner_lambdas v),
                      (activate_on_inner_lambdas e))
  
  | BoxSet'(v,e) -> BoxSet'(v, activate_on_inner_lambdas e) 
  | Def'(v,e) -> Def'((activate_on_inner_lambdas v),
                      (activate_on_inner_lambdas e))
  | Seq'(x) -> Seq'((List.map activate_on_inner_lambdas x))
  | Or'(x) -> Or'((List.map activate_on_inner_lambdas x))
  | Applic'(rator, rands) -> Applic'((activate_on_inner_lambdas rator),
                                     (List.map activate_on_inner_lambdas rands))
  | ApplicTP'(rator, rands) -> ApplicTP'((activate_on_inner_lambdas rator),
                                     (List.map activate_on_inner_lambdas rands))
  | _ -> body

and get_var_list args body =
  match args with 
  | [] -> []
  | [x] -> 
      if((should_be_boxed body x))
      then [x]
      else []
  | hd :: tl -> 
      if((should_be_boxed body hd))
      then (List.append [hd] (get_var_list tl body))
      else (get_var_list tl body)

(* -------box--------- *)

let annotate_lexical_addresses e = (handle_vars e)
  
let annotate_tail_calls e = (handle_tail_calls false e)

let box_set e = (handle_box e)

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)

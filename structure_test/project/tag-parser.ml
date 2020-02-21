(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(*****HELP FUNCTION*****)

let rec is_proper s = (** returns true also for Nil!!!!!!!!!!!!!!!! *)
	match s with
		| Nil -> true
		| Pair(f,r) -> (is_proper r) 
		| _ -> false;;
	
let is_pair s = 
	match s with
	| Pair(x,y) -> true
	| _ -> false;;

let rec pair_proper_to_list s = (**works only for proper list! *)
  match s with
  | Nil -> []
  | Pair(Symbol(f), r) -> List.append [f] (pair_proper_to_list r)
  | Pair(Pair(Symbol(f), r) , x) -> List.append [f] (pair_proper_to_list r)
	| _ -> [];;

let rec pair_improper_to_list s = (**works for both proper and improper list! *)
  match s with
  | Nil -> []
  | Symbol(x) -> [x]
  | Pair(Symbol(f), r) -> List.append [f] (pair_improper_to_list r)
  | Pair(Pair(Symbol(f), r) , x) -> List.append [f] (pair_improper_to_list r)
	| _ -> raise X_syntax_error;;

let rec get_N_minus_1_first_arguments lst =
  match lst with
  | [] -> []
  | [x] -> []
  | _ -> List.append [(List.hd lst)] (get_N_minus_1_first_arguments (List.tl lst));;

let rec get_last_argument lst = 
  match lst with
  | [] -> ""
  | [x] -> x
  | _ -> get_last_argument (List.tl lst);;

let get_x_from_symbol sym = 
  match sym with
  | Symbol(x) -> x
  | _ -> "";;

let rec dup_checker myList blackList =
  match myList with
  | [] -> false
  | _ -> let head = (List.hd myList) in
    if (List.mem head blackList)
    then true
    else (dup_checker (List.tl myList) (List.append [head] blackList));;

(* ------ COSNSTANT ------- *)

let const_tag_parser s = 
    match s with 
    | Bool(x) -> Const(Sexpr(Bool(x)))
    | Number(x) -> Const(Sexpr(Number(x)))
    | Char(x) -> Const(Sexpr(Char(x)))
    | String(x) -> Const(Sexpr(String(x)))
    | Pair(Symbol("quote"), Pair(x,Nil)) -> Const(Sexpr(x))
    | Pair(Symbol("unquote"), Pair(x,Nil)) -> Const(Sexpr(x))
    | _ -> raise X_syntax_error;;
    
let var_tag_parser s = 
    match s with
    | Symbol(x) -> 
        if(List.mem x reserved_word_list) then raise X_syntax_error
        else Var(x)
    | _ -> raise X_syntax_error;;
        
let rec expr_tag_parser s = 
    try const_tag_parser s
    with X_syntax_error -> 
        try var_tag_parser s
        with X_syntax_error ->
    match s with 
    | Pair (Symbol "if",Pair (test, Pair (dit, Nil))) -> 
                    If((expr_tag_parser test), (expr_tag_parser dit), Const(Void)) (*if expr*)
    | Pair (Symbol "if",Pair (test, Pair (dit, Pair (dif, Nil)))) -> 
                    If((expr_tag_parser test), (expr_tag_parser dit), (expr_tag_parser dif)) (*if-else expr*)
    
    | Pair (Symbol "set!", Pair(Symbol(var), Pair(value, Nil))) ->           
                    Set((expr_tag_parser (Symbol(var))), (expr_tag_parser value)) (*set expr*)

    | Pair (Symbol "or" ,Nil) -> Const(Sexpr(Bool(false))) (*start of or expr*)
    | Pair (Symbol "or" ,Pair(exp, Nil)) -> (expr_tag_parser exp)
    | Pair (Symbol "or" ,lst) -> Or((sexp_to_expr_list lst)) (*end of or expr*)
    

    | Pair (Symbol "define", Pair(Pair (Symbol(var), arglist), exp)) -> (expr_tag_parser (handle_MIT_define var arglist exp))
    | Pair (Symbol "define", Pair(var, Pair(exp, Nil))) -> Def((var_tag_parser var), (expr_tag_parser exp)) (*define exp*)
    
  
    | Pair (Symbol "lambda", Pair(arglist, Pair(body, Nil))) -> (handle_lambda arglist (Pair(body, Nil)))     
    | Pair (Symbol "lambda", Pair(Pair (arglist, Pair(body, Nil)), Nil)) -> (handle_lambda arglist body) 
    | Pair (Symbol "lambda", Pair(arglist, body)) -> (handle_lambda arglist body) 
    
    | Pair (Symbol "begin" ,Nil) -> Const(Void) (*empty sequence*)
    | Pair (Symbol "begin" ,Pair(exp, Nil)) -> (expr_tag_parser exp) (*sequence with one element*)
    | Pair (Symbol "begin" ,lst) -> Seq((sexp_to_expr_list lst)) (*sequence*)

    | Pair (Symbol "and" ,s) -> (expr_tag_parser (handle_and s))

      

    | Pair (Symbol "let", Pair(ribs, body)) -> (expr_tag_parser (handle_let ribs body))

    | Pair (Symbol "let*", Pair(ribs, body)) -> (expr_tag_parser (handle_let_star ribs body))

    | Pair (Symbol "letrec", Pair(ribs, body)) -> (expr_tag_parser (handle_let_rec ribs body))

    | Pair (Symbol "cond", rest) -> (expr_tag_parser (handle_cond rest))

    | Pair(Symbol("quasiquote"), Pair(exp,Nil)) -> (expr_tag_parser (handle_quasi exp))

    | Pair (op , rands) -> Applic((expr_tag_parser op), (sexp_to_expr_list rands)) 
  
    | _ -> raise X_syntax_error


and sexp_to_expr_list s =
    match s with
    | Nil -> []
    | Pair(Symbol("quote"), Pair(x,Nil)) -> [(expr_tag_parser s)]
    | Pair(f, r) -> List.append [(expr_tag_parser f)] (sexp_to_expr_list r)
    | _ -> raise X_syntax_error

and symbol_checker lst =
  let head = (List.hd lst) in
  match lst, head with
  | [], _ -> false
  | _, Symbol(x) -> (symbol_checker (List.tl lst))
  | _, _ -> true

and handle_lambda arglist body =
  let arglist_as_list = (pair_improper_to_list arglist) in
  let expr_body = (implicit_seq body) in
  
  if (dup_checker arglist_as_list []) (*|| (symbol_checker arglist_as_list))*)
  then
    raise X_syntax_error
  else
    if ((is_pair arglist) && (is_proper arglist))
    then
      LambdaSimple(arglist_as_list, expr_body)
    else
      if ((is_pair arglist))
      then
        LambdaOpt((get_N_minus_1_first_arguments arglist_as_list),
                  (get_last_argument arglist_as_list),
                  expr_body)
      else
        if ((List.length arglist_as_list) = 0) (** empty arglist *)
        then 
          LambdaSimple([], expr_body)
        else
          LambdaOpt([], (List.hd arglist_as_list), expr_body)

and implicit_seq lst =
  match lst with
  | Pair(Symbol("let*"), rest) -> Seq([expr_tag_parser lst])
  | Pair(Symbol("if"), rest) -> (expr_tag_parser lst)
  | _ ->
    let exp_list = (sexp_to_expr_list lst) in
    if (List.length exp_list = 0)
    then 
      raise X_syntax_error
    else
      if (List.length exp_list = 1)
      then
        (List.hd exp_list)
      else
        Seq(exp_list)

and handle_and s =
  match s with
  | Nil -> Bool(true)
  | Pair(exp, Nil) -> exp
  | Pair(curr, sexp) -> Pair (Symbol("if"), Pair(curr, Pair(Pair(Symbol("and"), sexp), Pair(Bool(false), Nil))))
  | _ -> s

and handle_let ribs body =
  match ribs with
  | Nil -> Pair(Pair(Symbol "lambda", Pair(Pair (Nil, Pair(body, Nil)), Nil)), Nil)
  | Pair(Pair(var, Pair(value, Nil)), Nil) -> Pair(Pair(Symbol "lambda", Pair(Pair (Pair(var, Nil), Pair(body, Nil)), Nil)), Pair(value,Nil))
  | Pair(Pair(var,Pair(value,Nil)), rest) ->
      let vars = (take_vars ribs) in
      let vals = (take_vals ribs) in
      Pair(Pair(Symbol "lambda", Pair(Pair (vars, Pair(body, Nil)), Nil)), vals)
  | _ -> raise X_syntax_error

and take_vars ribs = 
  match ribs with
  | Pair(Pair(var,Pair(value,Nil)), rest) -> Pair(var, (take_vars rest))
  | _ -> Nil

and take_vals ribs = 
  match ribs with
  | Pair(Pair(var,Pair(value,Nil)), rest) -> Pair(value, (take_vals rest))
  | _ -> Nil

and handle_let_star ribs body =
let seq_body = Pair(Symbol "begin",body) in
  match ribs with
  | Nil -> Pair (Symbol "let", Pair (Nil, Pair (seq_body, Nil)))
  | Pair(Pair(var,Pair(value,Nil)), Nil) -> Pair (Symbol "let", Pair(Pair(Pair (var, Pair (value, Nil)), Nil), Pair (seq_body, Nil)))
  | Pair(Pair(var,Pair(value,Nil)), rest) -> 
    let body_let = Pair(Symbol "let*", Pair(rest, Pair(seq_body, Nil))) in
    Pair (Symbol "let", Pair(Pair(Pair (var, Pair (value, Nil)), Nil), Pair (body_let, Nil)))
  | _ -> raise X_syntax_error

and handle_let_rec ribs body =
  match ribs with
  | Nil -> Pair (Symbol "let", Pair (Nil, Pair (Pair(Symbol "begin", body), Nil)))
  | Pair(Pair(var,Pair(value,Nil)), rest) ->
      let new_ribs = (take_vars_let_rec ribs) in
      let new_body = (set_vals ribs body) in
      Pair (Symbol "let", Pair (new_ribs, Pair (Pair(Symbol "begin", new_body), Nil)))
  | _ -> raise X_syntax_error

and take_vars_let_rec ribs = 
  match ribs with
  | Pair(Pair(var,Pair(value,Nil)), rest) -> Pair(Pair(var, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)),Nil)), (take_vars_let_rec rest))
  | _ -> Nil

and set_vals ribs body = 
  match ribs with
  | Nil -> body
  | Pair(Pair(var,Pair(value,Nil)), Nil) -> Pair(Pair(Symbol("set!"), Pair(var, Pair(value,Nil))), body)
  | Pair(Pair(var,Pair(value,Nil)), rest) -> Pair(Pair(Symbol("set!"), Pair(var, Pair(value,Nil))), (set_vals rest body))
  | _ -> Nil

and handle_MIT_define var arglist exp =
  let var_name = Symbol(var) in 
  let lambda_body = Pair (Symbol "lambda", Pair(arglist, exp)) in
  Pair (Symbol "define", Pair(var_name, Pair(lambda_body, Nil)))

and handle_cond conditions =
  match conditions with
  | Pair(Pair(Symbol "else",dit), Nil) -> 
        Pair(Symbol "begin", dit) 
  (*(cond (test 1) (test => 2))*)
  | Pair(Pair(test,Pair(Symbol "=>",Pair(f_expr, Nil))),Nil) ->
        let f_lambda = Pair(Symbol "lambda",Pair(Nil,Pair(f_expr,Nil))) in
        let ribs = Pair(Pair(Symbol "value",Pair(test,Nil)),Pair(Pair(Symbol "f",Pair(f_lambda,Nil)),Nil)) in
        let dit = Pair(Pair(Symbol "f",Nil), Pair(Symbol "value",Nil)) in 
        let body = Pair(Symbol "if",Pair(Symbol "value",Pair(dit,Nil))) in
        Pair (Symbol "let", Pair(ribs, Pair(body, Nil)))
  (*(cond (test 1) (test => 2) (test 3))*)
  | Pair(Pair(test,Pair(Symbol "=>",Pair(f_expr, Nil))),rest_of_conds) ->
        let f_lambda = Pair(Symbol "lambda",Pair(Nil,Pair(f_expr,Nil))) in
        let rest_lambda = Pair(Symbol "lambda",Pair(Nil,Pair(Pair(Symbol "cond", rest_of_conds),Nil)))  in
        let ribs = Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(Pair(Symbol "f", Pair(f_lambda, Nil)),
                        Pair(Pair(Symbol "rest", Pair(rest_lambda, Nil)), Nil))) in
        let dit = Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)) in
        let body = Pair(Symbol "if",Pair(Symbol "value", Pair(dit, Pair(Pair(Symbol "rest", Nil), Nil)))) in
        Pair (Symbol "let", Pair(ribs, Pair(body, Nil)))
  | Pair(Pair(test,dit), Nil) ->  
        let new_dit = Pair(Symbol "begin", dit) in
        Pair (Symbol "if",Pair (test, Pair (new_dit, Nil)))
  | Pair(Pair(test,dit), rest) ->  
        let new_dit = Pair(Symbol "begin", dit) in
        let dif = Pair(Symbol "cond", rest) in
        Pair (Symbol "if",Pair (test, Pair (new_dit, Pair (dif, Nil)))) 
  | _ -> raise X_syntax_error

and handle_quasi exp =

  match exp with

  | Pair(Symbol("unquote"), Pair(x,Nil)) -> x
  | Pair(Symbol("unquote-splicing"), rest) -> raise X_syntax_error
  | Nil -> Pair(Symbol("quote"), Pair(Nil,Nil))
  | Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x),Nil))
  | Vector(x) ->
      let exp_list = (List.map handle_quasi x) in
      let exp_pair = (lst_as_nested_pairs exp_list) in
      Pair(Symbol("vector"), exp_pair)
 
  | Pair(Pair (Symbol "unquote-splicing", Pair (car, Nil)),cdr) -> (*(,@a b)*)
         Pair(Symbol("append"), Pair(car, Pair((handle_quasi cdr), Nil)))

  | Pair(car, Pair (Pair (Symbol "unquote-splicing", Pair (cdr, rest)), Nil(*rest*))) -> (*(a ,@b)*)
         Pair(Symbol("cons"), Pair((handle_quasi car), Pair(Pair(Symbol("append"), Pair(cdr, Pair((handle_quasi rest),Nil))), Nil)))

  | Pair(car, Pair(Symbol("unquote-splicing"), Pair(cdr, Nil))) -> (*(a . ,@b)*)
         Pair(Symbol("cons"), Pair((handle_quasi car), Pair(cdr, Nil))) 

  | Pair(car, cdr) -> Pair(Symbol("cons"), Pair((handle_quasi car), Pair((handle_quasi cdr), Nil)))

  | _ -> exp

and lst_as_nested_pairs lst =
match lst with
| [] -> Nil
| [x] -> Pair(x, Nil)
| _ -> Pair((List.hd lst), (lst_as_nested_pairs (List.tl lst)));;


let tag_parse_expression sexpr = (expr_tag_parser sexpr);;

let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;


end;; (* struct Tag_Parser *)


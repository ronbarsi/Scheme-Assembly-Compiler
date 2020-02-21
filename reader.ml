(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

(*#use "reader.ml";;*)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> 
      (try
        List.for_all2 sexpr_eq l1 l2
      with Invalid_argument(x) -> false)
      
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(* ---USEFUL SYMBOLS--- *)
let hash_tag_parser = PC.char '#';;
let left_paren_parser = PC.word "(";;
let right_paren_parser = PC.word ")";;
let left_bparen_parser = PC.word "[";;
let right_bparen_parser = PC.word "]";;
let open_paren = PC.disj left_bparen_parser left_paren_parser;;
let close_paren = PC.disj right_bparen_parser right_paren_parser;;
let three_dots_parser = PC.word "...";;
let hex_num_prefix_parser = PC.word_ci "#X";;
let digit_parser = PC.range '0' '9';;
let e_parser = PC.char_ci 'e';;
let dot_parser s =
  let dot = PC.char '.' in
  PC.pack dot (fun(s) -> s) s;;

let whitespaces_parser = PC.pack (PC.const (fun (ch) -> int_of_char ch <= 32 )) (fun (e) -> Nil);;

let line_comments_parser s =
  let semicolon = PC.char ';' in
  let everychar = PC.star (PC.const (fun (ch) -> ch != '\n')) in (*every char except \n*)
  let end_of_input = PC.const (fun (e) -> (int_of_char e) >= 0) in (*every char*)
  let enter = PC.char '\n' in
  let optionA = PC.caten semicolon (PC.caten everychar enter) in
  let optionB = PC.caten semicolon (PC.caten everychar (PC.pack (PC.not_followed_by (PC.word "") end_of_input) (fun(e) -> char_of_int 0)) ) in
  let line_comments = PC.disj optionA optionB in
  PC.pack line_comments (fun (e) -> Nil) s;;

let symbol_char_noDigit_parser s =
  let a_to_z = PC.range 'a' 'z' in
  let cA_to_cZ = PC.range 'A' 'Z' in
  let special_char = PC.const (fun (ch) -> ch = '!'
                                        || ch = '$'
                                        || ch = '^'
                                        || ch = '*'
                                        || ch = '-'
                                        || ch = '_'
                                        || ch = '='
                                        || ch = '+'
                                        || ch = '>'
                                        || ch = '<'
                                        || ch = '?'
                                        || ch = ':'
                                        || ch = '/' ) in
  let symbol_char = PC.disj a_to_z (PC.disj cA_to_cZ special_char) in
  PC.pack symbol_char (fun (ch) ->
                        let ch_ascii = (int_of_char ch) in
                        if(ch_ascii>=65 && ch_ascii<=90) then (char_of_int (ch_ascii+32))
                        else ch) s;;

  let symbol_char_parser s =
  let symbol_char = PC.disj digit_parser symbol_char_noDigit_parser in
  PC.pack symbol_char (fun (ch) -> ch) s;;

let symbol_parser s =
  let symbol = PC.plus symbol_char_parser in
  PC.pack symbol (fun (s) -> Symbol((list_to_string s))) s;;

(* ---BOOLEAN--- *)

let bool_parser s =
  let f_parser = PC.caten hash_tag_parser (PC.char_ci 'f') in
  let packed_false = PC.pack f_parser (fun (f) -> Bool(false)) in
  let t_parser = PC.caten hash_tag_parser (PC.char_ci 't') in
  let packed_true = PC.pack t_parser (fun (t) -> Bool(true)) in
  let bool = PC.not_followed_by (PC.disj packed_true packed_false) symbol_char_parser in
  bool s;;

(* ---CHAR--- *)

let char_prefix_parser s =
  let prefix = PC.word_ci "#\\" in
  PC.pack prefix (fun (f) -> Nil) s;; (*TODO: Nil is ok???*)

let visible_simple_char_parser s =
  let visible_simple_char = PC.const (fun (ch) -> (int_of_char ch) > 32) in
  PC.pack visible_simple_char (fun (ch) -> Char(ch)) s;;

let named_char_parser s =
  let nul_parser = PC.word_ci "NUL" in
  let nul = PC.pack nul_parser (fun(e) -> char_of_int 0) in
  let page_parser = PC.word_ci "PAGE" in
  let page = PC.pack page_parser (fun (e) -> char_of_int 12) in
  let space_parser = PC.word_ci "SPACE" in
  let space = PC.pack space_parser (fun (e) -> char_of_int 32) in
  let tab_parser = PC.word_ci "TAB" in
  let tab = PC.pack tab_parser (fun (e) -> char_of_int 9) in
  let return_parser = PC.word_ci "RETURN" in
  let returnn = PC.pack return_parser (fun (e) -> char_of_int 13) in
  let newline_parser = PC.word_ci "NEWLINE" in
  let newline = PC.pack newline_parser (fun (e) -> char_of_int 10) in
  let named_char = PC.disj nul (PC.disj page (PC.disj space (PC.disj tab (PC.disj returnn newline)))) in
  PC.pack named_char (fun (ch) -> Char(ch)) s;;

let hex_digit_parser s =
  let a_to_f = PC.range 'a' 'f' in
  let cA_to_cF = PC.range 'A' 'F' in
  let hex_digit = PC.disj digit_parser (PC.disj a_to_f cA_to_cF) in
  PC.pack hex_digit (fun (ch) -> ch) s;;


let hex_char_to_int ch =
  if (ch >= '0' &&  ch <= '9') then ((int_of_char ch)-48)
  else (if (ch >= 'a' &&  ch <= 'f') then ((int_of_char ch)-87)
        else ((int_of_char ch)-55))

let rec hex_to_int s acc =
  match s with
  | "" -> acc
  | _ -> hex_to_int (String.sub s 1 ((String.length s)-1)) ((acc*16) + (hex_char_to_int s.[0]))

let hex_char_parser s =
  let x = PC.char_ci 'x' in
  let plus_hex = PC.plus hex_digit_parser in
  let hex_char = PC.caten x plus_hex in
  PC.pack hex_char (fun (s1) ->
    let final_char = hex_to_int (list_to_string (snd s1)) 0 in
      if (final_char > 127)
      then raise PC.X_no_match
      else Char(char_of_int final_char)) s;;

let char_parser s =
  let disjj = PC.disj hex_char_parser (PC.disj named_char_parser visible_simple_char_parser)in
  let char = PC.not_followed_by (PC.caten char_prefix_parser disjj) symbol_char_parser in
  PC.pack char (fun (ch) -> (snd ch)) s;;

(* ---STRING--- *)

let string_hex_char_parser s =
  let back_slash = PC.char '\\' in
  let x = PC.char_ci 'x' in
  let semicolon = PC.char ';' in
  let plus_hex_digit = PC.plus hex_digit_parser in
  let string_hex_char = PC.caten back_slash (PC.caten x (PC.caten plus_hex_digit semicolon)) in
  PC.pack string_hex_char (fun (s1) -> char_of_int (hex_to_int (list_to_string (fst (snd (snd s1)))) 0)) s;;

let string_meta_char_parser s =
  let metachar_prefix = PC.word "\\" in
  let meta = PC.const (fun(ch) -> ch ='t' || ch = 'f' || ch = 'n' || ch ='r' || ch = '\"' || ch = '\\') in
  let string_meta_char = PC.caten metachar_prefix meta in
  PC.pack string_meta_char (fun (ch) -> if((snd ch) = 't') then '\t'
                                        else if((snd ch) = 'f') then char_of_int 12
                                        else if((snd ch) = 'n') then '\n'
                                        else if((snd ch) = 'r') then '\r'
                                        else if((snd ch) = '\"') then '\"'
                                        else '\\') s;;

let string_literal_char_parser s =
  let string_literal_char = PC.const (fun (ch) -> (int_of_char ch) != 92
                                               && (int_of_char ch) != 34 ) in
  PC.pack string_literal_char (fun (ch) -> ch) s;;

let string_char_parser s =
  let string_char = PC.disj string_hex_char_parser (PC.disj string_meta_char_parser string_literal_char_parser) in
  PC.pack string_char (fun (ch) -> ch) s;;

let string_parser s = 
  let double_qoute_parser = PC.char (char_of_int 34) in
  let char_star =  PC.star string_char_parser in
  let sstring = PC.caten double_qoute_parser (PC.caten char_star double_qoute_parser) in
  PC.pack sstring (fun (s) -> String(list_to_string (fst (snd s)))) s;;

(* ---NUMBER--- *)

let natural_parser s =
  let natural = PC.plus digit_parser in
  PC.pack natural (fun (n) -> int_of_string (list_to_string n)) s;;
  
let sign_parser s =
  let sign = PC.const (fun(s) -> s = '+' || s = '-') in
  PC.pack sign (fun(s) -> s) s;;

let signed_int_parser s =
  let integer = PC.caten sign_parser natural_parser in
  PC.pack integer (fun(s) -> if((fst s) = '-') then (-1)*(snd s) else (snd s)) s;;
  
let regular_int_parser s = 
  let integer = PC.plus digit_parser in 
  PC.pack integer (fun(s) -> int_of_string (list_to_string s)) s;; 

let int_parser s =
  let final = PC.not_followed_by (PC.disj signed_int_parser regular_int_parser) symbol_char_noDigit_parser in
  PC.pack final (fun(s) -> Number(Int(s))) s;;

let regular_float_parser s =
  let float_helper = PC.plus digit_parser in
  let floatnum = PC.caten float_helper (PC.caten dot_parser float_helper) in   (* charlist* (char * (charlist) *)
  PC.pack floatnum (fun(s) -> float_of_string(list_to_string((List.append (fst s) (List.append ['.'] (snd (snd s))))))) s;;
  
let signed_float_parser s =
  let floatnum = PC.caten sign_parser regular_float_parser in
  PC.pack floatnum (fun(s) -> if ((fst s) = '-') then ((-1.0)*.(snd s)) else (snd s)) s;;
  
let float_parser s =
  let disj = PC.not_followed_by (PC.disj regular_float_parser signed_float_parser) symbol_char_noDigit_parser in
  PC.pack disj (fun(s) -> Number(Float(s))) s;;
  
let regular_hex_integer s = 
  let hexint = PC.plus hex_digit_parser in
  let hexnum = PC.caten hex_num_prefix_parser hexint in
  PC.pack hexnum (fun(s) -> int_of_string(list_to_string(List.append ['0'] (List.append ['x'] (snd s))))) s;;
  
let signed_hex_integer s =
  let hex_int = PC.plus hex_digit_parser in
  let signed_hex = PC.caten hex_num_prefix_parser (PC.caten sign_parser hex_int) in
  PC.pack signed_hex (fun(s) -> if (fst (snd s) = '-') 
                                then (-1)*int_of_string(list_to_string(List.append ['0'] (List.append ['x'] (snd (snd s)))))  
                                else int_of_string(list_to_string(List.append ['0'] (List.append ['x'] (snd (snd s)))))) s;; 
                                
let hexint_parser s = 
   let disj = PC.not_followed_by (PC.disj regular_hex_integer signed_hex_integer) symbol_char_noDigit_parser in
   PC.pack disj (fun(s) -> Number(Int(s))) s;;
   
let regular_hex_float s =
   let hex_int = PC.plus hex_digit_parser in
   let dot = PC.char '.' in
   let hex_float = PC.caten hex_num_prefix_parser (PC.caten hex_int (PC.caten dot hex_int)) in
   PC.pack hex_float (fun(s) -> 
   float_of_string(list_to_string (List.append ['0'] (List.append ['x'] (List.append (fst (snd s)) (List.append ['.'] (snd (snd (snd s))))))))) s;; 
   
let signed_hex_float s =
   let hex_int = PC.plus hex_digit_parser in
   let dot = PC.char '.' in
   let hex_float = PC.caten hex_num_prefix_parser (PC.caten sign_parser (PC.caten hex_int (PC.caten dot hex_int))) in
   PC.pack hex_float (fun(s) -> if((fst (snd s))='-')
                                then 
                                (-1.0)*.float_of_string(list_to_string (List.append ['0'] 
                                (List.append ['x'] (List.append (fst (snd (snd s))) (List.append ['.'] (snd (snd (snd (snd s)))))))))
                                else float_of_string(list_to_string (List.append ['0'] 
                                (List.append ['x'] (List.append (fst (snd (snd s))) (List.append ['.'] (snd (snd (snd (snd s)))))))))) s;;

let hexfloat_parser s = 
   let disj = PC.not_followed_by (PC.disj regular_hex_float signed_hex_float) symbol_char_noDigit_parser in
   PC.pack disj (fun(s) -> Number(Float(s))) s;;
                   
let sn_int_parser s =
   let integer = PC.disj signed_int_parser regular_int_parser in
   let num = PC.caten integer (PC.caten e_parser integer) in
   PC.pack num (fun(s) -> 
                  let first_num = float_of_int (fst s) in
                  let exp_num = float_of_int (snd (snd s)) in
                  let f_res = first_num *. (10.0 ** exp_num) in
                  Float(f_res)) s;;

let sn_float_parser s = 
   let integer = PC.disj signed_int_parser regular_int_parser in
   let float_num = PC.disj signed_float_parser regular_float_parser in
   let num = PC.caten float_num (PC.caten e_parser integer) in
   PC.pack num (fun(s) ->
                   let first_num = (fst s) in
                   let exp_num = float_of_int (snd (snd s)) in 
                   let f_res = first_num *. (10.0 ** exp_num) in
                   Float(f_res)) s;;
                   
let scientific_notation_num_parser s = 
   let num = PC.not_followed_by (PC.disj sn_float_parser sn_int_parser) symbol_char_noDigit_parser in
   PC.pack num (fun(s) -> Number(s)) s;;
   
let number_parser s = PC.disj scientific_notation_num_parser 
                         (PC.disj float_parser (PC.disj int_parser (PC.disj hexfloat_parser hexint_parser))) s;;

(* ---SEXPR--- *)

let rec sexpr_parser s =
  let sexpr_disjoint = PC.disj_list [bool_parser;
                            char_parser;
                            number_parser;
                            string_parser;
                            symbol_parser;
                            list_parser;
                            dottedlist_parser;
                            vector_parser;
                            quoted_parser;
                            quasiquoted_parser;
                            unquoted_spliced_parser;
                            unquoted_parser;
                            sexpr_comments_parser;
                            auto_balance_parser] 
                            in
  let skipable = PC.pack (PC.star (PC.disj_list [sexpr_comments_parser; line_comments_parser; whitespaces_parser])) (fun (e)->Nil) in                 
  let sexpr = PC.caten skipable (PC.caten sexpr_disjoint skipable) in
  PC.pack sexpr (fun(e) -> fst(snd e)) s

and list_parser s =
  let skip = PC.star (PC.disj_list [sexpr_comments_parser; line_comments_parser; whitespaces_parser]) in
  let sexpr_star = PC.star sexpr_parser in
  let reg_list = PC.caten left_paren_parser (PC.caten skip (PC.caten sexpr_star right_paren_parser)) in
  let b_list = PC.caten left_bparen_parser (PC.caten skip (PC.caten sexpr_star right_bparen_parser)) in
  let list = PC.disj reg_list b_list in
  PC.pack list (fun (e) -> 
    let lst = (fst (snd (snd e))) in
    match lst with
    | [] -> Nil
    | _  -> List.fold_right (fun acc el -> Pair(acc,el)) lst Nil) s

and dottedlist_parser s =
  let sexpr_plus = PC.plus sexpr_parser in
  let reg_dottedlist = PC.caten left_paren_parser (PC.caten sexpr_plus (PC.caten dot_parser (PC.caten sexpr_parser right_paren_parser))) in
  let b_dottedlist = PC.caten left_bparen_parser (PC.caten sexpr_plus (PC.caten dot_parser (PC.caten sexpr_parser right_bparen_parser))) in
  let dottedlist = PC.disj reg_dottedlist b_dottedlist in
  PC.pack dottedlist (fun (e) ->
    let head = (fst (snd e)) in
    let tail = (fst (snd (snd (snd e)))) in
    match head with
    | [] -> Nil (* unnecessary *)
    | _  -> List.fold_right (fun acc el -> Pair(acc,el)) head tail) s
    
and vector_parser s = 
  let sexpr_star = PC.star sexpr_parser in
  let vector = PC.caten hash_tag_parser (PC.caten left_paren_parser (PC.caten sexpr_star right_paren_parser)) in
  PC.pack vector (fun (e) ->
    let vec = fst (snd (snd e)) in
    Vector(vec) ) s

and quoted_parser s = 
  let quote = PC.char '\'' in
  let quoted = PC.caten quote sexpr_parser in
  PC.pack quoted (fun (e) ->
    Pair(Symbol("quote"), Pair((snd e), Nil))) s

and quasiquoted_parser s = 
  let quasi = PC.char '`' in
  let qquoted = PC.caten quasi sexpr_parser in
  PC.pack qquoted (fun (e) ->
    Pair(Symbol("quasiquote"), Pair((snd e), Nil))) s

and unquoted_spliced_parser s = 
  let spliced = PC.word ",@" in
  let unquoted_spliced = PC.caten spliced sexpr_parser in
  PC.pack unquoted_spliced (fun (e) ->
    Pair(Symbol("unquote-splicing"), Pair((snd e), Nil))) s

and unquoted_parser s = 
  let comma = PC.char ',' in
  let unquoted = PC.caten comma sexpr_parser in
  PC.pack unquoted (fun (e) ->
    Pair(Symbol("unquote"), Pair((snd e), Nil))) s

and sexpr_comments_parser s =
  let sexpr_comments_prefix = PC.word "#;" in
  let sexpr_comments = PC.caten sexpr_comments_prefix sexpr_parser in
  PC.pack sexpr_comments (fun (e) -> Nil) s

and auto_balance_disj s = 
    let disj = PC.disj_list [(PC.diff sexpr_parser auto_balance_parser);auto_balance_dlist;auto_balance_list;auto_balance_vector] in
    let skip = PC.star (PC.disj_list [sexpr_comments_parser; line_comments_parser; whitespaces_parser]) in
    let a_disj = PC.caten skip (PC.caten disj skip) in
    PC.pack a_disj (fun(e) -> (fst (snd e))) s
    
and auto_balance_parser s =
    let skip = PC.star (PC.disj_list [sexpr_comments_parser; line_comments_parser; whitespaces_parser]) in
    let auto_balance = PC.caten (PC.disj_list [auto_balance_dlist;auto_balance_list;auto_balance_vector]) (PC.caten skip three_dots_parser) in
    PC.pack auto_balance (fun(e) -> fst e) s

and auto_balance_list s = 
    let balanced_list = PC.caten open_paren (PC.caten (PC.star auto_balance_disj) (PC.maybe close_paren)) in
    PC.pack balanced_list (fun(e) -> 
        let sexp_lst = (fst (snd e)) in
        match sexp_lst with
        |[] -> Nil
        | _ -> List.fold_right (fun acc el -> Pair(acc,el)) sexp_lst Nil) s
    
and auto_balance_dlist s =
    let balanced_dotted_list = PC.caten open_paren (PC.caten (PC.plus auto_balance_disj) 
                        (PC.caten dot_parser (PC.caten auto_balance_disj (PC.maybe close_paren)))) in
    PC.pack balanced_dotted_list (fun (e) ->
    let head = (fst (snd e)) in
    let tail = (fst (snd (snd (snd e)))) in
    match head with
    | [] -> Nil (* unnecessary *)
    | _  -> List.fold_right (fun acc el -> Pair(acc,el)) head tail) s
    
and auto_balance_vector s = 
    let balanced_vec = PC.caten hash_tag_parser (PC.caten left_paren_parser 
                                (PC.caten (PC.star auto_balance_disj) (PC.maybe right_paren_parser))) in
    PC.pack balanced_vec (fun(e) ->
    let vec = fst (snd (snd e)) in
    Vector(vec) ) s;;

(*TODO - CHECK WHICH FUNCTION IS RIGHT*)
let read_sexpr string = 
    let res = sexpr_parser (string_to_list string) in
    let rest = snd res in
    match rest with
    | [] -> (fst res)
    | _ -> raise PC.X_no_match;;
    

let read_sexprs string = fst ((PC.star sexpr_parser) (string_to_list string));;
  
end;; (* struct Reader *)

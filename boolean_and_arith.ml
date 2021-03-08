(* A parser and evaluator for a toy boolean language
   Some defs set up for expansion to NB = boolean + arith language
   EXERCISE:  expand parser+evaluator to NB. Both small-step and
              big-step evaluator.
*)

(*
 *
 * concrete syntax:
 * tm --> if tm then tm else tm | true | false
 *
 *typical concrete syntax:
 *  if (if true then false) then false else
    (if true then false else (if true then false else false))


 * abstract syntax:
 * tm --> TmTrue|TmFalse|TmIf(tm,tm,tm)
 *
 * when extended to system (NB), it will be:
 * tm --> TmTrue|TmFalse|TmIf(tm,tm,tm)|TmZero|TmSucc(tm)|
 *        TmPred(tm)|TmIsZero(tm)
 *)

(* utility functions *)

(* converts a string to a list of chars:
   stolen from SML because it's so handy *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;


(* print a list of strings *)
let rec aux_print_list = function
  |[] -> print_string ""
  |(x::xs) -> (print_string x;print_string ":";aux_print_list xs);;

let print_list x =
  (print_string "<";aux_print_list x;print_string ">");;

(* boolean terms *)
type term =
    TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |TmZero
  |TmPred of (term)
  |TmSucc of (term)
  |TmIsZero of (term)
  |TmError

(* to display terms *)
exception NOT_A_VALUE;;

let rec show x =
  match x with
  |TmTrue -> "true"
  |TmFalse -> "false"
  |TmIf(t1,t2,t3) -> "(if "^(show t1)^" then "^(show t2)^" else "^(show t3)^")"
  |TmZero -> "0"
  |TmSucc(t1) -> "(succ "^(show t1)^")"
  |TmPred(t1) -> "(pred "^(show t1)^")"
  |TmIsZero(t1) -> "(isZero "^(show t1)^")"
  |_ -> raise NOT_A_VALUE;;

let print_value x = print_string (show x);;

(* weird: create a string rep of the ABSTRACT syntax *)

(* also OK: let is_a_value x = List.mem x [TmTrue;TmFalse;etc...] *)


(* lexer: breaks up a string into a list of so-called tokens:
   "if true then false else (if true then false else true)" |-->
   ["if";"true";"then";"false";"else";"(";"if";"true";...]
 *)

(* Here tokens just meant strings, but in many lexers, one transforms
   a program to a list of more informative terms,
   e.g. x |-->  ("x", VARIABLE) or ( |--> ("(",LPAREN)
   where VARIABLE and LPAREN are members of a new type called token
      token ::= LPAREN|RPAREN|VARIABLE|BOOLEAN_VALUE   etc.
 *)

(* alph x = true when char x is alphabetical
   you can add new characters, e.g. '_', if you
   want to allow underscores in variable names *)
let alph x =
  let n = Char.code x in
  (96< n && n < 122) || n == 48;;


exception BAD_CHAR
exception BAD_IDENT


(* token boundaries *)
let bdry x = (x='(') || (x= ')') ;;

(* accumulate characters until you reach a blank or a token boundary:
'e' ['l';'s';'e';'(';...] |--> ("else" ['('...])
 *)
let rec grab_chars_until_bdry ch rest =
  match rest with
    |[] -> (String.make 1 ch,rest)
    |(head::tail) ->
       if (head = ' ')
       then (String.make 1 ch,tail)
       else if (bdry head)
       then (String.make 1 ch,rest)
       else let (x,l) = (grab_chars_until_bdry head tail)
       in
	 ((String.make 1 ch)^x,l)
;;

(* char list |--> list of token strings *)
let rec aux_lexx chars =
  match chars with
    |[] -> []
    |(ch::rest) ->
       if (ch=' ')
       then aux_lexx rest
       else if (bdry ch)
       then (String.make 1 ch)::(aux_lexx rest)
       else if (alph ch)
       then
	 let (str, remainder) = grab_chars_until_bdry ch rest
	 in str::(aux_lexx remainder)
       else raise BAD_CHAR;;

(* explode input and apply aux_lexx to the result *)
let lexx x = aux_lexx (explode x);;


(* parser: expand to include arithmetic *)
(*
 * parse applies aux_parse to result of lexx.
 * aux_parse: string list -> term * string list
 * it checks for parentheses and identifiers and
 * calls helper parsers on de-parenthesized terms
 * aux_parse calls parse_if,parse_succ,parse_pred,parse_iszero
 * which checks for parentheses and identifiers and
 * calls aux_parse on de-parenthesized termschecks for parentheses and identifiers and
 * calls aux_parse on de-parenthesized terms
 *)
(* aux_parse : string list -> term * string list = <fun> *)

exception DANGLING_PAREN;;
exception DANGLING_SUCC;;
exception DANGLING_PRED;;
exception DANGLING_ISZERO;;
exception DANGLING_IF;;


let rec aux_parse tokens =
  match tokens with
  |[] -> (TmError,[])
  |("("::rest) ->
    let pair = aux_parse rest in
    begin
    match pair with
    |(_,[]) -> raise DANGLING_PAREN
    |(tm, (")"::remainder_after_rparen)) ->
      (tm,remainder_after_rparen) (* throw away right parenthesis *)
     |_ ->  raise DANGLING_PAREN
    end
  |("true"::rest) -> (TmTrue,rest)
  |("false"::rest) -> (TmFalse,rest)
  |("0"::rest) -> (TmZero,rest)
  |("if"::rest) -> parse_if rest
  |("succ"::rest) -> parse_succ rest
  |("pred"::rest) -> parse_pred rest
  |("isZero"::rest) -> parse_iszero rest
  |_ -> raise BAD_IDENT
and
  parse_if x =
  match x with
  |[] -> raise DANGLING_IF
  |rest ->
    let pair = aux_parse rest in
    match pair with
    |(_,[]) -> raise DANGLING_IF
    |(t1, rest1) ->
    let (tok_then::rest_then) = rest1 in (* throw away then *)
    let (t2, rest2) = aux_parse rest_then in
    let (tok_else::rest_else) = rest2 in (* throw away else *)
    let (t3,rest3) = aux_parse rest_else
    in (TmIf (t1,t2,t3),rest3)
and
  parse_succ x =
  match x with
  |[] -> raise DANGLING_SUCC
  |rest ->
    let pair = aux_parse rest in
    match pair with
    |(t1, rest1) -> (TmSucc(t1), rest1)

and
  parse_pred x =
  match x with
  |[] -> raise DANGLING_PRED
  |rest ->
    let pair = aux_parse rest in
    match pair with
    |(t1, rest1) -> (TmPred(t1), rest1)

and
  parse_iszero x =
  match x with
  |[] -> raise DANGLING_ISZERO
  |rest ->
    let pair = aux_parse rest in
    match pair with
    |(t1, rest1) -> (TmIsZero(t1), rest1)



(* parse:string -> term *)
let parse str =  fst (aux_parse (lexx str));;

(*** evaluation ***)

let rec is_a_numericalval x =
  match x with
  |TmZero -> true
  |TmSucc(t1) -> is_a_numericalval t1
  |TmPred(t1) -> is_a_numericalval t1
  |x -> false

(* identify which terms are values: expand to arithmetic *)
let is_a_value x =
   match x with
   |TmTrue -> true
   |TmFalse -> true
   |t -> is_a_numericalval t


(* also OK: let is_a_value x = List.mem x [TmTrue;TmFalse] *)

exception NO_RULE;;
exception NO_ZERO_RULE
(*
(* single small step eval EXPAND TO INCLUDE arithmetic *)
let rec small_step t =
  match t with
  (* bool eval rules *)
  |TmIf(TmTrue,t2,t3) -> t2
  |TmIf(TmFalse,t2,t3) -> t3
  |TmIf(t1,t2,t3) ->
     let t1' = small_step t1 in
     TmIf(t1',t2,t3)
  |TmSucc(t1) ->
    let t1' = small_step t1 in
    TmSucc(t1')
  |TmIsZero(t1) ->
    let t1' = small_step t1 in
    TmIsZero(t1')
  |TmPred(t1) ->
    let t1' = small_step t1 in
    TmPred(t1')
  |TmPred(TmZero) -> TmZero
  |TmIsZero(TmZero) -> TmTrue
  |TmPred(TmSucc(nv1)) ->
    match is_a_value nv1 with



    |_ -> raise NO_RULE;;

 *)
let rec big_step t =
  match t with
  (* bool eval rules *)
  |TmTrue -> t
  |TmFalse -> t
  |TmIf(TmTrue,t2,t3) -> t2
  |TmIf(TmFalse,t2,t3) -> t3
  |TmIf(t1,t2,t3) ->
    (match big_step t1 with
    |TmTrue -> big_step t2
    |TmFalse -> big_step t3)
  (* arith eval rules *)
  |TmZero -> t
  |TmSucc(t1) -> TmSucc(big_step t1)
  |TmPred(t1) ->
    (match big_step t1 with
     |TmZero -> TmZero
     |TmSucc(t2) -> t2
     |_ ->  raise NO_RULE)
  |TmIsZero(t1) ->
    (match big_step t1 with
     |TmZero -> TmTrue
     |TmSucc _ -> TmFalse
     |_ -> raise NO_ZERO_RULE)
  |_ -> raise NO_RULE
(*
(* and now,  the evaluation sequences it induces *)
let rec eval t =
  if (is_a_value t)
  then t
  else let t' = eval_step t in
    eval t';;

(* works for all normal forms, not just values *)

let rec eval_all t =
  try let t' = eval_step t
  in eval_all t'
  with NO_RULE -> t
 *)
	      (* some examples *)

let print_value x = print_string (show x);;
  
print_string "\n\n******* SOME EXAMPLES ************";;
is_a_value TmTrue;;
is_a_value (TmIf(TmTrue,TmFalse,TmTrue));;
big_step TmTrue;;
big_step (TmIf(TmTrue,TmFalse,TmTrue));;
big_step (TmIf(TmIf(TmTrue,TmFalse,TmTrue),TmTrue,TmFalse));;
(* eval (TmIf(TmIf(TmTrue,TmFalse,TmTrue),TmTrue,TmFalse));; *)



(* infix composition *)
let ($) f g x = f (g x)

(* parse and then evaluate *)
(* let eval_parse = eval $ parse;; 
let eval_all_parse = eval_all $ parse;; *)
let big_eval_parse = big_step $ parse;;


(* some examples to work with *)

  (* eval_parse "if (if true than false else true) then false else true";; *)
big_eval_parse "if (if true than false else true) then false else true";;
(* ss_big_eval_parse "if (if true than false else true) then false else true";; *)

big_eval_parse "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;
    
let pp = print_value $ big_step $ parse;;

pp "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;


pp "if";; (* generates a match failure *)

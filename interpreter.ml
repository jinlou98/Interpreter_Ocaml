(*
Honor code comes here:

First Name: Jin
Last Name: Lou
BU ID: U65306910

I pledge that this program represents my own
program code and that I have coded on my own. I received
help from no one in designing and debugging my program.
I have read the course syllabus of CS 320 and have read the sections on Collaboration
and Academic Misconduct. I also understand that I may be asked to meet the instructor
or the TF for a follow up interview on Zoom. I may be asked to explain my solution in person and
may also ask you to solve a related problem.
*)



open Printf

(* constants that go on the stack *)
type stack_Val = 
  | I of int 
  | B of bool
  | N of string
  | S of string 
  | Unit
  | Error
  (* | R of stackVal *)

(* commands go to interpreter *)
type command = 
  |  Push of stack_Val
  |  Pop
  |  Log
  |  Swap
  |  Add 
  |  Sub 
  |  Mul 
  |  Div 
  |  Rem 
  |  Neg

type commands = command list


(* writing from string to command*)
let rec stack_to_string (l: stack_Val list) (sl : string list) : string list= 
  match l with
  | [] -> sl
  | h::t -> stack_to_string t (match h with
      | I i -> (string_of_int i::sl) 
      | S s  -> s::sl
      | N n -> n::sl
      | B b -> (("<"^string_of_bool b^">")::sl)
      | Unit   -> "<unit>"::sl
      | Error -> "<error>"::sl)


type 'a stack = 'a list

let empty_stack () : 'a stack = []  

type 'a parser = Parser of (string -> ('a * string ) list)

let explode s =
  List.of_seq (String.to_seq s)

let implode ls =
  String.of_seq (List.to_seq ls)

(* run a parser: takes parser, input and return a tuple list  *)
let run_parse p s = 
  match p with 
    Parser f -> f s 

let charP  = 
  Parser (
    fun s ->
      match (explode s) with 
        []->[]
      |
        h::rest->[(h,implode rest)] 
  )

(* ex: parse (return 5) "abcd" = [(5, "abcd")] *)
let returnP a = 
  Parser 
    (
      fun s -> [a,s]
    )

(* Only do one thing: fail and give [] *)
let failP = 
  Parser
    (
      fun s->[]
    )

(* choice parser: There're 2 parsers. If parser 1 does not work, use parser 2 *)
let (<|>) a b = 
  Parser (
    fun s->  match (run_parse a s) with 
        []-> run_parse b s 
      |
        r->r
  )

(* binding parser *)
let (>>=) p f = 
  Parser (
    fun s ->
      match (run_parse p s ) with 
        []->[]     (* this is where the parser p has has failed and you make the bind fail as well *)
      |
        (v, out)::_-> run_parse (f v) out
  )

(* grab the first char and gives back the rest as string  *)
(* parse read "apple" -> [('a',"pple")] *)
let read: char parser = 
  Parser(
    fun cs ->
      match explode cs with
      | c::cs -> [(c,implode cs)]
      | []->[]
  )

(* eg: parse (readn 2) "apple" = [("ap","ple")] *)
(* eg: parse (readn 4) "push 4" = [("push","4")] *)
let rec readn (n:int):string parser=
  if n>0 then 
    read >>= fun c -> 
    readn (n-1) >>= fun cs -> 
    returnP (String.make 1 c^cs)
  else
    returnP ""

(* we want to read more, such as string*)
(* eg: parse (string "push") "push 5 push 6 push 7 add" -> [("push", "5 push 6 push 7 add")] *)
let stringp (str:string): string parser = 
  let len = String.length str in
  readn len >>= fun x ->
  if str = x then returnP x
  else failP

(* does what we recognize satisfy our accepted commands? *)
(* eg: check first char is digit? parse digit_p "12345" -> [('1',"2345")] *)
let sat f = 
  read >>= (fun x-> if f x then returnP x else failP)


let satcP (c:char)= 
  charP>>=fun x->
  if x=c then returnP c 
  else failP

let satsP s = 
  if s="" then failP else
    let rec asats (s:string)= 
      match (explode s) with 
        h::rest->satcP h >>=fun _->asats (implode rest)
      |
        []-> returnP([])
    in 
    asats (s:string)
(* satisfy a string  *)
(* let sats s = 
   if s="" then failP else
    let rec asats (s:string)= 
      match (explode s) with 
        h::rest->sat h >>=fun _->asats (implode rest)
      |
        []-> returnP([])
    in 
    asats (s:string) *)


let rec many0 p =
  (p >>= fun a -> 
   many0 p >>= fun b-> 
   returnP (a::b))
  <|>
  returnP []


let rec many1 p =
  p >>= fun a -> 
  many0 p >>= fun b-> 
  returnP (a::b)



(* All different parsers  *)
let is_alpha = function
  'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let is_digit = function
  '0' .. '9' -> true | _ -> false

let is_bool = function
    "true" | "false" -> true | _ -> false

let is_quote = function '\"' -> true | _ -> false

(* digit parser  *)
let digit_p = sat is_digit

(* letter parser  *)
let letter_p = sat is_alpha

(* char parser  *)
let char_p x = sat (fun y -> y=x)

(* quote parser *)
let quote_p = charP >>= fun q -> if (is_quote q) then failP else returnP q

(* bool parser  *)
let true_p = satcP '<' >>= fun _ -> satsP "true" >>= fun _ -> satcP '>' >>= fun _ -> returnP (true)
let false_p = satcP '<' >>= fun _ -> satsP "false" >>= fun _ -> satcP '>' >>= fun _ -> returnP (false)
let bool_p = true_p <|> false_p

(* whitespace parser*)
let whitespace_p = 
  char_p ' ' <|> char_p '\t' <|> char_p '\n'

(* youtube stringP  *)
let string (str:string): string parser =
  let len=String.length str in 
  readn len >>= fun x->
  if str=x then returnP x
  else failP

(* let string_p = 
   many0 (letter_p <|> digit_p  <|> char_p ' ') >>= fun x -> returnP (implode x) *)

let (let*) = (>>=)

let rec many (p: 'a parser): 'a list parser = 
  (let* a =p in
   let* ls = many p in
   returnP (a::ls))
  <|>
  returnP []

(* string parser  *)
let string_p =
  many0 whitespace_p >>= fun _ -> 
  satcP '\"' >>= fun a -> many quote_p >>= fun b -> satcP '\"' >>= fun c -> returnP ("\"" ^ implode b ^ "\"")

let empty_string_p = 
  satcP '\"' >>= fun b -> satcP '\"' >>= fun c -> returnP ("\"\"")


(* natural number parser  *)
let nat_p = 
  many1 digit_p >>= fun xs -> returnP (int_of_string (implode xs))

(* integer parser*)
let integer_p = 
  (char_p '-' >>= fun _-> 
   nat_p >>= fun n-> 
   returnP (-n)) <|> nat_p

(* name parser  *)
(* let name_p = 
   letter_p >>= fun a -> many1 (letter_p <|> digit_p <|> satcP '_' <|> satcP '\'') >>= fun b -> returnP (implode b) *)
let name_p =
  many1 (letter_p)  >>= fun x -> returnP (implode x)  

(* unit parser  *)
let unit_p = 
  string "<unit>"

(* error parser  *)
let error_p = 
  string "<error>"


(* let rec parse_commands (ls:string list): (command list) * (string list) = 
   match ls with
   | [] -> ([],[])
   | h::[] -> ((parse_command h), [])
   | h::t -> ((parse_command h), parse_commands t) *)


let const_p: stack_Val parser = 
  many0 whitespace_p >>= fun _ ->
  (integer_p >>= (fun a -> returnP(I a))) <|> 
  (name_p >>= (fun b -> returnP(N b))) <|> 
  (bool_p >>= (fun c -> returnP(B c))) <|> 
  (unit_p >>= (fun d -> returnP(Unit))) <|> 
  (empty_string_p >>= (fun e -> returnP(S e))) <|>
  (string_p >>= (fun f -> returnP(S f)))


(* -------------------------------------------------- *)
(* command parser  *)

(* parser for each command  *)
let parse_push =
  satsP "Push" >>= fun _-> 
  whitespace_p >>= fun _->
  const_p >>= fun i ->
  satsP ";" >>= fun _ ->
  returnP (Push i)
(* <|>
   (boolP >>= fun b ->
   returnP (PushB b)) *)

let parse_pop = 
  satsP "Pop" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Pop)

let parse_log = 
  satsP "Log" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Log)

let parse_swap = 
  satsP "Swap" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Swap)

let parse_add = 
  satsP "Add" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Add)

let parse_sub = 
  satsP "Sub" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Sub)

let parse_mul = 
  satsP "Mul" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Mul)

let parse_div = 
  satsP "Div" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Div)

let parse_rem = 
  satsP "Rem" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Rem)

let parse_neg = 
  satsP "Neg" >>= fun _-> 
  satsP ";" >>= fun _ ->
  returnP (Neg)


let flip f y x = f x y 
let ($) f g = fun x-> f (g x)

let parse s = 
  run_parse (parse_push <|> parse_add) s 

let parseStringOfCommandsIntoCommands (l:string list) = 
  List.map (flip List.nth 0 $ parse) l

let command_p =
  many whitespace_p >>= fun _-> (parse_push <|> parse_pop <|> parse_swap <|> parse_log <|> parse_add <|> parse_sub <|> parse_mul <|> parse_div <|> parse_neg <|> parse_rem) 

let commands_p = 
  many1 command_p >>= fun x -> returnP x



(* let prog = 
   many1 com

   let com =  *)






let rec eval (coms: command list) (stack: stack_Val list) (output: string list) (errorcode: int): (string list * int)= 
  match coms, stack with 
    Push x::rest, stack' -> eval rest (x::stack') output 0
  |
    Pop :: rest, [] -> (output, 2)
  |
    Pop::rest, x::stack' -> eval rest stack' output 0
  |
    Swap::_, [] -> (output, 2)
  |
    Swap::_, x::[] -> (output, 2)
  |
    Swap::rest, x::y::stack' -> (match x, y with
      | x, y -> eval rest (y::x::stack') output 0
    )
  |
    Add :: _, []-> (output, 2) 
  |
    Add :: _, x::[]-> (output, 2) 
  |
    Add :: rest, x::y::stack'-> (match x, y with 
        I x,I y->eval rest (I (x+y)::stack') output 0
      |
        _,_-> (output, 1))
  |
    Sub :: _, []-> (output, 2) 
  |
    Sub :: _, x::[]-> (output, 2) 
  |
    Sub :: rest, x::y::stack'-> (match x, y with 
        I x,I y->eval rest (I (x-y)::stack') output 0
      |
        _,_-> (output, 1))
  |
    Mul :: _, []-> (output, 2) 
  |
    Mul :: _, x::[]-> (output, 2) 
  |
    Mul :: rest, x::y::stack'-> (match x, y with 
        I x,I y->eval rest (I (x*y)::stack') output 0
      |
        _,_-> (output, 1))
  |
    Div :: _, []-> (output, 2) 
  |
    Div :: _, x::[]-> (output, 2) 
  |
    Div :: rest, x::y::stack'-> (match x, y with 
        I x,I y->if y=0 then (output, 3)  else eval rest (I (x/y)::stack') output 0
      |
        _,_-> (output, 1))
  |
    Rem :: _, []-> (output, 2) 
  |
    Rem :: _, x::[]-> (output, 2) 
  |
    Rem :: rest, x::y::stack'-> (match x, y with 
        I x,I y->if y=0 then (output, 3)  else eval rest (I (x mod y)::stack') output 0
      |
        _,_-> (output, 1))
  |
    Neg :: _, [] -> (output, 2)
  |
    Neg :: rest, x::stack'->(match x with
        I x -> eval rest (I (-x)::stack') output 0
      |
        _ -> (output, 1))
  | Log::rest, x::stack' -> (match x with
      | I x -> eval rest (stack') (output @[ string_of_int x]) 0
      | S x->eval rest (stack') (output @ [  x]) 0
      | N x->eval rest (stack') (output @ [  x]) 0
      | B x-> if x=true then eval rest (stack') (output @ [ "<true>"]) 0
        else eval rest (stack') (output @ [ "<false>"]) 0
      | Unit-> eval rest (stack') (output @ [ "<unit>"]) 0
      | Error -> eval rest (stack') (output @ [ "<error>"]) 0   
    )
  | Log::rest, [] -> (output, 2 )  

  |
    _,_-> (output, 0)
(* |
   _::rest ->  *)




(* let rec run (commands: command list) (stack: stackVal list) (env: env): (stackVal list * env) = 
   match (commands, stack) with 
   | (Add::rest, x::y::s') -> (match (res x, res y) with
      | (I i, I j)) *)




let interpreter (s : string) : string list * int = 
  match (run_parse commands_p s) with
  | (a,b)::rest -> eval a [] [] 0
  | _ -> ([],0)




let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ (loop ())
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

let runfile (file : string) : string list * int =
  let s = readlines file in
  interpreter s
type ae = CONST of int
	| VAR of string
	| POWER of string * int
	| TIMES of ae list
	| SUM of ae list

exception InvalidArgument

let rec diff : ae * string -> ae = fun (exp, s) -> 
  match exp with
  | CONST i -> CONST 0
  | VAR s1 -> if s1 = s then CONST 1 else CONST 0
  | POWER (s1, i) ->
    if s1 = s then
      if i = 1 then CONST 1
      else if i = 0 then CONST 0
      else if i = 2 then TIMES [CONST 2; VAR s1]
      else TIMES [CONST i; POWER (s1, i - 1)]
    else CONST 0
  | TIMES l ->
    (
	 match l with
     | hd::tl ->
       if tl = [] then diff (hd, s)
       else SUM [TIMES [diff (hd, s); TIMES tl]; TIMES [hd; diff (TIMES tl,s)]]
     | [] -> raise InvalidArgument
	)
  | SUM l ->
    (
	 match l with
     | hd::tl ->
       if tl = [] then diff (hd, s)
       else SUM ((diff (hd, s))::(diff (SUM tl, s))::[])
     | [] -> raise InvalidArgument
	)

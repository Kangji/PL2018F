type exp = X
	 | INT of int
	 | REAL of float
	 | ADD of exp * exp
	 | SUB of exp * exp
	 | MUL of exp * exp
	 | DIV of exp * exp
	 | SIGMA of exp * exp * exp
	 | INTEGRAL of exp * exp * exp

(* substitute variable X into assigned floating point number*)
let rec substitute : exp * float -> exp = fun (e, f) ->
  match e with
  | X -> REAL f
  | INT i -> INT i
  | REAL f1 -> REAL f1
  | ADD (e1, e2) -> ADD (substitute (e1, f), substitute (e2, f))
  | SUB (e1, e2) -> SUB (substitute (e1, f), substitute (e2, f))
  | MUL (e1, e2) -> MUL (substitute (e1, f), substitute (e2, f))
  | DIV (e1, e2) -> DIV (substitute (e1, f), substitute (e2, f))
  | SIGMA (e1, e2, e3) -> SIGMA (substitute (e1, f), substitute (e2, f), e3)
  | INTEGRAL (e1, e2, e3) -> INTEGRAL (substitute (e1, f), substitute (e2, f), e3)

exception FreeVariable

let rec calculate : exp -> float = fun e ->
  match e with
  | X -> raise FreeVariable
  | INT i -> float i
  | REAL f -> f
  | ADD (e1, e2) -> (calculate e1) +. (calculate e2)
  | SUB (e1, e2) -> (calculate e1) -. (calculate e2)
  | MUL (e1, e2) -> (calculate e1) *. (calculate e2)
  | DIV (e1, e2) -> (calculate e1) /. (calculate e2)
  | SIGMA (e1, e2, e3) ->
    let a = int_of_float (calculate e1) in
    let b = int_of_float (calculate e2) in
    if a > b then 0.
    else calculate (substitute (e3, float a)) +. calculate (SIGMA (ADD (INT a, INT 1), INT b, e3))
  | INTEGRAL (e1, e2, e3) ->
    let a = calculate e1 in
    let b = calculate e2 in
    if a > b then calculate (SUB (INT 0, INTEGRAL (e2, e1, e3)))
    else if b -. a < 0.1-.1e-6 then 0.
    else calculate (MUL (substitute (e3, a), REAL 0.1)) +. calculate (INTEGRAL (ADD (REAL a, REAL 0.1), REAL b, e3))

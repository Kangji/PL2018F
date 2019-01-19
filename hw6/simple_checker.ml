(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton Code
 *)

open M
open Pp

type var = string

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var

type tyEqn = 
  | Eqn of typ * typ
  | And of tyEqn * tyEqn

type sol = var -> typ
let empty_sol = fun x -> raise (M.TypeError "unbound variable")

let empty_env = fun x -> raise (M.TypeError "unbound variable")
let eq_operand = ref []
let write_operand = ref []

let rec eqn_make (env : M.id -> typ) exp : (var * tyEqn)= 
  let myVar = new_var () in
  match exp with
  | M.CONST (M.S s) -> (myVar, Eqn (TVar myVar, TString))
  | M.CONST (M.B b) -> (myVar, Eqn (TVar myVar, TBool))
  | M.CONST (M.N n) -> (myVar, Eqn (TVar myVar, TInt))
  | M.VAR x -> 
    (try (myVar, Eqn (TVar myVar, env x))
	with _ -> (myVar, Eqn (TVar myVar, TVar myVar)))
  | M.FN (x, e) -> 
    let a1 = new_var () in
    let env'= fun y -> if y = x then (TVar a1) else env y in
    let (a2, eqn') = eqn_make env' e in
	(myVar, And (Eqn (TVar myVar, TFun (TVar a1, TVar a2)), eqn'))
  | M.APP (e1, e2) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar a1, TFun (TVar a2, TVar myVar)), And (eqn1, eqn2)))
  | M.LET (M.VAL (x, e1), e2) -> (*t_x = t_e1 need?*)
    let (a1, eqn1) = eqn_make env e1 in
	let env' = fun y -> if y = x then (TVar a1) else env y in
	let (a2, eqn2) = eqn_make env' e2 in
	(myVar, And (Eqn (TVar myVar, TVar a2), And (eqn1, eqn2)))
  | M.LET (M.REC (f, x, e1), e2) ->
    let ax = new_var () in
	let af = new_var () in
    let env2 = fun y -> if y = f then (TVar af) else env y in
	let env1 = fun y -> if y = x then (TVar ax) else env2 y in
	let (a1, eqn1) = eqn_make env1 e1 in
	let (a2, eqn2) = eqn_make env2 e2 in
	(myVar, And (Eqn (TVar af, TFun (TVar ax, TVar a1)), And (Eqn (TVar myVar, TVar a2), And (eqn1, eqn2))))
  | M.IF (e1, e2, e3) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	let (a3, eqn3) = eqn_make env e3 in
	(myVar, And (Eqn (TVar a1, TBool), And (Eqn (TVar a2, TVar a3), And (Eqn (TVar myVar, TVar a3), And (eqn1, And (eqn2, eqn3))))))
  | M.BOP (M.ADD, e1, e2) ->
	let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar myVar, TInt), And (Eqn (TVar a1, TInt), And (Eqn (TVar a2, TInt), And (eqn1, eqn2)))))
  | M.BOP (M.SUB, e1, e2) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar myVar, TInt), And (Eqn (TVar a1, TInt), And (Eqn (TVar a2, TInt), And (eqn1, eqn2)))))
  | M.BOP (M.AND, e1, e2) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar myVar, TBool), And (Eqn (TVar a1, TBool), And (Eqn (TVar a2, TBool), And (eqn1, eqn2)))))
  | M.BOP (M.OR, e1, e2) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar myVar, TBool), And (Eqn (TVar a1, TBool), And (Eqn (TVar a2, TBool), And (eqn1, eqn2)))))
  | M.BOP (M.EQ, e1, e2) -> 
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	let _ = eq_operand := a1::a2::(!eq_operand) in
	(myVar, And (Eqn (TVar myVar, TBool), And (Eqn (TVar a1, TVar a2), And (eqn1, eqn2))))
  | M.READ -> (myVar, Eqn (TVar myVar, TInt))
  | M.WRITE e ->
    let (a, eqn') = eqn_make env e in
	let _ = write_operand := a :: (!write_operand) in
	(myVar, And (Eqn (TVar myVar, TVar a), eqn'))
  | M.MALLOC e ->
    let (a, eqn') = eqn_make env e in
	(myVar, And (Eqn (TVar myVar, TLoc (TVar a)), eqn'))
  | M.ASSIGN (e1, e2) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar a1, TLoc (TVar a2)), And (Eqn (TVar myVar, TVar a2), And (eqn1, eqn2))))
  | M.BANG e ->
    let (a, eqn') = eqn_make env e in
	(myVar, And (Eqn (TVar a, TLoc (TVar myVar)), eqn'))
  | M.SEQ (e1, e2) ->
	let (_, eqn1) = eqn_make env e1 in
	let (a, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar myVar, TVar a), And (eqn1, eqn2)))
  | M.PAIR (e1, e2) ->
    let (a1, eqn1) = eqn_make env e1 in
	let (a2, eqn2) = eqn_make env e2 in
	(myVar, And (Eqn (TVar myVar, TPair (TVar a1, TVar a2)), And (eqn1, eqn2)))
  | M.FST e ->
    let (a, eqn') = eqn_make env e in
	let tmp = new_var () in
	(myVar, And (eqn', Eqn (TVar a, TPair (TVar myVar, TVar tmp))))
  | M.SND e ->
    let (a, eqn') = eqn_make env e in
	let tmp = new_var () in
	(myVar, And (Eqn (TVar a, TPair (TVar tmp, TVar myVar)), eqn'))

let rec find x t : bool = 
  match t with
  | TPair (t1, t2) -> (find x t1) || (find x t2)
  | TLoc t -> find x t
  | TFun (t1, t2) -> (find x t1) || (find x t2)
  | TVar a -> x = a
  | _ -> false


let rec apply_sol s t : typ =
  match t with
  | TVar a -> (try s a with _ -> (TVar a))
  | TFun (t1, t2) -> TFun (apply_sol s t1, apply_sol s t2)
  | TLoc t -> TLoc (apply_sol s t)
  | TPair (t1, t2) -> TPair (apply_sol s t1, apply_sol s t2)
  | _ -> t
									
let rec apply_sol_tyEqn s u : tyEqn = 
  match u with
  | Eqn (t1, t2) -> Eqn (apply_sol s t1, apply_sol s t2)
  | And (u1, u2) -> And (apply_sol_tyEqn s u1, apply_sol_tyEqn s u2)

let rec unify : (typ * typ) -> sol = fun (t, t') ->
  match (t, t') with
  | (TInt, TInt) -> empty_sol
  | (TBool, TBool) -> empty_sol
  | (TString, TString) -> empty_sol
  | (TVar a, _) -> if find a t' then raise (M.TypeError "type mismatch") else fun x -> if x = a then t' else empty_sol x
  | (_, TVar a) -> if find a t then raise (M.TypeError "type mismatch") else fun x -> if x = a then t else empty_sol x
  | (TFun (t1, t2), TFun (t1', t2')) ->
    let s = unify (t1, t1') in
	let s' = unify (apply_sol s t2,apply_sol s t2') in
	fun x -> (try apply_sol s' (s x) with _ -> s' x)
  | (TPair (t1, t2), TPair (t1', t2')) ->
    let s = unify (t1, t1') in
	let s' = unify (t2, t2') in
	fun x -> (try apply_sol s' (s x) with _ -> s' x)
  | (TLoc t, TLoc t') -> unify (t, t')
  | _ -> raise (M.TypeError "type mismatch")

let rec unify_all : (tyEqn * sol) -> sol = fun (u, s) ->
  match u with
  | Eqn (t, t') -> fun x -> (try apply_sol (unify (t, t')) (s x) with _ -> (unify (t, t')) x)
  | And (u, u') -> let t = unify_all (u, s) in unify_all (apply_sol_tyEqn t u', t)
	

(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp ->
  let (a, eqn) = eqn_make empty_env exp in
  let solution = unify_all(eqn, empty_sol) in

  let rec eq_check eqlist = 
    match eqlist with
	| [] -> true
	| hd::tl -> 
	   (match solution hd with
	    | TFun (_,_) | TPair (_,_) -> false
	    | _ -> eq_check tl
	   )
  in

  let rec write_check writelist = 
    match writelist with
	| [] -> true
	| hd :: tl ->
	  (match solution hd with
	   | TFun (_,_) | TPair (_,_) | TLoc _ | TVar _ -> false
	   | _ -> write_check tl
	  )
  in

  if (eq_check (!eq_operand)) = false || (write_check (!write_operand)) = false then raise (M.TypeError "type mismatch") else 

  let rec translate t = 
    match t with
	| TInt -> M.TyInt
	| TBool -> M.TyBool
	| TString -> M.TyString
	| TVar x -> raise (M.TypeError "type inference failed")
	| TFun (t1, t2) -> M.TyArrow (translate t1, translate t2)
	| TPair (t1, t2) -> M.TyPair (translate t1, translate t2)
	| TLoc t' -> M.TyLoc (translate t')
  in

  translate (solution a)

(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

let count = ref 0

let new_var () =
  let _ = count := !count + 1 in
  "x_" ^ (string_of_int !count)

let rec alpha_conv exp subst = 
  match exp with
  | Num n -> Num n
  | Var x -> (try Var (List.assoc x subst) with Not_found -> Var x)
  | Fn (x, e) ->
    let x' = new_var () in
	let subst' = (x, x') :: subst in
	Fn (x', alpha_conv e subst')
  | App (e1, e2) -> App (alpha_conv e1 subst, alpha_conv e2 subst)
  | If (e1, e2, e3) -> If (alpha_conv e1 subst, alpha_conv e2 subst, alpha_conv e3 subst)
  | Equal (e1, e2) -> Equal (alpha_conv e1 subst, alpha_conv e2 subst)
  | Raise e -> Raise (alpha_conv e subst)
  | Handle (e1, n, e2) -> Handle (alpha_conv e1 subst, n, alpha_conv e2 subst)

let add k h exp = Fn (k, Fn (h, exp))

let rec cps' exp =
  let k = new_var () in (*normal continuation*)
  let h = new_var () in (*exception continuation*)
  match exp with
  | Num n -> add k h (App (Var k, Num n))
  | Var x -> add k h (App (Var k, Var x))
  | Fn (x, e) -> add k h (App (Var k, Fn (x, cps' e)))

  | App (e1, e2) ->
    let v1 = new_var () in
	let v2 = new_var () in
	let tmp = Fn (v1, App (App (cps' e2, Fn (v2, App (App (App (Var v1, Var v2), Var k), Var h))), Var h)) in
	add k h (App (App (cps' e1, tmp), Var h))
  | If (e1, e2, e3) -> 
    let v1 = new_var () in
	let v2 = new_var () in
	let v3 = new_var () in
	let tmp2 = Fn (v2, App (Var k, Var v2)) in
	let tmp3 = Fn (v3, App (Var k, Var v3)) in
	let tmp = Fn (v1, If (Var v1, App (App (cps' e2, tmp2), Var h), App (App (cps' e3, tmp3), Var h))) in
	add k h (App (App (cps' e1, tmp), Var h))
  | Equal (e1, e2) ->
    let v1 = new_var () in
	let v2 = new_var () in
	add k h (App (App (cps' e1, Fn (v1, App (App (cps' e2, Fn (v2, App (Var k, Equal (Var v1, Var v2)))), Var h))), Var h))
  
  | Raise e -> add k h (App (App (cps' e, Var h), Var h))
  | Handle (e1, n, e2) ->
    let x = new_var() in
	add k h (App (App (cps' e1, Var k), Fn (x, If (Equal (Var x, Num n), App (App (cps' e2, Var k), Var h), App (Var h, Var x)))))

let cps exp = cps' (alpha_conv exp [])

(* TODO : Implement this function *)
let removeExn : xexp -> xexp = fun e ->
  let x1 = new_var () in
  let x2 = new_var () in
  let k = Fn (x1, Var x1) in
  let h = Fn (x2, Num 201812) in
  App (App (cps e, k), h)

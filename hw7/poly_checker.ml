(*
 * SNU 4190.310 Programming Languages 2017 Fall
 * Type Checker Skeleton
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

let eq_operand = ref []
let write_operand = ref []
let generalized = ref []
let general_operand = ref []

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v -> [v]

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
	let _ = List.iter (fun beta -> general_operand := beta :: (!general_operand)) betas in
	let _ = List.iter2 (fun a' b' -> generalized := (a', b') :: (!generalized)) alphas betas in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec print_type : typ -> unit = fun t -> (*debugging*)
  match t with
  | TInt -> Printf.printf "%s" "int"
  | TBool -> Printf.printf "%s" "bool"
  | TString -> Printf.printf "%s" "string"
  | TPair (t1, t2) -> 
    let _ = Printf.printf "%s" "(" in
	let _ = print_type t1 in
	let _ = Printf.printf "%s" ", " in
	let _ = print_type t2 in
	Printf.printf "%s" ")"
  | TLoc t' ->
    let _ = Printf.printf "%s" "loc (" in
	let _ = print_type t' in
	Printf.printf "%s" ")"
  | TVar x -> Printf.printf "%s" x
  | TFun (t1, t2) ->
    let _ = Printf.printf "%s" "(" in
	let _ = print_type t1 in
	let _ = Printf.printf "%s" " -> " in
	let _ = print_type t2 in
	Printf.printf "%s" ")"

let rec find : var -> typ -> bool = fun x t ->
  match t with
  | TPair (t1, t2) -> (find x t1) || (find x t2)
  | TLoc t' -> find x t'
  | TFun (t1, t2) -> (find x t1) || (find x t2)
  | TVar a -> x = a
  | _ -> false

let rec unify : (typ * typ) -> subst = fun (t1, t2) ->
  match (t1, t2) with
  | (TInt, TInt) -> empty_subst
  | (TBool, TBool) -> empty_subst
  | (TString, TString) -> empty_subst
  | (TVar a, TVar b) ->
    if a = b then empty_subst
	else make_subst a (TVar b)
  | (TVar a, _) ->
    if find a t2 then raise (M.TypeError "type mismatch")
    else make_subst a t2
  | (_, TVar a) ->
    if find a t1 then raise (M.TypeError "type mismatch")
    else make_subst a t1
  | (TFun (t1, t2), TFun (t1', t2')) ->
    let s = unify (t1, t1') in
    let s' = unify (s t2, s t2') in
    s' @@ s
  | (TPair (t1, t2), TPair (t1', t2')) ->
    let s = unify (t1, t1') in
    let s' = unify (s t2, s t2') in
    s' @@ s
  | (TLoc t1, TLoc t2) -> unify (t1, t2)
  | _ -> raise (M.TypeError "type mismatch")

let rec expansive : M.exp -> bool = fun e ->
  match e with
  | M.CONST _ | M.VAR _ | M.FN _ | M.READ -> false
  | M.APP _ -> true
  | M.LET (M.VAL (_, e1), e2) -> (expansive e1) || (expansive e2)
  | M.LET (M.REC _, e2) -> expansive e2
  | M.IF (e1, e2, e3) -> (expansive e1) || (expansive e2) || (expansive e3)
  | M.BOP (_, e1, e2) -> (expansive e1) || (expansive e2)
  | M.WRITE e' -> (expansive e')
  | M.MALLOC _ -> true
  | M.ASSIGN (e1, e2) -> (expansive e1) || (expansive e2)
  | M.BANG e' -> expansive e'
  | M.SEQ (e1, e2) -> (expansive e1) || (expansive e2)
  | M.PAIR (e1, e2) -> (expansive e1) || (expansive e2)
  | M.FST e' -> expansive e'
  | M.SND e' -> expansive e'

let rec w : (typ_env * M.exp) -> (subst * typ) = fun (env, e) ->
  match e with
  | M.CONST (M.S s) -> (empty_subst, TString)
  | M.CONST (M.N n) -> (empty_subst, TInt)
  | M.CONST (M.B b) -> (empty_subst, TBool)
  | M.VAR x -> 
    (try
     (
      let typ_of_x = List.assoc x env in
      match typ_of_x with
      | SimpleTyp t -> (empty_subst, t)
      | GenTyp (alphas, t) ->
        let betas = List.map (fun _ -> new_var ()) alphas in
		let _ = List.iter2 (fun a' b' -> generalized := (a', b') :: (!generalized)) alphas betas in
        let s' =
          List.fold_left2
            (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst) empty_subst alphas betas in
        (empty_subst, s' t)
     ) with _ -> raise (M.TypeError ("unbound value"))
    )
  | M.FN (x, e') ->
    let beta = new_var () in
    let (s1, t1) = w ((x, SimpleTyp (TVar beta)) :: env, e') in
    (s1, TFun (s1 (TVar beta), t1))
  | M.APP (e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let (s2, t2) = w (subst_env s1 env, e2) in
    let beta = new_var () in
    let s3 = unify (s2 t1, TFun (t2, TVar beta)) in
    (s3 @@ (s2 @@ s1), s3 (TVar beta))
  | M.LET (M.VAL (x, e1), e2) ->
    if expansive e1 then
	let (s1, t1) = w (env, e1) in
	let (s2, t2) = w ((x, SimpleTyp t1)::(subst_env s1 env), e2) in
	(s2 @@ s1, t2)
	else
    let (s1, t1) = w (env, e1) in
    let env' = subst_env s1 env in
    let tyscm = generalize env' t1 in
	let _ = 
	  (
	   match tyscm with
	   | SimpleTyp _ -> ()
	   | GenTyp (alpha, _) ->
	     List.iter (fun a -> general_operand := a :: (!general_operand)) alpha
	  ) in
    let (s2, t2) = w ((x, tyscm) :: env', e2) in
    (s2 @@ s1, t2)
  | M.LET (M.REC (f, x, e1), e2) ->
    let alpha = new_var () in
	let beta = new_var () in
	let (s1, t1) = w ((f, SimpleTyp (TVar alpha)) :: (x, SimpleTyp (TVar beta)) :: env, e1) in
	let s2 = unify (s1 (TVar alpha), TFun (s1 (TVar beta), t1)) in
	let env' = subst_env (s2 @@ s1) env in
	let tyscm = generalize env' (s2 (s1 (TVar alpha))) in
	let _ = 
	  (
	   match tyscm with
	   | SimpleTyp _ -> ()
	   | GenTyp (alpha, _) ->
	     List.iter (fun a -> general_operand := a :: (!general_operand)) alpha
	  ) in
	let (s3, t2) = w((f, tyscm) :: env', e2) in
	(s3 @@ (s2 @@ s1), t2)
  | M.IF (e1, e2, e3) ->
    let (s1, t1) = w (env, e1) in
    let s2 = unify (t1, TBool) in
    let (s3, t2) = w (subst_env (s2 @@ s1) env, e2) in
    let (s4, t3) = w (subst_env (s3 @@ (s2 @@ s1)) env, e3) in
    let s5 = unify (s4 t2, t3) in
    (s5 @@ (s4 @@ (s3 @@ (s2 @@ s1))), s5 t3)
  | M.BOP (M.ADD, e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let s2 = unify (t1, TInt) in
    let (s3, t2) = w (subst_env (s2 @@ s1) env, e2) in
    let s4 = unify (t2, TInt) in
    (s4 @@ (s3 @@ (s2 @@ s1)), TInt)
  | M.BOP (M.SUB, e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let s2 = unify (t1, TInt) in
    let (s3, t2) = w (subst_env (s2 @@ s1) env, e2) in
    let s4 = unify (t2, TInt) in
    (s4 @@ (s3 @@ (s2 @@ s1)), TInt)
  | M.BOP (M.AND, e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let s2 = unify (t1, TBool) in
    let (s3, t2) = w (subst_env (s2 @@ s1) env, e2) in
    let s4 = unify (t2, TBool) in
    (s4 @@ (s3 @@ (s2 @@ s1)), TBool)
  | M.BOP (M.OR, e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let s2 = unify (t1, TBool) in
    let (s3, t2) = w (subst_env (s2 @@ s1) env, e2) in
    let s4 = unify (t2, TBool) in
    (s4 @@ (s3 @@ (s2 @@ s1)), TBool)
  | M.BOP (M.EQ, e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let (s2, t2) = w (subst_env s1 env, e2) in
    let s3 = unify (t1, t2) in
	let _ = 
	  (
	   match (s3 t1, s3 t2) with
	   | (TInt, TInt) | (TBool, TBool) | (TString, TString) | (TLoc _, TLoc _) -> ()
	   | (TVar x1, TVar x2) -> eq_operand := x1 :: x2 :: (!eq_operand)
	   | (_, _) -> raise (M.TypeError "type mismatch")
	  ) in
    (s3 @@ (s2 @@ s1), TBool)
  | M.READ -> (empty_subst, TInt)
  | M.WRITE e' ->
    let (s, t) = w (env, e') in
	let _ = 
	  (
	   match t with
	   | TInt | TBool | TString -> ()
	   | TVar x -> write_operand := x :: (!write_operand)
	   | _ -> raise (M.TypeError "type mismatch")
	  ) in
    (s, t)
  | M.MALLOC e' -> 
    let (s, t) = w (env, e') in
    (s, TLoc t)
  | M.ASSIGN (e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let (s2, t2) = w (env, e2) in
    let s3 = unify (s2 t1, TLoc t2) in
    (s3 @@ (s2 @@ s1), s3 t2)
  | M.BANG e' ->
    let (s, t) = w (env, e') in
    let beta = new_var () in
    let s2 = unify (TLoc (TVar beta), t) in
    (s2 @@ s, s2 (TVar beta))
  | M.SEQ (e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let (s2, t2) = w (subst_env s1 env, e2) in
    (s2 @@ s1, t2)
  | M.PAIR (e1, e2) ->
    let (s1, t1) = w (env, e1) in
    let (s2, t2) = w (subst_env s1 env, e2) in
    (s2 @@ s1, TPair (s2 t1, t2))
  | M.FST e' ->
    let (s, t) = w (env, e') in
	(
	 match t with
	 | TPair (t1, _) -> (s, t1)
	 | TVar x ->
	   let first = new_var () in
	   let second = new_var () in
	   let s2 = unify (TPair (TVar first, TVar second), t) in
	   (s2 @@ s, s2 (TVar first))
	 | _ -> raise (M.TypeError "type mismatch")
	)
  | M.SND e' ->
    let (s, t) = w (env, e') in
	(
	 match t with
	 | TPair (_, t2) -> (s, t2)
	 | TVar x ->
	   let first = new_var () in
	   let second = new_var () in
	   let s2 = unify (TPair (TVar first, TVar second), t) in
	   (s2 @@ s, s2 (TVar second))
	 | _ -> raise (M.TypeError "type mismatch")
	)

let rec translate t0 = 
  match t0 with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TFun (_, _) -> raise (M.TypeError "function type")
  | TVar x -> raise (M.TypeError "variable type")
  | TPair (t1, t2) -> M.TyPair (translate t1, translate t2)
  | TLoc t' -> M.TyLoc (translate t')

let rec check_eq subs x =
  match subs (TVar x) with
  | TInt | TBool | TString | TLoc _ -> ()
  | TVar x' ->
    if List.mem x' (!general_operand) then
	List.iter (check_eq subs) (snd (List.split (List.filter (fun (a, _) -> a = x') (!generalized))))
	else raise (M.TypeError "type mismatch")
  | _ -> raise (M.TypeError "type mismatch")

let rec check_write subs x =
  match subs (TVar x) with
  | TInt | TBool | TString -> ()
  | TVar x' ->
    if List.mem (x') (!general_operand) then
	List.iter (check_write subs) (snd (List.split (List.filter (fun (a, _) -> a = x') (!generalized))))
	else raise (M.TypeError "type mismatch")
  | _ -> raise (M.TypeError "type mismatch")

(* TODO : Implement this function *)
let check : M.exp -> M.typ = fun e ->

  let (s, t) = w ([], e) in

  let _ = List.iter (check_eq s) (!eq_operand) in
  let _ = List.iter (check_write s) (!write_operand) in
  translate t

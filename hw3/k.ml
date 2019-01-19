(*
 * SNU 4190.310 Programming Languages 2018 Fall
 *  K- Interpreter Skeleton Code
 *)

(*2017-18054 Kang Jiho*)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp

  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
    match v with
    | Unit -> ()
    | _ -> raise (Error "TypeError : not unit")

  let value_record v =
    match v with
    | Record r -> r
    | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr")) 
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let rec eval mem env e =
    match e with
    | READ x -> 
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
	| NUM n -> (Num n, mem)
	| TRUE -> (Bool true, mem)
	| FALSE -> (Bool false, mem)
	| UNIT -> (Unit, mem)
	| VAR x ->
	  let l = lookup_env_loc env x in
	  (Mem.load mem l,mem)
	| ADD (e1, e2) ->
	  let (v1, mem') = eval mem env e1 in
	  let (v2, mem'') = eval mem' env e2 in
	  (Num ((value_int v1)+(value_int v2)), mem'')
	| SUB (e1, e2) ->
	  let (v1, mem') = eval mem env e1 in
	  let (v2, mem'') = eval mem' env e2 in
	  (Num ((value_int v1)-(value_int v2)), mem'')
	| MUL (e1, e2) ->
	  let (v1, mem') = eval mem env e1 in
	  let (v2, mem'') = eval mem' env e2 in
	  (Num ((value_int v1)*(value_int v2)), mem'')
	| DIV (e1, e2) ->
	  let (v1, mem') = eval mem env e1 in
	  let (v2, mem'') = eval mem' env e2 in
	  let n2 = value_int v2 in
	  if n2 = 0 then raise (Error "Division by 0") else (Num ((value_int v1)/n2),mem'')
	| EQUAL (e1, e2) ->
	  let (v1,mem1) = eval mem env e1 in
	  let (v2,mem2) = eval mem1 env e2 in
	  (match (v1,v2) with
	   | (Num n1, Num n2) -> (Bool (n1 = n2), mem2)
	   | (Bool b1, Bool b2) -> (Bool (b1 = b2), mem2)
	   | (Unit, Unit) -> (Bool true, mem2)
	   | (_, _) -> (Bool false, mem2)
	  )
	| LESS (e1, e2) ->
	  let (v1, mem') = eval mem env e1 in
	  let (v2, mem'') = eval mem' env e2 in
	  let n1 = value_int v1 in
	  let n2 = value_int v2 in
	  (Bool (n1 < n2), mem'')
	| NOT e ->
	  let (v, mem') = eval mem env e in
	  let b = value_bool v in
	  if b then (Bool false, mem') else (Bool true, mem')
	| SEQ (e1, e2) ->
	  let (v1, mem') = eval mem env e1 in
	  eval mem' env e2
	| IF (e, e1, e2) ->
	  let (v, mem') = eval mem env e in
	  let b = value_bool v in
	  if b then (eval mem' env e1) else (eval mem' env e2)
	| WHILE (e1, e2) ->
	  let (v, mem') = eval mem env e1 in
	  let b = value_bool v in
	  if b then (
			  let (v1, mem1) = eval mem' env e2 in
			  eval mem1 env e)
	  else (Unit, mem')
	| LETF (f, par_list, e1, e) ->
	  let env' = Env.bind env f (Proc (par_list, e1, env)) in
	  eval mem env' e
	| CALLV (f, exp_list) ->
	  let (id_list, e', env') = lookup_env_proc env f in
	  let rec allocation t_id_list t_exp_list t_env' t_env t_mem = 
	    (match t_id_list with
		 | [] ->
		   (match t_exp_list with
			| [] -> (t_env', t_mem)
			| _ -> raise (Error "InvalidArg")
		   )
		 | id_hd::id_tl ->
		   (match t_exp_list with
			| [] -> raise (Error "InvalidArg")
			| exp_hd::exp_tl ->
			  let (t_v, t_mem') = eval t_mem t_env exp_hd in
			  let (t_l, t_mem'') = Mem.alloc t_mem' in
			  allocation id_tl exp_tl (Env.bind t_env' id_hd (Addr t_l)) t_env (Mem.store t_mem'' t_l t_v)
		   )
		) in
	  let (env'', mem') = allocation id_list exp_list env' env mem in
	  eval mem' (Env.bind env'' f (Proc (id_list, e', env'))) e'
	| CALLR (f, y) ->
	  let (x,e', env') = lookup_env_proc env f in
	  let rec add_then_eval t_x t_y t_env' = 
	    (match (t_x, t_y) with
		 | ([], []) -> eval mem (Env.bind t_env' f (Proc (x,e',env'))) e'
		 | ([], _) -> raise (Error "InvalidArg")
		 | (_, []) -> raise (Error "InvalidArg")
		 | ((x_hd::x_tl), (y_hd::y_tl)) -> add_then_eval x_tl y_tl (Env.bind t_env' x_hd (Addr (lookup_env_loc env y_hd)))
		) in
	  add_then_eval x y env'
	| RECORD r_list ->
	  let rec make_record t_mem t_r_list = 
	    (match t_r_list with
		 | [] -> (Record (fun x -> raise (Error "Unbound")),t_mem)
		 | (t_id, t_exp)::tl ->
		   let (v1, mem1) = eval t_mem env t_exp in
		   let (t_record, t_mem') = make_record mem1 tl in
		   let (t_l, t_mem'') = Mem.alloc t_mem' in
		   (Record (fun x -> if x = t_id then t_l else (value_record t_record) x),Mem.store t_mem'' t_l v1)
		) in
	  make_record mem r_list
	| FIELD (e, x) ->
	  let (v, mem') = eval mem env e in
	  let r = value_record v in
	  let l = r x in
	  (Mem.load mem' l,mem')
	| ASSIGNF (e1, x, e2) ->
	  let (v1, mem1) = eval mem env e1 in
	  let r = value_record v1 in
	  let (v, mem2) = eval mem1 env e2 in
	  (v, Mem.store mem2 (r x) v)

  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end

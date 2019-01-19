type treasure = StarBox | NameBox of string
type key = Bar | Node of key * key
type map = End of treasure
		 | Branch of map * map
		 | Guide of string * map

exception IMPOSSIBLE
exception NO_KEY

(*variable type of key*)
type varkey = Unknown of map
			| Known of key
			| Complicate of varkey * varkey

type record = {name: map; mutable lock: varkey}

(*caution : it is not optimized - it may easily cause stack overflow*)
(*it is easier to make program when you know type checking system*)

let rec updateRecord t_rec t_name t_lock = 
  match t_rec with
  | [] -> {name = t_name; lock = t_lock}::t_rec
  | hd::tl ->
    if hd.name = t_name then (hd.lock <- t_lock; t_rec) else hd::(updateRecord tl t_name t_lock)

let rec getLock t_rec t_name = 
  match t_rec with
  | hd::tl -> if hd.name = t_name then hd.lock else getLock tl t_name
  | [] -> raise NO_KEY

let rec findUnknown t_map t_varkey = 
  match t_varkey with
  | Unknown m -> if t_map = m then true else false
  | Known k -> false
  | Complicate (v1, v2) -> if (findUnknown t_map v1) || (findUnknown t_map v2) then true else false

let rec refresh t_rec k1 k2 = 
  if k1 = k2 then t_rec
  else
  (
   match (k1, k2) with
   | (Unknown m1, Unknown m2) ->
	 let key_m1 = getLock t_rec m1 in
	 updateRecord t_rec m2 key_m1
   | (Unknown m, Known k) -> updateRecord t_rec m (Known k)
   | (Unknown m, Complicate (_, _)) -> if findUnknown m k2 then raise IMPOSSIBLE else updateRecord t_rec m k2
   | (Known k, Unknown m) -> updateRecord t_rec m (Known k)
   | (Known k1, Known k2) -> if k1 = k2 then t_rec else raise IMPOSSIBLE
   | (Known k, Complicate (v1, v2)) ->
     (
	  match k with
	  | Bar -> raise IMPOSSIBLE
	  | Node (n1, n2) -> 
	    let t_rec' = refresh t_rec (Known n1) v1 in
		refresh t_rec' (Known n2) v2
	 )
   | (Complicate (_, _), Unknown m) -> if findUnknown m k1 then raise IMPOSSIBLE else updateRecord t_rec m k1
   | (Complicate (v1, v2), Known k) -> 
     (
	  match k with
	  | Bar -> raise IMPOSSIBLE
	  | Node (n1, n2) -> 
	    let t_rec' = refresh t_rec (Known n1) v1 in
		refresh t_rec' (Known n2) v2
	 )
   | (Complicate (v11, v12), Complicate (v21, v22)) ->
     let t_rec' = refresh t_rec v11 v21 in
	 refresh t_rec' v12 v22
  )

let rec getKey t_rec t_map = 
  match t_map with
  | End StarBox -> (t_rec, Known Bar)
  | End (NameBox x) -> 
    (
  	 try
	 (
	  let key_x = getLock t_rec t_map in
	  (t_rec, key_x)
	 ) with NO_KEY -> (updateRecord t_rec t_map (Unknown t_map),Unknown t_map)
	)
  | Guide (x, e) ->
    (
	 let (t_rec', key_e) = getKey t_rec e in
	 let key_x = getLock t_rec' (End (NameBox x)) in
	 match (key_x,key_e) with
	 | (Known k1, Known k2) -> (t_rec', Known (Node (k1,k2)))
	 | (_, _) -> (t_rec', Complicate (key_x, key_e))
	)
  | Branch (e1, e2) ->
    (
	 let (t_rec', key_e2) = getKey t_rec e2 in
	 let (t_rec'', key_e1) = getKey t_rec' e1 in
	 let t_rec1 = updateRecord t_rec'' t_map (Unknown t_map) in
	 let t_rec2 = refresh t_rec1 key_e1 (Complicate (key_e2, (Unknown t_map))) in
	 (t_rec2, getLock t_rec2 t_map)
	)

let rec make_key t_rec t_varkey = 
  match t_varkey with
  | Unknown m ->
    (
	 let m_key = getLock t_rec m in
	 match m_key with
	 | Unknown m' -> if m = m' then (let t_rec' = updateRecord t_rec m (Known Bar) in (t_rec',Bar)) else (let (t_rec', t_key) = make_key t_rec m_key in let t_rec'' = updateRecord t_rec' m (Known t_key) in (t_rec'', t_key))
	 | Known k -> (t_rec, k)
	 | Complicate (v1, v2) -> (let (t_rec', t_key) = make_key t_rec m_key in let t_rec'' = updateRecord t_rec' m (Known t_key) in (t_rec'', t_key))
	)
  | Known k -> (t_rec, k)
  | Complicate (v1, v2) -> 
    let (t_rec', key_v1) = make_key t_rec v1 in
	let (t_rec'', key_v2) = make_key t_rec' v2 in
	(t_rec'', Node (key_v1, key_v2))

let rec updateKeylist t_keylist t_key = 
  match t_keylist with
  | [] -> t_key::t_keylist
  | hd::tl -> if hd = t_key then t_keylist else hd::(updateKeylist tl t_key)

let rec makeKeylist t_rec t_keylist t_rec_origin= 
  match t_rec with
  | [] -> t_keylist
  | hd::tl ->
    (
	 match hd.name with
	 | End (NameBox x) -> 
	   let (t_rec_origin', t_key) = make_key t_rec_origin hd.lock in
	   let t_keylist' = updateKeylist t_keylist t_key in
	   makeKeylist tl t_keylist' t_rec_origin'
	 | _ -> makeKeylist tl t_keylist t_rec_origin
	)

let rec findStarBox t_map = 
  match t_map with
  | End StarBox -> true
  | End (NameBox x) -> false
  | Guide (s, e) -> findStarBox e
  | Branch (e1, e2) -> (findStarBox e1) || (findStarBox e2)

let getReady t_map = 
  let (t_rec, _) = getKey [] t_map in
  if findStarBox t_map then makeKeylist t_rec [Bar] t_rec else makeKeylist t_rec [] t_rec


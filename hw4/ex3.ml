type require = id * (cond list)
and cond = Items of gift list
		 | Same of id
		 | Common of cond * cond
		 | Except of cond * gift list
and gift = int
and id = A | B | C | D | E

let rec search x l = 
  match l with
  | [] -> false
  | hd::tl -> if hd = x then true else search x tl

let rec intersection a b = 
  match b with
  | [] -> []
  | hd::tl -> if (search hd a) then hd::(intersection a tl) else (intersection a tl)

let rec union a b = 
  match b with
  | [] -> a
  | hd::tl -> if (search hd a) then (union a tl) else hd::(union a tl)

let rec minus a b =
  match a with
  | [] -> []
  | hd::tl -> if (search hd b) then (minus tl b) else hd::(minus tl b)

let rec remove_duplicate l = 
  match l with
  | [] -> []
  | hd::tl -> if (search hd tl) then remove_duplicate tl else hd::(remove_duplicate tl)

let rec sort l = 
  let rec insertion a l' = 
    match l' with
	| [] -> [a]
	| hd::tl -> if a < hd then a::l' else hd::(insertion a tl)
  in
  match l with
  | [] -> []
  | hd::tl -> insertion hd (sort tl)

let rec getlist cond a b c d e = 
  match cond with
  | Items l -> remove_duplicate l
  | Same x -> (match x with | A -> a | B -> b | C -> c | D -> d | E -> e)
  | Common (c1, c2) -> intersection (getlist c1 a b c d e) (getlist c2 a b c d e)
  | Except (c', l) -> minus (getlist c' a b c d e) l

let update_id x cond a b c d e = 
  let l = getlist cond a b c d e in
  match x with
  | A ->
    (
	 let res_list = union a l in
	 let again = if res_list = a then false else true in
	 (res_list, b, c, d, e, again)
	)
  | B -> 
    (
	 let res_list = union b l in
	 let again = if res_list = b then false else true in
	 (a, res_list, c, d, e, again)
	)
  | C -> 
    (
	 let res_list = union c l in
	 let again = if res_list = c then false else true in
	 (a, b, res_list, d, e, again)
	)
  | D ->
    (
	 let res_list = union d l in
	 let again = if res_list = d then false else true in
	 (a, b, c, res_list, e, again)
	)
  | E -> 
    (
	 let res_list = union e l in
	 let again = if res_list = e then false else true in
	 (a, b, c, d, res_list, again)
	)

let rec update_req req a b c d e again = 
  match req with
  | (x,[]) -> (a, b, c, d, e, again)
  | (x,hd::tl) -> 
    let (a', b', c', d', e', again') = update_id x hd a b c d e in
	let again'' = again' || again in
	update_req (x,tl) a' b' c' d' e' again''

let rec update_list req_list a b c d e again = 
  match req_list with
  | [] -> (a, b, c, d, e, again)
  | hd::tl -> let (a', b', c', d', e', again') = update_req hd a b c d e again in update_list tl a' b' c' d' e' again'

let rec update req_list a b c d e = 
  let (a', b', c', d', e', again') = update_list req_list a b c d e false in
  if again' then update req_list a' b' c' d' e' else [(A, sort a'); (B, sort b'); (C, sort c'); (D, sort d'); (E, sort e')]

let shoppingList req_list = update req_list [] [] [] [] []

type heap = EMPTY | NODE of rank * value * heap * heap
and rank = int
and value = int

exception EmptyHeap

let rank h = match h with 
  | EMPTY -> -1
  | NODE (r, _, _, _) -> r
let findMin h = match h with
  | EMPTY -> raise EmptyHeap
  | NODE (_, x, _, _) -> x
let getLeft h = match h with
  | EMPTY -> raise EmptyHeap
  | NODE (_, _, lh, _) -> lh
let getRight h = match h with 
  | EMPTY -> raise EmptyHeap
  | NODE (_, _, _, rh) -> rh

let shake (x, lh, rh) = if (rank lh) >= (rank rh) then NODE (rank rh+1, x, lh, rh) else NODE (rank lh + 1, x, rh, lh)

let rec merge (lh, rh) = 
  if rank lh = -1 then rh
  else if rank rh = -1 then lh
  else if findMin lh < findMin rh then shake (findMin lh, getLeft lh, merge (getRight lh, rh))
  else shake (findMin rh, getLeft rh, merge (getRight rh, lh))

let insert (x, h) = merge (h, NODE (0, x, EMPTY, EMPTY))

let deleteMin h = match h with
  | EMPTY -> raise EmptyHeap
  | NODE (_, x, lh, rh) -> merge(lh, rh)


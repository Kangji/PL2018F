module type Queue= 
  sig
    type element
    type queue
    exception EMPTY_Q
    val emptyQ: queue
    val enQ: queue * element -> queue
    val deQ: queue -> element * queue
  end

module IntListQ = 
  struct
    type element = int list
    type queue = (element list) * (element list)
    exception EMPTY_Q
    let emptyQ : queue = ([], [])
    let enQ : queue * element -> queue = fun (q, e)->
      match q with | (l, r) -> ((e::l), r)
    let deQ = fun q ->
      match q with
      | (l, []) -> 
        (
		 let ll = List.rev l in
         match ll with
         | [] -> raise EMPTY_Q
         | hd::tl -> (hd, ([], tl))
        )
      | (l, hd::tl) -> (hd, (l, tl))
  end


let rec sumprod: (int*int->float) * int * int -> float = fun (m,n,k) ->
  let rec prod: (int*int->float) * int * int -> float = fun (mm,nn,kk) ->
    if kk < 1 then 1.
    else (mm (nn,kk)) *. (prod (mm,nn,kk-1))
  in
  if n < 1 then 0.
  else (prod (m,n,k)) +. (sumprod (m,n-1,k))
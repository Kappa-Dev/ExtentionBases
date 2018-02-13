type 'a t = {q: 'a Queue.t ; mutable l : 'a list}
exception Empty

let create () =
  let q = Queue.create () in
  {q = q ; l = []}

let add_lifo e ql = ql.l <- e::ql.l
let add_fifo e ql = Queue.add e ql.q

let pop ql =
  try
    match ql.l with
      e::tl -> ql.l <- tl ; e
    | [] -> Queue.pop ql.q
  with
    Queue.Empty -> raise Empty

let fold f ql cont =
  let cont =
    List.fold_left
      (fun cont e ->
        f e cont
      ) cont ql.l
  in
  Queue.fold
    (fun cont e -> f e cont
    ) cont ql.q

let elements ql =
  List.rev (fold (fun e l -> e::l) ql [])

let is_empty ql =
  Queue.is_empty ql.q && ql.l = []

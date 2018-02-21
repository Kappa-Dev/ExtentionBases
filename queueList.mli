type 'a t
exception Empty

(**Creates an empty queueList*)
val create : unit -> 'a t

(**[add_lifo e ql] adds [e] to the queueList [ql] with a last-in-first-out policy*)
val add_hp : 'a -> 'a t -> 'a t

(**[add_fifo e ql] adds [e] to the queueList [ql] with a first-in-first-out policy*)
val add_lp : 'a -> 'a t -> 'a t

(**Pops an element from the queueList according to its insertion policy*)
val pop : 'a t -> 'a

(**[fold f ql cont] iterator on queueList [ql]*)
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

(**To turn the queueList into a simple list*)
val elements : 'a t -> 'a list

(**Test for emptyness*)
val is_empty : 'a t -> bool

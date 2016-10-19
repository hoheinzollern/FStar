module Problem


open FStar.Heap

val sender_cnt: ref int
let sender_cnt = ST.alloc 0

val another_cnt: ref int
let another_cnt = ST.alloc 0

(* logic type senderInvariant h  = ((sel h sender_cnt) = 0) *)

(* some basic, untrusted network controlled by the adversary *)

logic type invariant h = (contains h sender_cnt) /\ (contains h another_cnt) /\ (sel h sender_cnt = 0) /\ (sender_cnt <> another_cnt)

assume val send: int -> ST unit
  (requires (fun h -> invariant h))
  (ensures (fun h x h' -> invariant h' /\ modifies (!{another_cnt}) h h'))

val sender: unit -> ST (option string) 
                      (requires (fun h -> invariant h))
		      (ensures (fun h x h' -> invariant h' /\ modifies (!{another_cnt}) h h'))
let sender () = 
  (* let x = !sender_cnt in assert(x = 0); *)
  (* send 0; *)
  (* let x = !sender_cnt in assert(x = 0); *)
  another_cnt := !another_cnt + 1;
  (* let x = !sender_cnt in assert(x = 0); *)
  None


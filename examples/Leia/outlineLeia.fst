(*--build-config
    options:--z3timeout 10 --verify_module CntProtocol --admit_fsi FStar.Seq --admit_fsi FStar.IO;
    variables:CONTRIB=/home/exr/projects/FStar/contrib;
    other-files:
            ext.fst classical.fst
            set.fsi set.fst
            heap.fst st.fst all.fst
            string.fst list.fst
            seq.fsi seqproperties.fst
            io.fsti
            $CONTRIB/Platform/fst/Bytes.fst
            $CONTRIB/CoreCrypto/fst/CoreCrypto.fst
            cnt-format.fst
            sha1.fst
            mac.fst
  --*)
  
module OutlineLeia


open FStar.All
open FStar.Set
open FStar.String
open FStar.IO
open FStar.Heap


let init_print = print_string "\ninitializing...\n\n"

open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes
open SHA1
open MAC

type message = bytes
type msg (l:nat) = m:message{length m==l}

type uint = i:int{0 <= i}
type pint = i:int{1 <= i}

type uint16 = i:nat{repr_bytes i <= 2}
type uint32 = i:nat{repr_bytes i <= 4}

val uint16_to_bytes: uint16 -> Tot (b:bytes{length b = 2})
let uint16_to_bytes = bytes_of_int 2

let uint32_to_bytes = bytes_of_int 4
let bytes_to_uint16 (x:msg 2) = int_of_bytes x
let bytes_to_uint32 (x:msg 4) = int_of_bytes x

let uint16_length = 2


type event =
  | Recv : c:uint16 -> d:bytes -> event

val sender_log_prot: ref (list event)
let sender_log_prot = ST.alloc []

val recv_cnt: ref uint16
let recv_cnt = lemma_repr_bytes_values (* 1*) 0; ST.alloc (* 1 *) 0

val sender_cnt: ref uint16
let sender_cnt = lemma_repr_bytes_values 0; ST.alloc 0


assume val data: bytes

val construct_tag: (c:nat{repr_bytes c <= 2}) -> (data:bytes) -> Tot (msg (2 + (length data)))
let construct_tag c data =  ((uint16_to_bytes c) @| data)

  opaque logic type req (msg:message) =  
  (exists n.  (repr_bytes n <= 2) /\ (msg  = construct_tag n data)) 
  
val max_event: list event -> Tot uint16
let rec max_event l = 
  match l with
    [] -> lemma_repr_bytes_values 0; 0
    | (Recv c _)::es ->
      let prev = max_event es in
      if c > prev then c else prev
      

 logic type SenderInvariant h  = contains h sender_cnt /\ contains h recv_cnt /\ contains h sender_log_prot /\ (max_event (sel h sender_log_prot)) <= (sel h sender_cnt) /\ repr_bytes (sel h sender_cnt) <= 2 /\ sender_cnt <> recv_cnt 

val sender_log: d: bytes -> ST(unit)
  (requires (fun h -> SenderInvariant h))
  (ensures (fun h x h' -> SenderInvariant h' /\ 
		       (sel h' sender_log_prot = (Recv (sel h sender_cnt) d ) :: (sel h sender_log_prot))
 		       /\ modifies (!{sender_log_prot}) h h')) 
		       
		       

let sender_log d =
  sender_log_prot := (Recv !sender_cnt d):: !sender_log_prot


let k = keygen req

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
     Seq.Eq (utf8 s0) (utf8 s1) ==> s0==s1

val inc_sender_counter: unit -> ST(unit)
    (requires (fun h -> SenderInvariant h /\  repr_bytes ((sel h sender_cnt) + 1) <= 2))
    (ensures (fun h x h' -> SenderInvariant h'  /\ 
                         (sel h sender_cnt) < (sel h' sender_cnt) /\
                         modifies (!{sender_cnt}) h h'))

let inc_sender_counter () =
      sender_cnt := !sender_cnt + 1


type string16 = s:string{repr_bytes (length (utf8 s)) <= 2} (* up to 65K *)




(* some basic, untrusted network controlled by the adversary *)

assume val send: message -> ST unit
		       (requires (fun h -> SenderInvariant h))
		       (ensures (fun h x h' -> SenderInvariant h' /\ modifies (!{}) h h'))

assume val recv: unit -> ST message
		    (requires (fun h -> True))
 		    (ensures (fun h x h' -> modifies (!{}) h h')) 
		    
		

val sender: unit -> ST (option string) 
                     (requires (fun h -> SenderInvariant h /\ repr_bytes ((sel h sender_cnt) + 1) = 2))
                      (ensures (fun h x h' -> SenderInvariant h' /\ modifies (!{sender_log_prot, sender_cnt, log}) h h'))                 


let sender () = 
 	inc_sender_counter (); 
        let sc = !sender_cnt in
        let t = construct_tag sc  data in
        let bs = uint16_to_bytes sc in 
	let smac = mac k t in  
  	send (bs @| data);  
        send (bs @| smac);   
        sender_log data;  
      None
      
val receiver:  unit -> ST (option string) 
                     (requires (fun h -> True))
                     (ensures (fun h x h' -> modifies (!{log, recv_cnt}) h h'))                 

let receiver () = 
    let msg = recv() in
    if length msg <> uint16_length + (length data) then Some "Wrong length"
    else
    let (xcnt, xdata) = split msg uint16_length in
    let msg2 = recv() in 
    if length msg2 < uint16_length then Some "Wrong length of second message"
    else
    let (xcnt1, xmac) = split msg2 uint16_length in 
    if xcnt <>  xcnt1 then Some "Wrong counter received"
    else 	    
    let xc = bytes_to_uint16 xcnt in
    if  xc <  !recv_cnt then Some "sender counter smaller than receiver counter"
    else 
      begin
      recv_cnt := xc;
      if not (verify k xmac (xcnt @| xdata)) then Some "MAC verification failed"
      else None
    end


(*--build-config
    options:--z3timeout 10 --verify_module StProtocol --admit_fsi FStar.Seq --admit_fsi FStar.IO;
    variables:CONTRIB=../../contrib;
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
	    counter.fst
            sha1.fst
            mac.fst
  --*)


(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)

module StProtocol

#set-options "--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1"

open FStar.All
open FStar.Set
open FStar.String
open FStar.IO
open FStar.Heap
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes
open SHA1
open CntFormat
open MAC
open Counter

(* some basic, untrusted network controlled by the adversary *)

val msg_buffer: ref message
let msg_buffer = ST.alloc (empty_bytes)

val send: message -> ST unit
		       (requires (fun h -> True))
		       (ensures (fun h x h' -> modifies !{msg_buffer} h h'))
let send m = msg_buffer := m

val recv: unit -> ST message
		    (requires (fun h -> True))
		    (ensures (fun h x h' -> modifies !{msg_buffer} h h'))
let rec recv _ = if length !msg_buffer > 0
                then (
                  let msg = !msg_buffer in
                  msg_buffer := empty_bytes;
                  msg)
                else recv ()

(* the meaning of MACs, as used in RPC *)

logic type Signal : uint32 -> uint16 -> Type
opaque logic type req (msg:message) =
    (exists s c.   msg = CntFormat.signal s c /\ Signal s c)

let k = keygen req

val proc_a : uint32 -> All unit
 			  (requires (fun h -> Invariant h /\
				     repr_bytes ((sel h proc_a_st) + 1) <= 2 ))
 			  (ensures (fun h x h' -> Invariant h'))
let proc_a (s: uint32) =
  let c = fresh_challenge () in
  admitP (Signal s c);
  let t = CntFormat.signal s c in
  let m = mac k t in
  send (t @| m)

val proc_b : unit -> All unit
			(requires (fun h -> Invariant h))
			(ensures (fun h x h' -> Invariant h'
			  /\ modifies (!{log_p, proc_b_st, msg_buffer}) h h'))
let proc_b () =
  let msg = recv () in (
    if length msg = signal_size + macsize then (
      let (t, m) = split msg signal_size  in
      let (s, c) = CntFormat.signal_split t in
        if is_fresh_challenge c then(
          if verify k t m then (
	    assert(Signal s c);
	    recv_lemma s c (!log_p);
	    log_and_update s c;
	    None
	  ) else Some "MAC failed"
	) else Some "Counter already used"
    ) else Some "Wrong length")

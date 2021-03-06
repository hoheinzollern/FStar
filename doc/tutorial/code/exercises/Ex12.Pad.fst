module Ex12.Pad

open FStar.UInt8
open FStar.Seq
open FStar.SeqProperties


type uint8 = FStar.UInt8.t

let n2b = uint_to_t
let b2n = v

type bytes = seq byte (* concrete byte arrays *)


type nbytes (n:nat) = b:bytes{length b == n} (* fixed-length bytes *)

let blocksize = 32 
type block = nbytes blocksize
type text = b:bytes {(length b < blocksize)}

val pad: n:nat { 1 <= n /\ n <= blocksize } -> Tot (nbytes n)

// BEGIN: CreatePadding
let pad n = 
  Seq.create n (n2b (n-1))  
// END: CreatePadding

(* pad 1 = [| 0 |]; pad 2 = [| 1; 1 |]; ... *)

val encode: a: text -> Tot block 
// BEGIN: EncodePadding
let encode a = append a (pad (blocksize - length a))
// END: EncodePadding

val inj: a: text -> b: text -> Lemma (requires (equal (encode a) (encode b)))
                                     (ensures (equal a b))
                                     [SMTPat (encode a); SMTPat (encode b)]


let inj a b = 
  if length a = length b
  then lemma_append_inj a (pad (blocksize - length a)) b  (pad (blocksize - length a))
  else let aa = encode a in
       let bb = encode b in
       cut (index aa 31 <> index bb 31)


val decode: b:block -> option (t:text { equal b (encode t) })
// BEGIN: DecodePadding
let decode (b:block) = 
  let padsize = b2n(index b (blocksize - 1)) + 1 in
  if padsize <= blocksize then 
    let (plain,padding) = split b (blocksize - padsize) in
    if  Seq.eq padding (pad padsize)
    then Some plain
    else None   
  else None
// END: DecodePadding

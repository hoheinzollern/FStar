module Counter

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

let max x y = if x > y then x else y

(* Events for proving injective agreement *)
type event =
  | Recv : m:uint32 -> c:uint16 -> event

val log_p: ref (list event)
let log_p = ST.alloc []

val proc_a_st: ref uint16
let proc_a_st = lemma_repr_bytes_values 1; ST.alloc 1

val proc_b_st: ref uint16
let proc_b_st = lemma_repr_bytes_values 0; ST.alloc 0

val proc_b_max: l:list event -> Tot (c:uint16)
let rec proc_b_max l =
  match l with
  | [] -> lemma_repr_bytes_values 0; 0
  | Recv _ c :: l' -> max c (proc_b_max l')

val max_c: s:uint32 -> c:uint16 -> l:list event ->
  Lemma(if c > proc_b_max l then
	  proc_b_max (Recv s c :: l) > proc_b_max l
	else proc_b_max (Recv s c :: l) = proc_b_max l)
let max_c s c l = ()

val recv_lemma: s:uint32 -> c:uint16 -> (l:list event{c > proc_b_max l}) ->
  Lemma(forall e . List.mem e l ==> e <> (Recv s c))
let rec recv_lemma s c l =
  match l with
  | [] -> ()
  | Recv s' c' :: l' ->
     max_c s' c' l';
     recv_lemma s c l'

logic type Invariant h =
  proc_b_max (Heap.sel h log_p) = Heap.sel h proc_b_st &&
    Heap.contains h proc_b_st && Heap.contains h proc_a_st &&
      Heap.contains h log_p && proc_b_st <> proc_a_st

logic type PreLogUpd s c h =
  c > sel h proc_b_st

logic type PostLogUpd s c h =
  c = sel h proc_b_st

let is_fresh_challenge x =
  let y = !proc_b_st in
  (y < x)

let fresh_challenge () =
  let c  = !proc_a_st in
  proc_a_st := c+1;
  lemma_repr_bytes_values c; c

let update_challenge x =
  let y = !proc_b_st in
  proc_b_st := max x y

val log_and_update: s: uint32 -> c: uint16 -> ST (unit)
    (requires (fun h -> Invariant h /\ PreLogUpd s c h /\
		     (forall e . List.mem e (sel h log_p) ==> e <> (Recv s c))))
    (ensures (fun h x h' -> Invariant h' /\ PostLogUpd s c h' /\
                         (sel h' log_p = Recv s c :: sel h log_p) /\
			 (modifies (!{log_p, proc_b_st}) h h')))
let log_and_update s c =
  log_p := Recv s c :: !log_p;
  update_challenge c

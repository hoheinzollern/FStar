(*--build-config
variables:LIB=../../lib;
variables:MATHS=../maths;
other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst located.fst
  --*)


module Lref
open Located
open Ghost

type lref (a:Type) : Type = located (ref a)

type heapAux
type heap = erased heapAux


open Set

type aref =
  | Ref : #a:Type -> r:lref a -> aref
assume logic val sel :       #a:Type -> heap -> lref a -> Tot (*erased*) a
assume logic val upd :       #a:Type -> heap -> lref a -> a -> Tot heap
assume logic val emp :       heap
assume logic val contains :  #a:Type -> heap -> lref a -> Tot (*erased*) bool
assume logic val equal:      heap -> heap -> Tot (*erased*) bool
assume logic val restrict:   heap -> set aref -> Tot heap
assume logic val concat:     heap -> heap -> Tot heap

assume SelUpd1:       forall (a:Type) (h:heap) (r:lref a) (v:a).            {:pattern (sel (upd h r v) r)}
                      sel (upd h r v) r == v

assume SelUpd2:       forall (a:Type) (b:Type) (h:heap) (k1:lref a) (k2:lref b) (v:b).{:pattern (sel (upd h k2 v) k1)}
                      k2=!=k1 ==> sel (upd h k2 v) k1 == sel h k1

assume ContainsUpd:   forall (a:Type) (b:Type) (h:heap) (k1:lref a) (k2:lref b) (v:a).{:pattern contains (upd h k1 v) k2}
                      contains (upd h k1 v) k2 <==> (k1==k2 \/ contains h k2)

assume InDomEmp:      forall (a:Type) (k:lref a).                           {:pattern contains emp k}
                      not(contains emp k)

assume Extensional:   forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> h1 == h2

assume Equals:        forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> (forall (a:Type) (k:lref a).{:pattern (sel h1 k); (sel h2 k)} sel h1 k == sel h2 k)

assume RestrictSel:   forall (a:Type) (h:heap) (r:set aref) (a:lref a).     {:pattern sel (restrict h r) a}
                      mem (Ref a) r ==> sel (restrict h r) a == sel h a

assume RestrictIn:    forall (a:Type) (h:heap) (r:set aref) (a:lref a).     {:pattern contains (restrict h r) a}
                      contains (restrict h r) a == (mem (Ref a) r && contains h a)

assume SelConcat:     forall (a:Type) (h1:heap) (h2:heap) (a:lref a).       {:pattern sel (concat h1 h2) a}
                      if b2t (contains h2 a) then sel (concat h1 h2) a==sel h2 a else sel (concat h1 h2) a == sel h1 a

assume ContainsConcat:forall (a:Type) (h1:heap) (h2:heap) (a:lref a).       {:pattern contains (concat h1 h2) a}
                      contains (concat h1 h2) a == (contains h1 a || contains h2 a)

type On (r:set aref) (p:(heap -> Type)) (h:heap) = p (restrict h r)
(*opaque type fresh (h:heap) (lrefs:set aref)       = (forall (a:Type) (a:lref a).{:pattern (contains h a)} mem (Ref a) lrefs ==> not(contains h a))*)
opaque type fresh (lrefs:set aref) (h0:heap) (h1:heap) =
  (forall (a:Type) (a:lref a).{:pattern (contains h0 a)} mem (Ref a) lrefs ==> not(contains h0 a) /\ contains h1 a)
opaque logic type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (equal h' (concat h' (restrict h (complement mods))))

let only x = Set.singleton (Ref x)
module FStar.Tcp
open FStar.Bytes

assume new type stream
assume new type listener


(* Server side *)

assume val listen: host:string -> port:int -> listener
assume val accept: l:listener -> stream
assume val stop: l:listener -> unit

(* Client side *)

assume val connect: host:string -> port:int -> stream

(* Input/Output *)

assume val read: s:stream -> n:int -> option bytes
assume val write: s:stream -> b:bytes -> option unit
assume val close: s:stream -> unit

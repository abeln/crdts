(* Original CCDDB code by Leon Gondelman *)

open Unix

(** Aneris.network_helpers translation *)
let udp_socket () = socket PF_INET SOCK_DGRAM 0

let makeAddress ip port = ADDR_INET (ip, port)

let socketBind socket addr = bind socket addr

let receiveFrom skt =
  let buffer = Bytes.create 1024 in
  match recvfrom skt buffer 0 1024 [] with
  | len, (ADDR_INET (addr, port) as sockaddr) ->
    let msg = Bytes.sub_string buffer 0 len in
    Some (msg, sockaddr)
  | _ -> None

let sendTo skt msg sktaddr =
  let _ = sendto skt (Bytes.of_string msg) 0 (String.length msg) [] sktaddr
  in ()

let rec listen skt handle =
  match (receiveFrom skt) with
  | Some msg -> handle (fst msg) (snd msg)
  | None -> listen skt handle

let rec listen_wait skt =
  match (receiveFrom skt) with
  | Some msg -> msg
  | None -> listen_wait skt

(** Aneris.lock manual translation with Mutex *)
let newlock () = Mutex.create ()
let acquire lk = Mutex.lock lk
let release lk = Mutex.unlock lk

(** Aneris.dict manual translation using lists *)
let dict_empty () = []
let dict_remove = List.remove_assoc
let dict_insert k v d = (k,v) :: dict_remove k d
let dict_lookup k db =
  try Some (List.assoc k db)
  with Not_found -> None


(** Aneris.vector_clocks manual translation using lists *)
let vect_make len e = List.init len (fun _ -> e)
let vect_nth vc i = try List.nth vc i with Failure _ -> assert false
let rec vect_update vc i v =
  match vc with
  | w :: l -> if i = 0 then v :: l else w :: vect_update l (i-1) v
  | [] -> []
let vect_inc vc i =
  let v = vect_nth vc i + 1 in
  vect_update vc i v
let vect_leq v1 v2 =
  List.for_all2 (fun a b -> a <= b) v1 v2
let vect_applicable v1 v2 i =
  let rec aux j l1 l2 =
    match (l1, l2) with
    | [], [] -> true
    | a :: q1, b :: q2 when i = j -> a = b + 1 && aux (j+1) q1 q2
    | a :: q1, b :: q2 -> a <= b && aux (j+1) q1 q2
    | _, _ -> false
  in aux 0 v1 v2
let rec vect_serialize v =
  match v with
  | a :: q -> String.concat  "_" ((string_of_int a) :: [vect_serialize q])
  | [] -> ""
let rec vect_deserialize s =
  try
    let i = String.index s '_' in
    try
      let x = int_of_string (String.sub s 0 i) in
      let vc =
        vect_deserialize (String.sub s (i+1) (String.length s - (i + 1))) in
      x :: vc
    with Failure _ -> assert false
  with Not_found -> []


(** Aneris.serialization manual translation *)
let string_ser x = x
let string_deser x = x
let int_ser n = string_of_int n
let int_deser s = int_of_string s

(* to simplify for time being, values are just integers *)
let val_ser v = string_of_int v
let val_deser s = int_of_string s

let prod_ser serA serB v =
  let s1 = serA (fst v) in
  let s2 = serB (snd v) in
  (string_of_int (String.length s1)) ^ "_" ^ s1 ^ s2

let prod_deser deserA deserB s =
  try
    let i = String.index s '_' in
    let len = int_of_string (String.sub s 0 i) in
    let s1 = String.sub s (i + 1) len in
    let s2 = String.sub s (i + 1 + len)
               (String.length s - (i + 1 + len)) in
    let v1 = deserA s1 in
    let v2 = deserB s2 in
    (v1, v2)
  with _ -> assert false

let either_ser left_ser right_ser v =
  match v with
  | (1, lv) -> "1_" ^ (left_ser lv)
  | (2, rv) -> "2_" ^ (right_ser rv)
  | _ -> assert false

let either_deser left_deser right_deser s =
  let i = String.index s '_' in
  let len = String.length s - 2 in
  match (String.sub s 0 1) with
  | "1" -> left_deser (String.sub s (i + 1) len)
  | "2" -> right_deser (String.sub s (i + 1) len)
  | _ -> assert false

let we_serialize =
  prod_ser
    (prod_ser
       (either_ser (prod_ser string_ser val_ser) 
                   (prod_ser string_ser val_ser))
       vect_serialize) int_ser

let we_deserialize =
  prod_deser
    (prod_deser
       (either_deser (prod_deser string_deser val_deser)
                     (prod_deser string_deser val_deser))
        vect_deserialize) int_deser


(* Type aliases for Ocaml but not present in Aneris *)
type vc = int list
type cmd = (int * (string * int))
type oper = ((cmd * vc) * int)

(* CCDDB manual translation  *)
let pi1 ((x,y),z) = x
let pi2 ((x,y),z) = y
let pi3 ((x,y),z) = z

let rec find f l = match l with
  | [] -> None
  | hd :: tl ->
      if f hd then Some (hd, tl) else
        match (find f tl) with
        | Some (hd',tl') -> Some (hd', hd :: tl')
        | None -> None

let check vc i w =
  let (wt, wo) = (pi2 w, pi3 w) in
  let test1 = (i != wo) in
  let test2 = (wo < List.length vc) in
  let test3 = (vect_applicable wt vc wo) in
  test1 && test2 && test3

let apply ctr vc lock (iq : oper list ref) i =
  let rec aux () =
    Thread.delay 1.;
    acquire lock;
    begin
      match (find (check !vc i) !iq) with
      | Some (w, iq') ->
         iq := iq';
         (match (pi1 w) with
         | (1, inc) -> ctr := !ctr + (snd inc)
         | (2, dec) -> ctr := !ctr - (snd dec)
         | _ -> assert false);
         vc := vect_inc !vc (pi3 w);
      | None -> ()
    end;
    release lock; aux ()
  in aux ()

let sendNext i skt (mq : oper Queue.t) sktaddrl acks =
  let rec aux () =
    if (Queue.is_empty mq) then ()
    else (
      let op = Queue.peek mq in 
      let vc = pi2 op in
      let dest = pi3 op in
      let sn = vect_nth vc i in
      let sn_ack = List.nth acks dest in
      if (sn = sn_ack) then
        (* The current message was acked, so we can move on
           to the next one.  *)
        (Queue.pop mq;
         aux ())
      else if (sn = sn_ack + 1) then
        (* The current message hasn't been acked.
           We should send or re-send it, in case
           it wasn't previously received.  *)
        sendTo skt (we_serialize op) (List.nth sktaddrl dest)
      else
        (* No other cases are possible:
           - sn < sn_ack is not possible because we would've already sent the message
           - sn > sn_ack + 1 is not possible because it means we sent two messages in a row
             without waiting for an ack *) 
        assert false
    )
    in
    aux ()

let send_thread i skt lock l acks oq =
  let rec aux () =
    Thread.delay 1.;
    acquire lock;
    match !oq with
    | [] -> release lock; aux ()
    | msgs :: oq' ->
      sendNext i skt msgs l acks;
      release lock;
      aux ()
  in aux ()

let receive_thread skt lock iq =
  let rec aux () =
    Thread.delay 0.5;
    let (msg, _) = listen_wait skt in
    (* Printf.printf "<debug received> %s \n" msg; *)
    (* flush Stdlib.stdout; *)
    acquire lock;
    iq := (we_deserialize msg) :: !iq;
    release lock; aux ()
  in aux ()

let read db lock x =
  (* Printf.printf "<debug> reading db before lock \n"; *)
  acquire lock;
  Thread.delay 0.3;
  (* Printf.printf "<debug> reading db \n"; *)
  (* flush Stdlib.stdout; *)
  let r = dict_lookup x !db in
  release lock; r

let write db vc oq lock i x v =
  acquire lock;
  Thread.delay 0.1;
  vc := vect_inc !vc i;
  db := dict_insert x v !db;
  oq := (((x, v), !vc), i) :: !oq;
  release lock

let init l i =
  let (ctr : int ref) = ref 0 in
  let n = List.length l in
  let vc = ref (vect_make n 0) in
  (* The in-queue contains a list of operations.
     An operation is a tuple (payload, vector-clock, source-index).
     The payload is either an inc or a dec.
     An (inc v) is represented as (1, ("INC", v)).
     A (dec v) is represented as (2, ("DEC", v)).

     The out-queue is a map of replica index to a queue of operations
     sorted increasingly by sequence number.
     An operation is represented as in the in-queue.
     The sequence number for replica i is the ith entry in the vector clock
     corresponding to the operation.
  *)
  let (iq : oper list ref) = ref [] in
  let (oq : (oper Queue.t) list ref) = ref (vect_make n (Queue.create ())) in
  (* A vector that maps replica indices to the highest ack
     received from that replica. *)
  let (acks : int list ref) = ref (vect_make (List.length l) 0) in
  let lock = newlock () in
  let skt = udp_socket () in
  socketBind skt (List.nth l i);
  let _ = Thread.create (apply ctr vc lock iq) i in
  let _ = Thread.create (send_thread i skt lock l acks) oq in
  let _ = Thread.create (receive_thread skt lock) iq in
  (read db lock, write db vc oq lock i)

(** Execution *)
let action i rd wr =
  let s = read_line () in
  match (String.split_on_char ' ' s) with
    "read" :: k :: [] ->
     begin
       match rd k with
         Some v -> Printf.printf "DB(%n)[%s] : %n\n"  i k v
       | None -> Printf.printf "DB(%n)[%s] : None\n" i k
     end
  | "write" :: k :: v :: [] ->
     let v = int_of_string v in
     let () = wr k v in
     Printf.printf "DB(%n)[%s <- %n]\n" i k v
  | "close" :: _ -> exit 0
  | _ -> Printf.printf "invalid command \n"

let init_exec () =
  if Array.length Sys.argv < 4
  then (prerr_endline "Usage: init <index> <port1 port2 ... portN>"; exit 2);
  let ip = (gethostbyname "localhost").h_addr_list.(0) in
  let l =
    let dbsa i = makeAddress ip (int_of_string Sys.argv.(i+2)) in
    List.init (Array.length Sys.argv - 2) dbsa in
  let i = int_of_string Sys.argv.(1) in
  let (rd, wr) = init l i in
  while true do action i rd wr done

let () = Unix.handle_unix_error init_exec ()

(* on a new terminal *)
(* ./ccddb 0 1200 1201 1202 *)
(* write x 37 *)
(* write x 1  *)

(* on a new terminal *)
(* ./ccddb 1 1200 1201 1202 *)
(* read x *)
(* write y 1 *)

(* on a new terminal *)
(* ./ccddb 2 1200 1201 1202 *)
(* read y *)
(* read x *)

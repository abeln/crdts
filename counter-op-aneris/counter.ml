(* Original CCDDB code by Leon Gondelman *)

open Unix
open Either

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

(* In AnerisLang we don't have ADTs, but we don't have types either.
   So in Ocaml for (de)serializing sums we use proper sums, but in
   AnerisLang we use tuples where the type of the second compoenent 
   depends on the tag (the first component). *)

let either_ser left_ser right_ser v =
  match v with
  | Left lv -> "1_" ^ (left_ser lv)
  | Right rv -> "2_" ^ (right_ser rv)

let either_deser left_deser right_deser s =
  let i = String.index s '_' in
  let len = String.length s - 2 in
  match (String.sub s 0 1) with
  | "1" -> Left (left_deser (String.sub s (i + 1) len))
  | "2" -> Right (right_deser (String.sub s (i + 1) len))
  | _ -> assert false

(* Type aliases for Ocaml but not present in Aneris *)
type vc = int list
type cmd = string * int (* ("INC", v) or ("DEC", v) *)
type oper = ((cmd * vc) * int)
type seqnum = int
type ack = (string * seqnum) * int (* (("ACK", seqnum), sender-id) *)

let mk_ack sn sender_id : ack = (("ACK", sn), sender_id)
let mk_oper cmd vc sender_id : oper = ((cmd, vc), sender_id)

let msg_of_oper op = Left op
let msg_of_ack ack = Right ack

let oper_ser = 
  prod_ser
    (prod_ser
      (prod_ser string_ser int_ser)
       vect_serialize)
    int_ser

let oper_deser =
  prod_deser
    (prod_deser
     (prod_deser string_deser int_deser)
      vect_deserialize)
    int_deser

let ack_ser =
  prod_ser (prod_ser string_ser int_ser)
           int_ser

let ack_deser =
  prod_deser (prod_deser string_deser int_deser)
             int_deser

let msg_ser = either_ser oper_ser ack_ser
  
let msg_deser = either_deser oper_deser ack_deser
  
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
      | Some (op, iq') ->
         let cmd = pi1 op in
         let sender_id = pi3 op in
         iq := iq';
         (match cmd with
         | ("INC", v) -> ctr := !ctr + v
         | ("DEC", v) -> ctr := !ctr - v
         | _ -> assert false
         );
         vc := vect_inc !vc sender_id;
      | None -> ()
    end;
    release lock; aux ()
  in aux ()

let sendNext i skt mq sktaddrl acks =
  let rec aux () =
    if (Queue.is_empty mq) then ()
    else
    begin
      let (op : oper) = Queue.peek mq in 
      let vc = pi2 op in
      let dest = pi3 op in
      let sn = vect_nth vc i in
      let sn_ack = List.nth !acks dest in
      if (sn = sn_ack) then
        begin
          (* The current message was acked, so we can move on
             to the next one.  *)
          let _ = Queue.pop mq in
          aux ()
        end
      else if (sn = sn_ack + 1) then
        begin
          (* The current message hasn't been acked.
             We should send or re-send it, in case
             it wasn't previously received.  *)
          sendTo skt (msg_ser (msg_of_oper op)) (List.nth sktaddrl dest)
        end
      else
        begin
          (* No other cases are possible:
            - sn < sn_ack is not possible because we would've already sent the message
            - sn > sn_ack + 1 is not possible because it means we sent two messages in a row
              without waiting for an ack *) 
          assert false
        end
    end
    in
    aux ()

let send_thread i skt lock l acks oq =
  let rec aux () =
    Thread.delay 1.;
    acquire lock;
    match !oq with
    | [] -> release lock; aux ()
    | mq :: oq' ->
      sendNext i skt mq l acks;
      release lock;
      aux ()
  in aux ()

let receive_thread i skt lock vc iq =
  let rec aux () =
    Thread.delay 0.5;
    let (msg, addr) = listen_wait skt in
    (* Printf.printf "<debug received> %s \n" msg; *)
    (* flush Stdlib.stdout; *)
    acquire lock;
    (match (msg_deser msg) with
    | Left op ->
        let sender_vc = pi2 op in
        let sender = pi3 op in
        let sender_sn = vect_nth sender_vc sender in
        let my_sn = vect_nth !vc sender in
        if (sender_sn < my_sn) then
          begin
            (* Must be a network duplicate, so ignore it *)
          end
        else if (sender_sn = my_sn) then
          begin
            (* Could be a duplicate, but it could also be that our ack
               got lost, so resend the ack  *)
            sendTo skt (msg_ser (msg_of_ack (mk_ack sender_sn i))) addr
          end
        else if (sender_sn = my_sn + 1) then
          begin
            (* This is a new message from the sender, so we need to store it
               and ack it. *)
            iq := op :: !iq;
            sendTo skt (msg_ser (msg_of_ack (mk_ack sender_sn i))) addr
          end
        else
          begin
            (* We must have sender_sn > my_sn + 1, but that can't happen because
               we're running stop-and-wait *)
            assert false
          end
    | Right ack -> ()
    );
    release lock; aux ()
  in aux ()

let read ctr lock =
  (* Printf.printf "<debug> reading db before lock \n"; *)
  acquire lock;
  Thread.delay 0.3;
  (* Printf.printf "<debug> reading db \n"; *)
  (* flush Stdlib.stdout; *)
  let r = !ctr in
  release lock; r

let update ctr vc oq lock i cmd =
  acquire lock;
  Thread.delay 0.1;
  vc := vect_inc !vc i;
  let tag = fst cmd in
  let v = snd cmd in
  let op = mk_oper cmd !vc i in
  (match tag with
  | "INC" -> ctr := !ctr + v
  | "DEC" -> ctr := !ctr - v
  | _ -> assert false);
  (* Put the new op in every out-queue *)
  List.iter (fun q -> Queue.push op q) !oq;
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
  let _ = Thread.create (receive_thread i skt lock vc) iq in
  (read ctr lock, update ctr vc oq lock i)

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

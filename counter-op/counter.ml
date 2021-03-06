open Base
open Unix

let ( = ) = Poly.( = )
let ( > ) = Poly.( > )


(** Aneris.network_helpers translation *)
module A = struct
  let udp_socket () = socket PF_INET SOCK_DGRAM 0

  let makeAddress ip port = ADDR_INET (ip, port)

  let socketBind socket addr = bind socket addr

  let receiveFrom skt =
    let buffer = Bytes.create 1024 in
    match recvfrom skt buffer 0 1024 [] with
    | len, (ADDR_INET _ as sockaddr) ->
        let msg = Caml.Bytes.sub_string buffer 0 len in
        Some (msg, sockaddr)
    | _ -> None

  let sendTo skt msg sktaddr =
    let (_ : file_perm) =
      sendto skt (Bytes.of_string msg) 0 (String.length msg) [] sktaddr
    in
    ()
end

module VC = struct
  let sexp_of_sockaddr addr =
    match addr with
    | ADDR_UNIX _ -> Sexp.Atom "UNSUPPORTED"
    | ADDR_INET (a, port) ->
        Sexp.List
          [ Sexp.Atom (string_of_inet_addr a); Sexp.Atom (Int.to_string port) ]

  let sockaddr_of_sexp sexp =
    match sexp with
    | Sexp.List [ Sexp.Atom a; Sexp.Atom port ] ->
        ADDR_INET (inet_addr_of_string a, Int.of_string port)
    | _ ->
        Sexp.Of_sexp_error (Invalid_argument "not a socket address", sexp)
        |> raise

  (* TODO: upgrade to maps? *)
  type t = (sockaddr, int) List.Assoc.t [@@deriving sexp]

  type cmp_res = Lt | Gt | Eq | Co (* concurrent *)

  let init addrs = List.map addrs ~f:(fun addr -> (addr, 0))

  let cmp vc1 vc2 =
    assert (List.length vc1 = List.length vc2);
    List.fold vc1 ~init:Eq ~f:(fun acc e1 ->
        let k1, v1 = e1 in
        let v2 = List.Assoc.find_exn vc2 ~equal:( = ) k1 in
        match acc with
        | Eq -> if v1 < v2 then Lt else if v1 > v2 then Gt else Eq
        | Lt -> if v1 > v2 then Co else Lt
        | Gt -> if v1 < v2 then Co else Gt
        | Co -> Co)

  (* Computes the pointwise max of two vector clocks. *)
  let merge vc1 vc2 =
    assert (List.length vc1 = List.length vc2);
    List.map vc1 ~f:(function k1, v1 ->
        (k1, Int.max v1 (List.Assoc.find_exn vc2 ~equal:( = ) k1)))

  (* Does vc_next correspond to an operation that causally follows vc_base  without any interleaving operations?
     This is the case if every entry in vc_next is <= than the corresponding one in vc_base, except for exactly
     one entry which must be exactly one larger than vc_base's. *)
  let causal_next ~vc_base ~vc_next =
    assert (List.length vc_base = List.length vc_next);
    let counts =
      List.map vc_next ~f:(function next_k, next_v ->
          let base_v = List.Assoc.find_exn vc_base ~equal:( = ) next_k in
          if next_v <= base_v then (1, 0)
          else if next_v = base_v + 1 then (0, 1)
          else (0, 0))
    in
    let pair_add p1 p2 =
      match (p1, p2) with (v11, v12), (v21, v22) -> (v11 + v21, v12 + v22)
    in
    let le_count, next_count = List.fold counts ~init:(0, 0) ~f:pair_add in
    le_count + next_count = List.length vc_base

  let seqnum vc addr = List.Assoc.find_exn vc ~equal:( = ) addr
end

module type COUNTER = sig
  (* State of the counter *)
  type t

  (* An operation propagated to other nodes *)
  type op [@@deriving sexp]

  (* A command is a local operation issued by the client. *)
  type cmd = Inc | Dec [@@deriving sexp]

  (* Creates a new counter with replicas at addrs, where the current node
     is at local_addr. *)
  val init : addrs:sockaddr list -> local_addr:sockaddr -> t

  (* The current value of the counter *)
  val query : t -> int

  (* Returns the vector clock of the current state of the counter *)
  val vc_of_t : t -> VC.t

  (* Returns the vector clock corresponding to the operation *)
  val vc_of_op : op -> VC.t

  (* Updates the counter according to the provided op.
     Returns the new state of the counter. *)
  val update : t -> op -> t

  (* Turns a local command into an operation and immediately executes it.
     Returns the new state of the counter and the corresponding operation that
     should be propagated. *)
  val local_update : t -> cmd -> t * op
end

module Counter : COUNTER = struct
  (* The state of the counter is a tuple
     (current value, vector clock of the last update, socket address ). *)
  type t = int * VC.t * sockaddr

  type cmd = Inc | Dec [@@deriving sexp]

  (* An operation packages a command with the associated vector clock, so it
     can be propagated. *)
  type op = cmd * VC.t [@@deriving sexp]

  let init ~addrs ~local_addr =
    assert (List.mem addrs local_addr ~equal:( = ));
    (0, VC.init addrs, local_addr)

  let query st =
    let v, _, _ = st in
    v

  let vc_of_t = function _, vc, _ -> vc

  let vc_of_op = function _, vc -> vc

  (* TODO: should this check the op's vector clock? *)
  let update st op =
    let v, vc, addr = st in
    let cmd, vc_op = op in
    let new_v = match cmd with Inc -> v + 1 | Dec -> v - 1 in
    (new_v, VC.merge vc vc_op, addr)

  let local_update st cmd =
    let _, vc, addr = st in
    let ts = List.Assoc.find_exn vc ~equal:( = ) addr in
    let new_vc = List.Assoc.add vc ~equal:( = ) addr (ts + 1) in
    let new_op = (cmd, new_vc) in
    (update st new_op, new_op)
end

(* Two kinds of operations:
    - an (Ack n) as a response to a message from a replica
      at 'addr' means that we've locally applied the n-th op originating
      at 'addr'
    - a Counter.op is a locally-applied op that we need to transmit to other
      replicas
*)
type msg = Ack of int | Op of Counter.op [@@deriving sexp]

(* TODO: we should be doing arithmetic modulo some N *)
type seqnum = int

type ctx = {
  skt : file_descr;
  addr : sockaddr;
  inq : (Counter.op * sockaddr) list ref;
  outq : (sockaddr, msg list) List.Assoc.t ref;
  acks : (sockaddr, seqnum) List.Assoc.t ref;
  counter : Counter.t ref;
  lock : Nano_mutex.t;
}

let add_msg outq addr msg =
  let msgs = List.Assoc.find_exn outq ~equal:( = ) addr in
  List.Assoc.add outq ~equal:( = ) addr (msg :: msgs)

let gen_ack vc addr = VC.seqnum vc addr |> Ack

let receive_loop ctx =
  let rec run () =
    (match A.receiveFrom ctx.skt with
    | Some (raw_msg, addr) ->
        let msg = msg_of_sexp (Parsexp.Single.parse_string_exn raw_msg) in
        (* Caml.Printf.printf "received message %s\n" raw_msg; *)
        Nano_mutex.lock_exn ctx.lock;
        (match msg with
        | Ack sn ->
            let ack_sn = List.Assoc.find_exn !(ctx.acks) ~equal:( = ) addr in
            if sn > ack_sn then
              ctx.acks := List.Assoc.add !(ctx.acks) ~equal:( = ) addr sn
            else (* ignore ack: it's too small so it was already processed *)
              ()
        | Op op ->
            (* All ops are added to the in-queue. Acks are issued in the apply loop,
               which also prunes stale ops. *)
            ctx.inq := (op, addr) :: !(ctx.inq));
        Nano_mutex.unlock_exn ctx.lock
    | None -> ());
    run ()
  in
  run ()

let send_loop ctx =
  let last_op_sent_secs = ref (Unix.time ()) in
  let rec run () =
    Nano_mutex.lock_exn ctx.lock;
    let new_outq =
      List.fold !(ctx.outq) ~init:[] ~f:(fun acc entry ->
          let addr, msgs = entry in
          let sn = List.Assoc.find_exn !(ctx.acks) ~equal:( = ) addr in
          let new_msgs =
            List.fold msgs ~init:[] ~f:(fun ms m ->
                match m with
                | Ack _ ->
                    (* we always send all acks immediately *)
                    A.sendTo ctx.skt (Sexp.to_string (sexp_of_msg m)) addr;
                    (* remove the ack *)
                    ms
                | Op op ->
                    let vc = Counter.vc_of_op op in
                    let sn_op = List.Assoc.find_exn vc ~equal:( = ) ctx.addr in
                    if sn_op <= sn then
                      (* The op has already been acked, and can now be removed *)
                      ms
                    else if sn_op = sn + 1 && ((Unix.time ()) -. !last_op_sent_secs > 1.0) then (
                      (* We're implementing stop-and-wait, so the next op can be sent.
                         Wait at least a second between sent ops so we give other replicas time to reply. *)
                      A.sendTo ctx.skt (Sexp.to_string (sexp_of_msg m)) addr;
                      last_op_sent_secs := Unix.time ();
                      (* Leave the op around until it's acked *)
                      m :: ms)
                    else
                      (* The op should be sent, but only after a previous op is acknowledged,
                         so do nothing for now *)
                      m :: ms)
          in
          (addr, new_msgs) :: acc)
    in
    ctx.outq := new_outq;
    Nano_mutex.unlock_exn ctx.lock;
    run ()
  in
  run ()

let apply_loop ctx : unit =
  let rec run () =
    Nano_mutex.lock_exn ctx.lock;
    (* Fold over the in queue and apply all ops that are causally next
       after the current vc. Prune all old ops. This fold has side effects. *)
    let new_inq =
      List.fold !(ctx.inq) ~init:[] ~f:(fun acc_inq op_and_addr ->
          let op, addr = op_and_addr in
          let vc = Counter.vc_of_t !(ctx.counter) in
          let op_vc = Counter.vc_of_op op in
          match VC.cmp vc op_vc with
          | VC.Gt | VC.Eq ->
              (* prune old op, but also send an ack in case the previous one got lost.
                 Use the current vc instead of the op vc because the current vc is necessarily
                 more up-to-date. *)
              ctx.outq := add_msg !(ctx.outq) addr (gen_ack vc addr);
              acc_inq
          | _ ->
              if VC.causal_next ~vc_base:vc ~vc_next:op_vc then (
                (* We can apply the op as a side effect *)
                ctx.counter := Counter.update !(ctx.counter) op;
                (* Now acknowledge it *)
                ctx.outq := add_msg !(ctx.outq) addr (gen_ack op_vc addr);
                (* Prune it from the list *)
                acc_inq)
              else
                (* save and apply in the future : don't acknowledge because
                   we haven't applied it *)
                (op, addr) :: acc_inq)
    in
    ctx.inq := new_inq;
    Nano_mutex.unlock_exn ctx.lock;
    run ()
  in
  run ()

type io_cmd = Cmd of Counter.cmd | Query

(* Read one command from stdin *)
let get_cmd () =
  match Caml.read_line () with
  | "inc" -> Some (Cmd Counter.Inc)
  | "dec" -> Some (Cmd Counter.Dec)
  | "q" -> Some Query
  | _ -> None

let rec io_loop ctx : unit =
  (match get_cmd () with
  | None -> Caml.Printf.printf "invalid\n"
  | Some Query -> Caml.Printf.printf "%d\n" (Counter.query !(ctx.counter))
  | Some (Cmd cmd) ->
      Nano_mutex.lock_exn ctx.lock;
      (* Apply the command locally *)
      let new_counter, new_op = Counter.local_update !(ctx.counter) cmd in
      ctx.counter := new_counter;
      (* And then propagate it *)
      ctx.outq := List.Assoc.map !(ctx.outq) ~f:(fun msgs -> Op new_op :: msgs);
      Nano_mutex.unlock_exn ctx.lock;
      Caml.Printf.printf "%d\n" (Counter.query !(ctx.counter)));
  io_loop ctx

(* TODO: use the Aneris version instead *)
let mk_addr ip_str port_str =
  ADDR_INET (inet_addr_of_string ip_str, Int.of_string port_str)

let splitList lst =
  let l, r, _ =
    List.fold lst ~init:([], [], true) ~f:(fun acc e ->
        match acc with
        | l, r, true -> (e :: l, r, false)
        | l, r, false -> (l, e :: r, true))
  in
  (l, r)

let () =
  let argv = Sys.get_argv () in
  let my_addr = mk_addr argv.(1) argv.(2) in
  let other_addrs =
    Array.to_list (Array.sub argv ~pos:3 ~len:(Array.length argv - 3))
    |> splitList
    |> (function l, r -> List.zip_exn l r)
    |> List.map ~f:(function addr, port -> mk_addr addr port)
  in
  let addrs = my_addr :: other_addrs in
  let skt = A.udp_socket () in
  A.socketBind skt my_addr;
  let ctx =
    {
      acks = ref (List.map other_addrs ~f:(fun addr -> (addr, 0)));
      addr = my_addr;
      skt;
      counter = ref (Counter.init ~addrs ~local_addr:my_addr);
      inq = ref [];
      outq = ref (List.map other_addrs ~f:(fun addr -> (addr, [])));
      lock = Nano_mutex.create ();
    }
  in
  (* TODO: set socket receive timeout: https://ocaml.org/api/Unix.html#VALsetsockopt_float *)
  ignore (Thread.create apply_loop ctx : Thread.t);
  ignore (Thread.create receive_loop ctx : Thread.t);
  ignore (Thread.create send_loop ctx : Thread.t);
  io_loop ctx

open Base
open Unix

let ( = ) = Poly.( = )

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
  inq : Counter.op list ref;
  outq : (sockaddr, msg list) List.Assoc.t ref;
  acks : (sockaddr, seqnum) List.Assoc.t ref;
  current_vc : VC.t;
  lock : Nano_mutex.t;
}

let rec receive_loop ctx =
  let run () =
    match A.receiveFrom ctx.skt with
    | Some (msg, addr) ->
        let msg = msg_of_sexp (String.sexp_of_t msg) in
        Nano_mutex.lock_exn ctx.lock;
        (match msg with
        | Ack sn ->
            let ack_sn = List.Assoc.find_exn !(ctx.acks) ~equal:( = ) addr in
            if sn = ack_sn + 1 then
              ctx.acks := List.Assoc.add !(ctx.acks) ~equal:( = ) addr sn
            else
              (* ignore ack: if too small then it was already processed;
                 if too high then it was received out of order and it'll be re-sent *)
              ()
        | Op op ->
            (* All ops are added to the in-queue. Acks are issued in the apply loop,
               which also prunes stale ops. *)
            ctx.inq := op :: !(ctx.inq));
        Nano_mutex.unlock_exn ctx.lock
    | None -> ()
  in
  run ()

let send_loop ctx =
  let run () =
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
                    A.sendTo ctx.skt (String.t_of_sexp (sexp_of_msg m)) addr;
                    (* remove the ack *)
                    ms
                | Op op ->
                    let vc = Counter.vc_of_op op in
                    let sn_op = List.Assoc.find_exn vc ~equal:( = ) addr in
                    if sn_op <= sn then
                      (* The op has already been acked, and can now be removed *)
                      ms
                    else if sn_op = sn + 1 then (
                      (* We're implementing stop-and-wait, so the next op can be sent *)
                      A.sendTo ctx.skt (String.t_of_sexp (sexp_of_msg m)) addr;
                      ms)
                    else
                      (* The op should be sent, but only after a previous op is acknowledged,
                         so do nothing for now *)
                      m :: ms)
          in
          (addr, new_msgs) :: acc)
    in
    ctx.outq := new_outq;
    Nano_mutex.unlock_exn ctx.lock
  in
  run ()

(*
module type RCB = sig
  type msg = VC.t * string

  type t

  val init : file_descr -> sockaddr -> t

  val receiveFrom : t -> (msg * sockaddr) option

  val sendTo : t -> msg -> sockaddr list -> unit
end

module Mailbox = struct
  type op = Op of VC.t * string [@@deriving sexp]

  type msg = Ack of int | OpMsg of op [@@deriving sexp]

  type seqnum = int

  type t = {
    skt : file_descr;
    inq : op list ref;
    outq : (sockaddr, msg list) List.Assoc.t ref;
    seen : (sockaddr, seqnum * bool) List.Assoc.t ref;
    lock : Nano_mutex.t;
  }

  (* Check whether the given ack with sequence number 'sn' is the
     expected one for the given 'addr'. *)
  let expect_sn seen addr sn =
    List.exists seen ~f:(function
      | seen_addr, (seen_sn, false) -> seen_addr = addr && seen_sn = sn
      | _ -> false)

  let rec receive_loop st =
    let run () =
      match A.receiveFrom st.skt with
      | Some (msg, addr) ->
          let msg = msg_of_sexp (String.sexp_of_t msg) in
          Nano_mutex.lock_exn st.lock;
          (match msg with
          | Ack sn ->
              if expect_sn !(st.seen) addr sn then
                st.seen := List.Assoc.add !(st.seen) ~equal:( = ) addr (sn, true)
              else ()
          | OpMsg op -> st.inq := op :: !(st.inq));
          Nano_mutex.unlock_exn st.lock
      | None -> ()
    in
    run ()

  let rec send_loop st =
    let run () = 
      true
    in
    run ()

  let init skt addr = ()

  let receiveFrom st = ()
end

(* We need multiple threads:
      1) the tcp server thread that reads messages and puts them in the in queue
      3) a thread that processes user requests and puts them in the out queue
      4) a thread that sends out queue requests
      5) the in queue and out queue and counter and a mutex *)

(* Loop and apply all applicable ops in the in queue *)
let rec apply_loop ctx : unit =
  Nano_mutex.lock_exn ctx.lock;
  (* Fold over the in queue and apply all ops that are causally next
     after the current vc. Prune all old ops. This fold has side effects. *)
  let new_inq =
    List.fold !(ctx.inq)
      ~init:([] : Counter.op list)
      ~f:(fun (acc_inq : Counter.op list) op ->
        let vc = Counter.get_vc !(ctx.cnt) in
        let op_vc = Counter.get_op_vc op in
        match VC.cmp vc op_vc with
        | VC.Gt | VC.Eq -> acc_inq (* prune old op *)
        | _ ->
            if VC.causal_next ~vc_base:vc ~vc_next:op_vc then (
              (* We can apply the op as a side effect *)
              ctx.cnt := Counter.update !(ctx.cnt) op;
              (* Prune it from the list *)
              acc_inq)
            else op :: acc_inq
        (* save and apply in the future*))
  in
  ctx.inq := new_inq;
  Nano_mutex.unlock_exn ctx.lock;
  apply_loop ctx

let rec server_loop (ctx, skt) =
  (* TODO: figure out whether it's ok to receive strings *)
  (match A.receiveFrom skt with
  | Some (msg, _) ->
      let op = Counter.op_of_sexp (String.sexp_of_t msg) in
      Nano_mutex.lock_exn ctx.lock;
      ctx.inq := op :: !(ctx.inq);
      Nano_mutex.unlock_exn ctx.lock
  | None -> ());
  server_loop (ctx, skt)

(* Send the op to all addresses in addrs using stop-and-wait *)
let send_to_all op skt addrs =
  let op_str = Sexp.to_string(Counter.sexp_of_op op) in
  (* Implements stop-and-wait ARQ: https://en.wikipedia.org/wiki/Stop-and-wait_ARQ
     without alternating bit, because we already do de-duplication via the vector clock *)
  let rec send addr =
    A.sendTo skt op_str addr;
    match (A.receiveFrom skt) with  
      Some (res, )
  in
  List.iter addrs ~f:send

(* Send the messages in the out-queue to the given addresses *)
let rec reply_loop (ctx, skt, addrs) =
  Nano_mutex.lock_exn ctx.lock;
  (match !(ctx.outq) with
  | [] -> Nano_mutex.unlock_exn ctx.lock
  | op :: ops ->
      ctx.outq := ops;
      Nano_mutex.unlock_exn ctx.lock;
      send_to_all op skt addrs);
  reply_loop (ctx, skt, addrs)

type cmd = Cmd of Counter.cmd | Query

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
  | Some Query -> Caml.Printf.printf "%d\n" (Counter.query !(ctx.cnt))
  | Some (Cmd cmd) ->
      Nano_mutex.lock_exn ctx.lock;
      let new_cnt, new_op = Counter.local_update !(ctx.cnt) cmd in
      ctx.cnt := new_cnt;
      (* TODO: make the out queue really a queue *)
      ctx.outq := new_op :: !(ctx.outq);
      Nano_mutex.unlock_exn ctx.lock;
      Caml.Printf.printf "%d\n" (Counter.query !(ctx.cnt)));
  io_loop ctx

let () =
  (* TODO: fill in details below *)
  let ctx =
    {
      cnt =
        ref (Counter.init ~addrs:[ "192.168.0.1" ] ~local_addr:"192.168.0.1");
      inq = ref [];
      outq = ref [];
      lock = Nano_mutex.create ();
    }
  in
  let skt = A.udp_socket () in
  let addr = A.makeAddress ip port in
  A.socketBind skt addr;
  (* TODO: set socket receive timeout: https://ocaml.org/api/Unix.html#VALsetsockopt_float *)
  ignore (Thread.create apply_loop ctx : Thread.t);
  ignore (Thread.create server_loop (ctx, skt) : Thread.t);
  io_loop ctx
*)

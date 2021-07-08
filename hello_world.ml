

open Base
open Async

module VC = struct

  (* TODO: find the proper type *)
  type ip = string [@@deriving sexp]

  (* TODO: upgrade to maps? *)
  type t = (ip, int) List.Assoc.t [@@deriving sexp]

  type cmp_res = 
    Lt | Gt | Eq | Co (* concurrent *)

  let init ips =
    List.map ips ~f:(fun ip -> (ip, 0))

  let cmp vc1 vc2 = 
    assert (List.length vc1 = List.length vc2);
    List.fold vc1 ~init:Eq ~f:(fun acc e1 -> let (k1, v1) = e1 in
      let v2 = List.Assoc.find_exn vc2 ~equal:String.equal k1 in
      match acc with 
      | Eq ->
        if (v1 < v2) then Lt
        else if v1 > v2 then Gt
        else Eq
      | Lt ->
        if v1 > v2 then Co
        else Lt
      | Gt ->
        if v1 < v2 then Co
        else Gt
      | Co -> Co
    ) 

  (* Computes the pointwise max of two vector clocks. *)
  let merge vc1 vc2 = 
    assert (List.length vc1 = List.length vc2);
    List.map vc1 ~f:(function (k1, v1) -> (k1, Int.max v1 (List.Assoc.find_exn vc2 ~equal:String.equal k1)))

    (* Does vc_next correspond to an operation that causally follows vc_base  without any interleaving operations?
       This is the case if every entry in vc_next is <= than the corresponding one in vc_base, except for exactly
       one entry which must be exactly one larger than vc_base's. *)
  let causal_next ~vc_base ~vc_next =
    assert (List.length vc_base = List.length vc_next);
    let counts = List.map vc_next ~f:(function (next_k, next_v) ->
      let base_v = List.Assoc.find_exn vc_base ~equal:String.equal next_k in
      if (next_v <= base_v) then (1, 0)
      else if (next_v = base_v + 1) then (0, 1)
      else (0, 0))
    in
    let pair_add = fun p1 p2 ->
      match p1, p2 with
      | (v11, v12), (v21, v22) -> (v11 + v21, v12 + v22)
    in
    let (le_count, next_count) = List.fold counts ~init:(0, 0) ~f:pair_add in
    le_count + next_count = List.length vc_base

end

module type COUNTER = sig

  (* TODO: use a better type? *)
  type ip = string
  
  (* State of the counter *)
  type t

  (* An operation propagated to other nodes *)
  type op [@@deriving sexp]

  (* A command is a local operation issued by the client. *)
  type cmd = Inc | Dec [@@deriving sexp]

  (* Creates a new counter with replicas at addrs, where the current node
     is at local_addr. *)
  val init : addrs:(ip list) -> local_addr:ip -> t

  (* The current value of the counter *)
  val query : t -> int

  (* Returns the vector clock of the current state of the counter *)
  val get_vc : t -> VC.t

  (* Returns the vector clock corresponding to the operation *)
  val get_op_vc : op -> VC.t

  (* Updates the counter according to the provided op.
     Returns the new state of the counter. *)
  val update : t -> op -> t

  (* Turns a local command into an operation and immediately executes it.
     Returns the new state of the counter. *)
  val local_update : t -> cmd -> t * op

end

module Counter : COUNTER = struct

  type ip = string

  (* The state of the counter is a tuple
       (current value, vector clock of the last update, ip address). *)
  type t = (int * VC.t * string) 

  type cmd = Inc | Dec [@@deriving sexp]

  (* An operation packages a command with the associated vector clock, so it
     can be propagated. *)
  type op = cmd * VC.t [@@deriving sexp]

  let init ~addrs ~local_addr =
    assert (List.mem addrs local_addr ~equal:String.equal);
    ((0, VC.init addrs, local_addr) : t)

  let query (cnt : t) =
    let (v, _, _) = cnt in v

  let get_vc = function (_, vc, _) -> vc

  let get_op_vc = function (_, vc) -> vc

  (* TODO: should we be incrementing the local VC for the counter here? *)
  let update cnt oper = 
    let (v, vc, ip) = cnt in
    let (cmd, vc_op) = oper in
    let new_v = (match cmd with
    | Inc -> v + 1
    | Dec -> v - 1)
    in  
    (new_v, VC.merge vc vc_op, ip)

  let local_update cnt cmd =
    let (_, vc, ip) = cnt in
    let ts = List.Assoc.find_exn vc ~equal:String.equal ip in
    let new_vc = List.Assoc.add
                  (List.Assoc.remove vc ~equal:String.equal ip)
                  ~equal:String.equal
                  ip (ts + 1) in
    let new_op = (cmd, new_vc) in
    (update cnt new_op, new_op)

end

(* We need multiple threads:
      1) the tcp server thread that reads messages and puts them in the in queue
      3) a thread that processes user requests and puts them in the out queue
      4) a thread that sends out queue requests
      5) the in queue and out queue and counter and a mutex *)

type ctx =
  { cnt : Counter.t ref;
    inq : Counter.op list ref;
    outq : Counter.op list ref;
    lock : Nano_mutex.t;
  }

  (* Run one round of processing in the in queue *)
  let apply_once ctx : unit Deferred.t =
    Nano_mutex.lock_exn ctx.lock;
    (* Fold over the in queue and apply all ops that are causally next
     after the current vc. Prune all old ops. This fold has side effects. *)
    let new_inq = List.fold !(ctx.inq) ~init:([] : Counter.op list)  ~f:(fun (acc_inq : Counter.op list) op ->
      let vc = Counter.get_vc !(ctx.cnt) in
      let op_vc = Counter.get_op_vc op in
      match (VC.cmp vc op_vc) with
      | VC.Gt | VC.Eq -> acc_inq (* prune old op *)
      | _ ->
        if (VC.causal_next ~vc_base:vc ~vc_next:op_vc) then (
          (* We can apply the op as a side effect *)
          ctx.cnt := Counter.update !(ctx.cnt) op;
          (* Prune it from the list *)
          acc_inq)
        else
          op :: acc_inq (* save and apply in the future*)) in
    ctx.inq := new_inq;
    Nano_mutex.unlock_exn ctx.lock;
    return ()

(* Loop and apply all applicable ops in the in queue *) 
  let rec apply_ops ctx : unit Deferred.t =
    (* We need one bind here so that the scheduler can schedule in another "thread" *)
    apply_once ctx >>= (fun _ -> apply_ops ctx)

let buffer_size = 100 * 1024 (* 100 kilobytes *)
let add_op ctx r =
  let buffer = Bytes.create buffer_size in
  Reader.read r buffer
  >>= function
  | `Eof -> return ()
  | `Ok _ ->
    (* TODO: this is a hack since we're only reading once. Fix. *)
    let op = Counter.op_of_sexp (String.sexp_of_t (Bytes.to_string buffer)) in
    Nano_mutex.lock_exn ctx.lock;
    ctx.inq := op :: !(ctx.inq);
    Nano_mutex.unlock_exn ctx.lock;
    return ()

let run_server ctx port =
  Tcp.Server.create
    ~on_handler_error:`Raise
    (Tcp.Where_to_listen.of_port port)
    (fun _addr r w ->
      add_op ctx r
      >>= (fun _ ->
      Writer.write w "ACK";
      Writer.flushed w))

(* User-level commands *)
type cmd_or_query =
| Cmd of Counter.cmd
| Query

(* Read one command from stdin *)
let get_cmd () =
  match Caml.read_line () with
  | "inc" -> Some (Cmd Counter.Inc)
  | "dec" -> Some (Cmd Counter.Dec)
  | "q" -> Some Query
  | _ -> None

let rec io_loop ctx : unit = 
  (match get_cmd () with
  |  None -> ()
  | Some Query ->
    Caml.Printf.printf "%d\n" (Counter.query !(ctx.cnt))
  | Some (Cmd cmd) ->
    Nano_mutex.lock_exn ctx.lock;
    let new_cnt, _ = Counter.local_update !(ctx.cnt) cmd in
    ctx.cnt := new_cnt;
    Nano_mutex.unlock_exn ctx.lock);
    Caml.Printf.printf "%d\n" (Counter.query !(ctx.cnt));
    io_loop ctx
  
  let () =
    (* TODO: fill in details below *)
    let ctx = {
      cnt = ref (Counter.init ~addrs:["192.168.0.1"] ~local_addr:"192.168.0.1");
      inq = ref [];
      outq = ref [];
      lock = Nano_mutex.create ();
    } in
    (* let port = 0 in *)
    (* ignore(run_server ctx port : (Socket.Address.Inet.t, int) Tcp.Server.t Deferred.t); *)
    io_loop ctx
    (* ignore(Thread.create ~on_uncaught_exn:`Kill_whole_process io_loop ctx : Thread.t); *)

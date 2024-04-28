open Global
open Util
open Process.Messages
module Set = Set.Make (Pid)

type internal = {
  mutable reader_count : int;
      (* Track number of readers and keep their PIDs in a set to validate messages *)
  status : state;
  read_queue : Pid.t Lf_queue.t;
  write_queue : Pid.t Lf_queue.t;
}

and state = Reading of Set.t | Writing of Pid.t | Unlocked

type 'a t = { mutable inner : 'a; process : Pid.t }

type error =
  [ `not_owner | `multiple_unlocks | `locked | `process_died | `invalid_message ]

(* Process *)

type Message.t +=
  | Read of Pid.t
  | Lock_accepted
  | Write of Pid.t
  | Try of [ `read | `write ] * Pid.t
  | Unlock of Pid.t
  | Unlock_accepted
  | Failed of error

let rec loop state =
  match[@warning "-8"] receive_any () with
  | Read reader -> handle_read state reader
  | Write writer -> handle_write state writer
  | Try (action, pid) -> handle_try state pid action
  | Unlock pid -> handle_unlock state pid
  | Monitor (Process_down fell_pid) -> handle_proc_down state fell_pid

and handle_read ({ reader_count; read_queue; status; _ } as state) reader =
  match status with
  | Reading readers ->
      monitor reader;
      send reader Lock_accepted;
      state.reader_count <- succ reader_count;
      let status = Reading (Set.add reader readers) in
      loop { state with status }
  | Unlocked ->
      monitor reader;
      send reader Lock_accepted;
      state.reader_count <- succ reader_count;
      let readers = Set.of_list [ reader ] in
      loop { state with status = Reading readers }
  | Writing _ ->
      Lf_queue.push read_queue reader;
      loop state

and handle_write ({ write_queue; status; _ } as state) writer =
  match status with
  | Unlocked ->
      monitor writer;
      send writer Lock_accepted;
      loop { state with status = Writing writer }
  | _ ->
      Lf_queue.push write_queue writer;
      loop state

and handle_try ({ status; reader_count; _ } as state) pid = function
  | `read when reader_count = 0 && status <> Unlocked ->
      send pid @@ Failed `locked
  | `read -> handle_read state pid
  | `write when status <> Unlocked -> send pid @@ Failed `locked
  | `write -> handle_write state pid

and handle_unlock ({ reader_count; status; _ } as state) pid =
  match status with
  | Reading readers when Set.mem pid readers ->
      send pid Unlock_accepted;
      demonitor pid;
      state.reader_count <- pred reader_count;
      if state.reader_count = 0 then
        check_queues { state with status = Unlocked }
      else
        let status = Reading (Set.remove pid readers) in
        loop { state with status }
  | Writing current when Pid.equal pid current ->
      send pid Unlock_accepted;
      demonitor pid;
      check_queues state
  | Unlocked ->
      Logger.error (fun f -> f "RWLock received multiple unlocks");
      send pid @@ Failed `multiple_unlocks;
      loop state
  | _ ->
      Logger.error (fun f -> f "RWLock received invalid unlock");
      send pid @@ Failed `not_owner;
      loop state

and handle_proc_down ({ reader_count; status; _ } as state) fell_pid =
  match status with
  | Reading readers when Set.mem fell_pid readers ->
      Logger.error (fun f -> f "RWLock: Reader process failed");
      state.reader_count <- pred reader_count;
      loop { state with status = Reading (Set.remove fell_pid readers) }
  | Writing writer when Pid.equal writer fell_pid ->
      Logger.error (fun f -> f "RWLock: Writer process failed");
      check_queues state
  | _ ->
      Logger.error (fun f -> f "RWLock failed to demonitor all processes");
      loop state

and check_queues ({ write_queue; read_queue; _ } as state) =
  if Lf_queue.is_empty write_queue then
    if Lf_queue.is_empty read_queue then loop state else grant_readers state
  else
    let writer = Lf_queue.pop write_queue |> Option.get in
    loop { state with status = Writing writer }

and grant_readers state =
  let rec grant ({ read_queue; reader_count; _ } as state) read_set =
    match Lf_queue.pop read_queue with
    | Some reader ->
        monitor reader;
        send reader Lock_accepted;
        state.reader_count <- succ reader_count;
        let read_set = Set.add reader read_set in
        grant state read_set
    | None -> loop { state with status = Reading read_set }
  in
  grant state (Set.of_list [])

(* API internals *)

let selector = function
  | (Lock_accepted | Unlock_accepted | Failed _ | Monitor (Process_down _)) as
    msg ->
      `select msg
  | _ -> `skip

let wait_lock { process; _ } msg =
  monitor process;
  send process msg;
  match receive ~selector () with
  | Lock_accepted -> Ok ()
  | Failed reason -> Error reason
  | Monitor (Process_down _) -> Error `process_died
  | _ -> Error `invalid_message

let try_wait_lock { process; _ } mode =
  monitor process;
  send process @@ Try (mode, self ());
  match receive ~selector () with
  | Lock_accepted -> Ok ()
  | Failed reason -> Error reason
  | Monitor (Process_down _) -> Error `process_died
  | _ -> Error `invalid_message

let unlock { process; _ } =
  send process @@ Unlock (self ());
  match receive ~selector () with
  | Unlock_accepted ->
      demonitor process;
      Ok ()
  | Failed reason -> Error reason
  | Monitor (Process_down _) -> Error `process_died
  | _ -> Error `invalid_message

let init_state () =
  let read_queue = Lf_queue.create () in
  let write_queue = Lf_queue.create () in
  let status = Unlocked in
  let reader_count = 0 in
  { reader_count; status; write_queue; read_queue }

let clone (inner : 'a) : 'a =
  let open Marshal in
  let ser = to_bytes inner [ Closures; No_sharing ] in
  from_bytes ser 0

(* API *)

let create inner =
  let process = spawn_link @@ fun () -> loop @@ init_state () in
  { inner; process }

let read handle =
  let* _ = wait_lock handle @@ Read (self ()) in
  let inner = clone handle.inner in
  let* _ = unlock handle in
  Ok inner

let try_read handle =
  let* _ = try_wait_lock handle `read in
  let res = clone handle.inner in
  let* _ = unlock handle in
  Ok res

let read_iter handle fn =
  let* _ = wait_lock handle @@ Read (self ()) in
  fn handle.inner;
  unlock handle

let write handle fn =
  let* _ = wait_lock handle @@ Write (self ()) in
  handle.inner <- fn handle.inner;
  unlock handle

let try_write handle fn =
  let* _ = try_wait_lock handle `write in
  handle.inner <- fn handle.inner;
  unlock handle

let write_iter handle fn =
  let* _ = wait_lock handle @@ Write (self ()) in
  fn handle.inner;
  unlock handle

let unsafe_read { inner; _ } = inner
let unsafe_write value handle = handle.inner <- value

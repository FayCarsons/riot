open Global
open Util
open Process.Messages
module Reader_set = Set.Make (Pid)

type internal = {
  mutable reader_count : int;
      (* Track number of readers and keep their PIDs in a set to validate messages *)
  status : state;
  read_queue : Pid.t Lf_queue.t;
  write_queue : Pid.t Lf_queue.t;
}

and state = Reading of Reader_set.t | Writing of Pid.t | Unlocked

type 'a t = { mutable inner : 'a; process : Pid.t }
type error = [ `not_owner | `multiple_unlocks | `locked | `process_died ]

(* Process *)

type Message.t +=
  | Read of Pid.t
  | Locked
  | Lock_accepted
  | Write of Pid.t
  | Unlock of Pid.t
  | Unlock_accepted
  | Failed of error

let rec loop ({ reader_count; status; read_queue; write_queue } as state) =
  match[@warning "-8"] (receive_any (), status) with
  | Read reader, Reading readers ->
      monitor reader;
      send reader Lock_accepted;
      state.reader_count <- succ reader_count;
      let status = Reading (Reader_set.add reader readers) in
      loop { state with status }
  | Read reader, Unlocked ->
      monitor reader;
      send reader Lock_accepted;
      state.reader_count <- succ reader_count;
      let readers = Reader_set.of_list [ reader ] in
      loop { state with status = Reading readers }
  | Read reader, Writing _ ->
      send reader Locked;
      Lf_queue.push read_queue reader;
      loop state
  | Write writer, Unlocked ->
      monitor writer;
      send writer Lock_accepted;
      loop { state with status = Writing writer }
  | Write writer, Reading _ | Write writer, Writing _ ->
      send writer Locked;
      Lf_queue.push write_queue writer;
      loop state
  | Unlock reader, Reading readers ->
      if Reader_set.mem reader readers then (
        send reader Unlock_accepted;
        demonitor reader;
        state.reader_count <- pred reader_count;
        if state.reader_count = 0 then
          check_queues { state with status = Unlocked }
        else
          let status = Reading (Reader_set.remove reader readers) in
          loop { state with status })
      else Logger.error (fun f -> f "RWLock received invalid unlock");
      send reader @@ Failed `not_owner;
      loop state
  | Unlock writer, Writing current when Pid.equal writer current ->
      send writer Unlock_accepted;
      demonitor writer;
      check_queues state
  | Unlock writer, Writing _ ->
      Logger.error (fun f -> f "RWLock received invalid unlock");
      send writer @@ Failed `not_owner;
      loop state
  | Unlock pid, Unlocked ->
      Logger.error (fun f -> f "RWLock received multiple unlocks");
      send pid @@ Failed `multiple_unlocks;
      loop state
  | Monitor (Process_down fell_pid), _ -> (
      match status with
      | Reading readers when Reader_set.mem fell_pid readers ->
          Logger.error (fun f -> f "RWLock: Reader process failed");
          state.reader_count <- pred reader_count;
          loop
            { state with status = Reading (Reader_set.remove fell_pid readers) }
      | Writing writer when Pid.equal writer fell_pid ->
          Logger.error (fun f -> f "RWLock: Writer process failed");
          check_queues state
      | _ ->
          Logger.error (fun f -> f "RWLock failed to demonitor all processes");
          loop state)

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
        let read_set = Reader_set.add reader read_set in
        grant state read_set
    | None -> loop { state with status = Reading read_set }
  in
  grant state (Reader_set.of_list [])

(* API internals *)

let selector = function
  | (Lock_accepted | Unlock_accepted | Failed _ | Monitor (Process_down _)) as
    msg ->
      `select msg
  | _ -> `skip

let wait_lock { process; _ } msg =
  monitor process;
  send process msg;
  match[@warning "-8"] receive ~selector () with
  | Lock_accepted -> Ok ()
  | Failed reason -> Error reason
  | Monitor (Process_down _) -> Error `process_died

let try_wait_lock { process; _ } msg =
  monitor process;
  send process @@ msg;
  match[@warning "-8"] receive_any () with
  | Lock_accepted -> Ok ()
  | Locked -> Error `locked
  | Failed reason -> Error reason
  | Monitor (Process_down _) -> Error `process_died

let unlock { process; _ } =
  send process @@ Unlock (self ());
  match[@warning "-8"] receive ~selector () with
  | Unlock_accepted ->
      demonitor process;
      Ok ()
  | Failed reason -> Error reason
  | Monitor (Process_down _) -> Error `process_died

let init_state () =
  let read_queue = Lf_queue.create () in
  let write_queue = Lf_queue.create () in
  let status = Unlocked in
  let reader_count = 0 in
  { reader_count; status; write_queue; read_queue }

(* API *)

let create inner =
  let process = spawn_link @@ fun () -> loop @@ init_state () in
  { inner; process }

let read handle =
  let* _ = wait_lock handle @@ Read (self ()) in
  let res = Mutex.clone handle.inner in
  let* _ = unlock handle in
  Ok res

let try_read handle =
  let* _ = try_wait_lock handle @@ Read (self ()) in
  let res = Mutex.clone handle.inner in
  let* _ = unlock handle in
  Ok res

let write handle fn =
  let* _ = wait_lock handle @@ Write (self ()) in
  handle.inner <- fn handle.inner;
  unlock handle

let try_write handle fn =
  let* _ = try_wait_lock handle @@ Write (self ()) in
  handle.inner <- fn handle.inner;
  unlock handle

let unsafe_read { inner; _ } = inner
let unsafe_write value handle = handle.inner <- value


type 'a t =
  { mutex : Mutex.t
  ; cell  : 'a ref }

let create default =
  { mutex = Mutex.create ()
  ; cell  = ref default }

let update f { mutex ; cell } =
  Mutex.lock mutex;
  cell := f !cell;
  let x = !cell in
  Mutex.unlock mutex;
  x

let get { cell ; mutex } =
  Mutex.lock mutex;
  let r = !cell in
  Mutex.unlock mutex;
  r
  
module Make (X : Types.T) = struct
  type nonrec t = X.t t
  let create = create
  let update = update
end

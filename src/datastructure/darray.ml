
type 'a darray =
  { mutable data : 'a array;
    mutable size : int;
    mutable free : int list;
            free_ht : (int,bool) Hashtbl.t;
  }

let tabulate f n =
  let rec tab i =
    if i<n then
      (f i)::(tab (i+1))
    else []
  in tab 0

let is_free da i =
  Hashtbl.mem da.free_ht i

let da_next_free da =
  match da.free with
      (n::nr) -> n
    | [] -> Array.length da.data
    
let da_make s e =
  let ht = Hashtbl.create s in
  let fr = tabulate (fun i -> Hashtbl.add ht i true; i) s in
  {
    data = Array.make s e;
    size = 0;
    free = fr;
    free_ht = ht;
  }


let da_insert da e =
  match da.free with
      (n::nr) ->
        da.data.(n) <- e;
        da.free <- List.tl da.free;
        Hashtbl.remove da.free_ht n;
        da.size <- da.size + 1;
        n
    | [] ->
        if Array.length da.data = 0
        then (
          da.data <- [|e|];
          da.free <- tabulate (fun i -> Hashtbl.add da.free_ht (i+1) true; (i+1)) (Array.length da.data -2);
          da.size <- 1;
          0)
        else (
          let newarray = Array.make (2 * da.size) e in
          Array.blit da.data 0 newarray 0 da.size;
          da.data <- newarray;
          da.free <- tabulate (fun i ->
            Hashtbl.add da.free_ht (i + da.size + 1) true;
            i + da.size + 1) (da.size-1);
          da.data.(da.size) <- e;
          da.size <- da.size + 1;
          da.size - 1
          )


let da_remove da i =
  assert(i>=0 && i<Array.length da.data);
  if not (is_free da i) then (
    da.free <- i::da.free;
    Hashtbl.add da.free_ht i true;
    da.size <- da.size - 1)
  
let da_iteri f da =
(*  assert(da.size>0); *)
  for i = 0 to Array.length da.data - 1 do
    if not (Hashtbl.mem da.free_ht i) then
      f i da.data.(i)
  done


let da_copy da = {
  data = Array.copy da.data;
  size = da.size;
  free = da.free;
  free_ht = Hashtbl.copy da.free_ht}
          
let array2da ar = {
  data = ar;
  size = Array.length ar;
  free = [];
  free_ht = Hashtbl.create 0}

let da2array da =
(*  assert(da.size>0); *)
  let result = Array.make da.size da.data.(0) in
  let j = ref 0 in
  for i = 0 to Array.length da.data - 1 do
    if not (Hashtbl.mem da.free_ht i) then
      (result.(!j) <- da.data.(i);
       j := !j + 1)
  done;
  result
  
let da_get da i =
  assert(not (is_free da i));
  da.data.(i)
  
let da_set da i v =
  assert(not (is_free da i));
  da.data.(i) <- v
  
let da_size da =
  da.size


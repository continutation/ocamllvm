(** Pointer type is virtual address, relevant byte store, offset into that bytestore. *)
type pointer = 
  | NullPointer of {off: int}
  | DataPointer of {id: int; bytes: bytes; off: int}
  | FuncPointer of {id: int; func: string * polyfunc}
and polyval = [
  | `Int of BigInt.t
  | `Float of float
  | `Aggregate of polyval list
  | `Pointer of pointer
  | `Void
]
and polyfunc = polyval list -> polyval

(* this *must* match what you're trying to compile. *)
let pointer_size = 4

let rec show_polyval : polyval -> string = function
  | `Int bi -> BigInt.to_string bi
  | `Float x -> Float.to_string x
  | `Aggregate l -> "[" ^ String.concat "; " (List.map show_polyval l) ^ "]"
  | `Pointer (NullPointer {off}) -> "*null" ^ string_of_int off
  | `Pointer (FuncPointer {id; func=_}) -> "*func" ^ string_of_int (-id)
  | `Pointer (DataPointer {id; bytes; off}) ->
    Printf.sprintf "*%d[%d/%d]" id off (Bytes.length bytes)
  | `Void -> "void"

exception Abort

(*
 * Implementations for different sized integer types.
 * Maybe we should specialize the functions for common widths?
 *)

module type IntImpl = sig
  (** Name of the module as it exists here. *)
  val module_name : string

  type t
  val zero : t

  (** For all these functions, the first argument is the bitwidth. *)
  val add : int -> t -> t -> t
  val sub : int -> t -> t -> t
  val mul : int -> t -> t -> t
  val udiv : int -> t -> t -> t
  val sdiv : int -> t -> t -> t
  val urem : int -> t -> t -> t
  val srem : int -> t -> t -> t
  val shl : int -> t -> t -> t
  val lshr : int -> t -> t -> t
  val ashr : int -> t -> t -> t
  val logand : int -> t -> t -> t
  val logor : int -> t -> t -> t
  val logxor : int -> t -> t -> t

  val eq  : int -> t -> t -> bool
  val ne  : int -> t -> t -> bool
  val ugt : int -> t -> t -> bool
  val uge : int -> t -> t -> bool
  val ult : int -> t -> t -> bool
  val ule : int -> t -> t -> bool
  val sgt : int -> t -> t -> bool
  val sge : int -> t -> t -> bool
  val slt : int -> t -> t -> bool
  val sle : int -> t -> t -> bool

  (* The repr functions are more for compile time than runtime, but, it
   * seemed more organized to have them here. *)
  val repr : int -> t -> string
  val repr_bi : int -> BigInt.t -> string
  val of_int : int -> int -> t
  val to_unsigned_int : int -> t -> int
  val to_signed_int : int -> t -> int
  val of_bi : int -> BigInt.t -> t
  val to_bi : int -> t -> BigInt.t
end

module MakeCmp (I : sig
  type t
  val compare : t -> t -> int
  val signed : int -> t -> t
  val unsigned : int -> t -> t
end) = struct
  open I
  let eq  bits x y = compare (unsigned bits x) (unsigned bits y) = 0
  let ne  bits x y = compare (unsigned bits x) (unsigned bits y) <> 0
  let ugt bits x y = compare (unsigned bits x) (unsigned bits y) > 0
  let uge bits x y = compare (unsigned bits x) (unsigned bits y) >= 0
  let ult bits x y = compare (unsigned bits x) (unsigned bits y) < 0
  let ule bits x y = compare (unsigned bits x) (unsigned bits y) <= 0
  let sgt bits x y = compare (signed bits x) (signed bits y) > 0
  let sge bits x y = compare (signed bits x) (signed bits y) >= 0
  let slt bits x y = compare (signed bits x) (signed bits y) < 0
  let sle bits x y = compare (signed bits x) (signed bits y) <= 0
end

module IntBig = struct
  let module_name = "IntBig"
  open BigInt
  type t = BigInt.t
  let zero = zero

  let add _bits = (+)
  let sub _bits = (-)
  let mul bits a b = unsigned bits (a * b)
  let udiv bits a b = unsigned bits a / unsigned bits b

  let sdiv bits a b = signed bits a / signed bits b
  let urem bits a b = modulo (unsigned bits a) (unsigned bits b)
  let srem bits a b =
    let a, b = signed bits a, signed bits b in
    let ret = modulo a b in
    match compare ret zero < 0, compare a zero < 0 with
    | true, true -> ret
    | false, false -> ret
    | true, false -> ret + b
    | false, true -> ret - b

  let shl  bits a b = shift_left a (to_int_exn @@ unsigned bits b)
  let lshr bits a b = shift_right (unsigned bits a) (to_int_exn @@ unsigned bits b)
  let ashr bits a b = shift_right (signed bits a) (to_int_exn @@ unsigned bits b)
  let logand _bits = (land)
  let logor  _bits = (lor)
  let logxor _bits = (lxor)

  include MakeCmp(BigInt)

  let repr bits bi =
    let bi = unsigned bits bi in
    let repr_int x = if x < 0 then "("^string_of_int x^")" else string_of_int x in
    let repr_int64 x = if Int64.compare x 0L < 0 then "("^Int64.to_string x^"L)" else Int64.to_string x^"L" in
    match to_int bi with Some x -> "Big_int.big_int_of_int "^repr_int x | None ->
    match to_int64 bi with Some x -> "Big_int.big_int_of_int64 "^repr_int64 x | None ->
    "Big_int.big_int_of_string \""^BigInt.to_string bi^"\""

  let repr_bi = repr
  let of_int bits x = unsigned bits (of_int x)
  let to_unsigned_int bits x = to_int_exn (unsigned bits x)
  let to_signed_int bits x = to_int_exn (signed bits x)

  let of_bi = unsigned
  let to_bi = unsigned
end

let _ = assert (Sys.int_size >= 31) (* codegen assumes this. *)
module IntShort = struct
  let module_name = "IntShort"
  (* int type, but where number of bits is guarenteed not to be the maximum.
   * That is, the 'unsigned' function will return a positive number. *)
  type t = int
  let zero = 0

  let unsigned bits x =
    ((1 lsl bits) - 1) land x

  let signed bits x =
    if (1 lsl (bits-1)) land x = 0
    then ((1 lsl bits) - 1) land x
    else ((-1) lsl bits) lor x

  let add _bits = (+)
  let sub _bits = (-)
  let mul _bits = ( * )
  let udiv bits a b = unsigned bits a / unsigned bits b

  let sdiv bits a b = signed bits a / signed bits b
  let urem bits a b = unsigned bits a mod unsigned bits b
  let srem bits a b = signed bits a mod signed bits b

  let shl  bits a b = a lsl unsigned bits b
  let lshr bits a b = unsigned bits a lsr unsigned bits b
  let ashr bits a b = signed bits a asr unsigned bits b
  let logand _bits = (land)
  let logor  _bits = (lor)
  let logxor _bits = (lxor)

  include MakeCmp(struct
    type t = int
    let compare x y = x - y (* works cuz ints are short. *)
    let unsigned = unsigned
    let signed = signed
  end)

  let repr bits x = string_of_int @@ unsigned bits x
  let repr_bi bits bi =
    BigInt.to_string @@ BigInt.extract ~low:0 ~len:bits bi
  let of_int _bits x = x
  let to_unsigned_int bits x = unsigned bits x
  let to_signed_int bits x = signed bits x
  let of_bi bits x = BigInt.to_int_exn @@ BigInt.extract ~len:bits x
  let to_bi bits x = BigInt.of_int @@ unsigned bits x
end

module IntInt64 = struct
  let module_name = "IntInt64"
  type t = int64
  let zero = 0L

  let unsigned bits x =
    if bits = 64 then x else
    Int64.pred (Int64.shift_left 1L bits) |> Int64.logand x

  let signed bits x =
    if bits = 64 then x else
    let unwidth = 64 - bits in
    Int64.shift_right (Int64.shift_left x unwidth) unwidth

  let add _bits = Int64.add
  let sub _bits = Int64.sub
  let mul _bits = Int64.mul
  let udiv bits a b =
    if bits < 64 then
      Int64.div (unsigned bits a) (unsigned bits b)
    else
      (*64 bit unsigned division hax*)
      if Int64.compare b 0L < 0 then 0L else
      let t = Int64.shift_left (Int64.div (Int64.shift_right_logical a 1) b) 1 in
      if Int64.compare (Int64.sub a (Int64.mul (Int64.succ t) b)) 0L >= 0 then Int64.succ t else t

  let urem bits a b =
    if bits < 64 then
      Int64.rem (unsigned bits a) (unsigned bits b)
    else
      sub bits a (mul bits (udiv bits a b) b)

  let sdiv bits a b = Int64.div (signed bits a) (signed bits b)
  let srem bits a b = Int64.rem (signed bits a) (signed bits b)

  let shl  bits a b = Int64.shift_left a (Int64.to_int @@ unsigned bits b)
  let lshr bits a b = Int64.shift_right_logical (unsigned bits a) (Int64.to_int @@ unsigned bits b)
  let ashr bits a b = Int64.shift_right (signed bits a) (Int64.to_int @@ unsigned bits b)
  let logand _bits = Int64.logand
  let logor  _bits = Int64.logor
  let logxor _bits = Int64.logxor

  include MakeCmp(struct
    type t = int64
    let compare = Int64.compare
    let unsigned = unsigned
    let signed = signed
  end)

  let repr bits x =
    let t = Int64.to_string (unsigned bits x) ^ "L" in
    if t.[0] = '-' then "("^t^")" else t

  let repr_bi bits bi =
    let x = BigInt.extract ~len:bits bi in
    if BigInt.log2p1 x = 64 then
      "(" ^ BigInt.to_string (BigInt.(-) x @@ BigInt.power_int 2 64) ^ "L)"
    else
      BigInt.to_string x ^ "L"

  let of_int _bits x = Int64.of_int x
  let to_unsigned_int bits x = Int64.to_int @@ unsigned bits x
  let to_signed_int bits x = Int64.to_int @@ signed bits x
  let of_bi bits x = BigInt.to_int64_exn @@ BigInt.extract ~len:bits x
  let to_bi bits x = BigInt.extract ~len:bits @@ BigInt.of_int64 x
end

module IntBool = struct
  let module_name = "IntBool"
  type t = bool
  let zero = false

  let add _bits = (<>)
  let sub _bits = (<>)
  let mul _bits = (&&)
  let udiv _bits a b = if b then a else raise Division_by_zero
  let sdiv _bits a b = if b then a else raise Division_by_zero
  let urem _bits _a b = if b then false else raise Division_by_zero
  let srem _bits _a b = if b then false else raise Division_by_zero

  let shl  _bits a b = if b then false else a
  let lshr _bits a b = if b then false else a
  let ashr _bits a _b = a
  let logand _bits = (&&)
  let logor  _bits = (||)
  let logxor _bits = (<>)

  let eq  _bits a b = a = b
  let ne  _bits a b = a <> b
  let ugt _bits a b = a && not b
  let ult _bits a b = not a && b
  let uge _bits a b = not @@ ult _bits a b
  let ule _bits a b = not @@ ugt _bits a b
  let sgt _bits a b = not a && b
  let slt _bits a b = a && not b
  let sge _bits a b = not @@ slt _bits a b
  let sle _bits a b = not @@ sgt _bits a b

  let repr _bits x = if x then "true" else "false"
  let repr_bi _bits bi = if BigInt.(equal zero) @@ BigInt.extract ~len:1 bi then "false" else "true"
  let of_int _bits x = if x mod 2 = 0 then false else true
  let to_unsigned_int _bits x = if x then 1 else 0
  let to_signed_int _bits x = if x then -1 else 0
  let of_bi _bits x = not @@ BigInt.(equal zero) @@ BigInt.extract ~len:1 x
  let to_bi _bits x = if x then BigInt.one else BigInt.zero
end

(*
 * Implementations for float-to-bits and back.
 *)


let encode_float (ebits, sbits) x =
  (* let sign = Float.sign_bit x in *)
  match Float.classify_float x with
  | FP_zero ->
    let sign = Float.compare (Float.copy_sign 1. x) 0. < 0 in
    if sign then BigInt.power_int 2 (ebits+sbits-1) else BigInt.zero
  | FP_normal | FP_subnormal ->
    let sign = Float.compare x 0. < 0 in
    let frac, pow = Float.frexp @@ Float.abs x in
    let high =
      let bias = (1 lsl (ebits-1))-1 in
      let t = pow + bias + (if sign then 1 lsl ebits else 0) in
      BigInt.shift_left (BigInt.of_int t) (sbits-1)
    in
    let low =
      let s = Float.ldexp frac sbits |> Float.to_string in
      assert (s.[String.length s - 1] = '.');
      let s = String.sub s 0 (String.length s - 1) in
      let t = BigInt.of_string s in
      BigInt.(land) t (BigInt.power_int 2 (sbits - 1) |> BigInt.pred)
    in
    BigInt.(lor) high low
  | FP_infinite ->
    let sign = Float.compare x 0. < 0 in
    let t = if sign then ebits+1 else ebits in
    BigInt.shift_left
      (BigInt.power_int 2 t |> BigInt.pred)
      (sbits-1)
  | FP_nan ->
    BigInt.shift_left
      (BigInt.power_int 2 (ebits+1) |> BigInt.pred)
      (sbits-2)

let encode_float_x87 x =
  let implicit =
    match Float.classify_float x with
    | FP_zero | FP_subnormal -> BigInt.zero
    | FP_normal | FP_infinite | FP_nan -> BigInt.power_int 2 63
  in
  let ieee = encode_float (15, 64) x in
  let high = BigInt.shift_left (BigInt.shift_right ieee 63) 64 in
  let low = BigInt.(land) ieee (BigInt.power_int 2 63 |> BigInt.pred) in
  BigInt.(lor) implicit @@ BigInt.(lor) high low

let decode_float (ebits, sbits) x =
  let sign = BigInt.shift_right x (ebits + sbits - 1) in
  let exp = BigInt.(land) (BigInt.power_int 2 ebits |> BigInt.pred) @@ BigInt.shift_right x (sbits-1) in
  let exp = BigInt.to_int_exn exp in
  let bias = (1 lsl (ebits-1))-1 in
  let frac = BigInt.(land) (BigInt.power_int 2 (sbits-1) |> BigInt.pred) x in
  let tofloat bi = Float.ldexp (BigInt.to_float bi) (-sbits) in
  let t =
    if exp = 0 then
      Float.ldexp (tofloat frac) (1 - bias)
    else if exp+1 = 1 lsl ebits then
      if BigInt.(equal zero) frac then Float.infinity else Float.nan
    else
      Float.ldexp (tofloat @@ BigInt.(lor) frac @@ BigInt.power_int 2 (sbits-1)) (exp - bias)
  in
  if BigInt.(equal zero) sign then t else Float.neg t

let decode_float_x87 x =
  (* just ignore the implicit bit. *)
  let high = BigInt.shift_left (BigInt.shift_right x 64) 63 in
  let low = BigInt.(land) x (BigInt.power_int 2 63 |> BigInt.pred) in
  decode_float (15,64) @@ BigInt.(lor) high low


(*
 * Pointers.
 * All pointers must be created with alloc (or alloc_bytes)
 *)

let null_pointer = NullPointer {off=0}

let alloc_physical_counter = ref 4096
let alloc_virtual_counter = ref (-256)

(** bytes must not have previously been alloced. *)
let alloc_bytes bytes : pointer =
  let id = !alloc_physical_counter in
  alloc_physical_counter := id + Bytes.length bytes;
  DataPointer {id; bytes; off=0}

let alloc nbytes : pointer =
  alloc_bytes (Bytes.create nbytes)

let alloc_id () =
  let id = !alloc_virtual_counter in
  alloc_virtual_counter := id - 1;
  id

let compare_pointer a b =
  match a, b with
  | NullPointer {off=offa}, NullPointer {off=offb} -> compare offa offb
  | NullPointer _, _ -> -1
  | _, NullPointer _ -> 1
  | _, _ ->
  let get_id = function
    | NullPointer {off} -> off
    | DataPointer {id; bytes=_; off} -> id + off
    | FuncPointer {id; func=_} -> id
  in
  compare (get_id a) (get_id b)

let pointer_offset ptr offset =
  match ptr with
  | DataPointer {id; bytes; off} -> DataPointer {id; bytes; off=off+offset}
  | NullPointer {off} -> NullPointer {off=off+offset}
  | _ -> assert false

(* Pointer to int and back isn't perfect in a variety of
 * ways, but, should work for now. *)

module IntMap = Map.Make(struct
  type t = int
  let compare = (compare : int -> int -> int)
end)
let inttoptr_table : pointer IntMap.t ref = ref IntMap.empty

let ptrtoint = function
  | NullPointer {off} -> off
  | DataPointer {id; bytes; off} ->
    inttoptr_table := IntMap.add id (DataPointer {id; bytes; off=0}) !inttoptr_table;
    id + off
  | FuncPointer {id; func=_} as ptr ->
    inttoptr_table := IntMap.add id ptr !inttoptr_table;
    id

let inttoptr id =
  let less, x, _more = IntMap.split id !inttoptr_table in
  match x with Some ptr -> ptr | None ->
  if id < 0 then NullPointer {off=id} else
  match IntMap.max_binding_opt less with
  | None ->
    Printf.eprintf "producing nullptr %d from inttoptr\n%!" id;
    NullPointer {off=id}
  | Some (k, v) ->
    if k <= 0 then NullPointer {off=id} else
    let offset = id - k in
    match v with
    | DataPointer {id; bytes; off} -> DataPointer {id; bytes; off=off+offset}
    | _ -> assert false (* should actually be impossible since only DataPointers have positive ids. *)

(* We're not really using this "dealloc" right now; we'd need to call it
 * as stack vars go out of scope to be sure that bytes will get GCed. *)
let dealloc = function
  | NullPointer {off=_} -> ()
  | DataPointer {id; bytes=_; off=_} ->
    inttoptr_table := IntMap.remove id !inttoptr_table
  | FuncPointer {id; func=_} ->
    inttoptr_table := IntMap.remove id !inttoptr_table

let funptr_register name func =
  let id = alloc_id () in
  FuncPointer {id; func=(name, func)}

let call_ptr : pointer -> polyfunc = function
  | FuncPointer {id=_; func=(_, f)} -> f
  | _ -> (fun _ -> assert false)

let load_bits ptr nbytes =
  try match ptr with
  | DataPointer {id=_; bytes; off} ->
    let acc = ref BigInt.zero in
    for i = 0 to nbytes - 1 do
      acc := BigInt.(lor) (!acc) @@ BigInt.shift_left_int (int_of_char @@ Bytes.get bytes (off+i)) (i*8)
    done;
    !acc
  | _ ->
    failwith ("Load from non-data " ^ show_polyval (`Pointer ptr))
  with e ->
    Printf.eprintf "error loading %d bytes from %s\n%!" nbytes @@ show_polyval (`Pointer ptr);
    raise e

let store_bits ptr nbytes bits =
  try match ptr with
  | DataPointer {id=_; bytes; off} ->
    for i = 0 to nbytes - 1 do
      Bytes.set bytes (off+i) (BigInt.extract ~low:(i*8) ~len:8 bits |> BigInt.to_int_exn |> char_of_int)
    done
  | _ ->
    failwith ("Store to non-data " ^ show_polyval (`Pointer ptr))
  with e ->
    Printf.eprintf "error storing %d bytes from %s\n%!" nbytes @@ show_polyval (`Pointer ptr);
    raise e

let bytes_of_bits nbytes bits =
  Bytes.init nbytes (fun i -> BigInt.extract ~low:(i*8) ~len:8 bits |> BigInt.to_int_exn |> char_of_int)

let alloc_bits nbytes bits =
  alloc_bytes @@ bytes_of_bits nbytes bits

let encode_pointer ptr =
  BigInt.unsigned 32 @@ BigInt.of_int @@ ptrtoint ptr

let decode_pointer bi =
  inttoptr @@ BigInt.to_int_exn @@ BigInt.signed 32 bi

let va_table : (int, polyval list) Hashtbl.t = Hashtbl.create 0
let va_id = ref 0

let va_start (ptr : pointer) (varargs : polyval list) =
  va_id := 1 + !va_id;
  Hashtbl.add va_table !va_id varargs;
  store_bits ptr pointer_size (BigInt.of_int !va_id)

let va_end (ptr : pointer) =
  let id = load_bits ptr pointer_size |> BigInt.to_int_exn in
  Hashtbl.remove va_table id

let va_arg ptr =
  let id = load_bits ptr pointer_size |> BigInt.to_int_exn in
  match Hashtbl.find va_table id with
  | hd::tl -> Hashtbl.replace va_table id tl; hd
  | [] -> failwith "va_arg called when no more args left"

let va_copy dst src =
  let id = load_bits src pointer_size |> BigInt.to_int_exn in
  va_id := 1 + !va_id;
  Hashtbl.add va_table !va_id @@ Hashtbl.find va_table id;
  store_bits dst pointer_size (BigInt.of_int !va_id)

let chararray_to_string arr off len =
  String.init len (fun i -> match arr.(off+i) with `Int c -> Int64.to_int c land 0xff |> char_of_int | _ -> failwith "Bad type in chararray_to_string")

let cstring_to_string = function
  | DataPointer {id=_; bytes; off} ->
    let rec f i =
      if i >= Bytes.length bytes then None
      else match Bytes.get bytes i with
      | '\000' -> Some i
      | _ -> f (i+1)
    in
    begin match f off with
    | None -> failwith "cstring is not null terminated!"
    | Some endoff -> Bytes.sub_string bytes off (endoff-off)
    end
  | _ -> failwith "Bad pointer type for cstring"

let chararray_of_string s =
  Array.init (String.length s) (fun i -> `Int (int_of_char s.[i] |> Int64.of_int))

let cstring_of_string s =
  let len = match String.index_opt s '\x00' with
    | None -> String.length s + 1
    | Some i -> i + 1
  in
  Bytes.init len (fun i -> try s.[i] with Invalid_argument _ -> '\x00')

(* TODO: we need runtime type information about dst and src to properly set them; this here is wrong when pointer-casting has happened. *)
let llvm_memmove dst dstw src srcw len _isvol =
  ignore dst; ignore dstw; ignore src; ignore srcw; ignore len

let llvm_memcpy = llvm_memmove

(* TODO: we need runtime type information about dst in order to properly set it. This here is wrong if dst has been pointer-casted. *)
let llvm_memset dst dstw byte len _isvol =
  ignore dst; ignore dstw; ignore byte; ignore len

let llvm_objectsize obj _obj_ty min nullunk dyn =
  let unkval = if min then Int64.minus_one else 0L in
  if not dyn then unkval else
  if obj == null_pointer then (if nullunk then unkval else 0L) else
  unkval (* Dummy always-unknown implementation *)

let start_main f exit =
  let len = Array.length Sys.argv in
  let argv = alloc (pointer_size * (len+1)) in
  for i = 0 to (len-1) do
    store_bits (pointer_offset argv (i*pointer_size)) pointer_size @@ encode_pointer @@ alloc_bytes @@ cstring_of_string Sys.argv.(i)
  done;
  store_bits (pointer_offset argv (len*pointer_size)) pointer_size @@ encode_pointer null_pointer;
  f (Int64.of_int len) argv |> exit

let exit = exit

(** Run the given ctors array. *)
let run_ctors ctors len =
  match ctors with `Pointer (arr, off) ->
    let fs = Array.init len (fun i ->
      let prio,f = match arr.(off+3*i+0), arr.(off+3*i+1), arr.(off+3*i+2) with
        | `Int prio, `Pointer (ptr, ptri), _ -> Int64.logand 0xFFFFFFFFL prio, ptr.(ptri)
        | _ -> failwith "Bad type for ctors list"
      in
      match f with
      | `Function f -> prio, f
      | _ -> failwith "Bad type for ctors list"
    ) in
    Array.sort (fun (i, _) (j, _) -> Int64.compare i j) fs;
    Array.iter (fun (_, f) -> f [] |> ignore) fs
  | _ -> assert false

(** Run the given dtors array. *)
let run_dtors = run_ctors

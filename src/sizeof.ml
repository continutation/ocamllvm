(* Should probably be calling data_layout to figure out the right size and alignment values.
 * If this doesn't match the target code, it will all break. *)

open Llvm

let pointer_size = Runtime.pointer_size

(* Return the index of the highest bit plus one (or, 0 for 0). Only for positive numbers. *)
let num_bits x =
  Big_int.(num_bits_big_int @@ big_int_of_int x)

let rec alignof llty =
  match classify_type llty with
  | Void -> 1

  | Integer | Pointer | Half | Float | Double | X86fp80 | Fp128 | Ppc_fp128 | X86_mmx ->
    let size = sizeof llty in
    min 16 (1 lsl (num_bits size - 1))

  | Label | Function | Metadata | Token -> failwith "nonphysical type"
  | Struct ->
    (* I think aligns are defined to be powers of two, so, 'max' is valid here. *)
    Array.fold_left (fun acc ty -> max acc @@ alignof ty) 1 @@ struct_element_types llty
  | Array -> alignof (element_type llty)
  | Vector ->
    let size = sizeof llty in
    min 16 (1 lsl (num_bits size - 1))

and pad llty off =
  let align = alignof llty in
  match off mod align with 0 -> 0 | x -> align - x

and sizeof llty =
  match classify_type llty with
  | Void -> 0
  | Integer ->
    let bytes = (integer_bitwidth llty + 7) / 8 in
    begin match bytes with
    | 0|1 -> 1
    | 2 -> 2
    | 3|4 -> 4
    | 5|6|7|8 -> 8
    | 9|10|11|12 -> 12
    | 13|14|15|16 -> 16
    | x -> ((x+7)/8)*8
    end
  | Pointer -> pointer_size
  | Half -> 2
  | Float -> 4
  | Double -> 8
  | X86fp80 -> 12
  | Fp128 -> 16
  | Ppc_fp128 -> 16
  | X86_mmx -> 8
  | Label | Function | Metadata | Token -> failwith "nonphysical type"
  | Struct ->
    let pad = if is_packed llty then (fun _ _ -> 0) else pad in
    let acc = Array.fold_left (fun acc ty -> acc + pad ty acc + sizeof ty) 0 @@ struct_element_types llty in
    acc + pad llty acc
  | Array  ->
    (* NB: by definition sizes are already padded out to their alignment. *)
    sizeof (element_type llty) * array_length llty
  | Vector ->
    sizeof (element_type llty) * vector_size llty

let struct_layout llty : (int * lltype) array =
  let eltys = struct_element_types llty in
  let pad = if is_packed llty then (fun _ _ -> 0) else pad in
  let out = Array.map (fun ty -> 0, ty) eltys in
  let off = ref 0 in
  for i = 0 to Array.length out - 1 do
    let _, ty = out.(i) in
    off := !off + pad ty !off;
    out.(i) <- !off, ty;
    off := !off + sizeof ty
  done;
  assert (sizeof llty = !off + pad llty !off);
  out

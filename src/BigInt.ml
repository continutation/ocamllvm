open Big_int
type t = big_int
let compare = compare_big_int
let equal = eq_big_int
let zero = zero_big_int
let one = unit_big_int
let minus_one = minus_big_int unit_big_int
let to_int32 = int32_of_big_int_opt
let of_int32 = big_int_of_int32
let to_int64 = int64_of_big_int_opt
let of_int64 = big_int_of_int64
let to_int = int_of_big_int_opt
let of_int = big_int_of_int
let to_int_exn x = match to_int x with Some y -> y | None -> failwith "BigInt.to_int_exn: out of range"
let to_int64_exn x = match to_int64 x with Some y -> y | None -> failwith "BigInt.to_int64_exn: out of range"
let to_string = string_of_big_int
let of_string = big_int_of_string
let to_float = float_of_big_int
let (land) = and_big_int
let (lor) = or_big_int
let (lxor) = xor_big_int
let shift_left = shift_left_big_int
let shift_left_int x y = shift_left (of_int x) y
let shift_right = shift_right_big_int
let power = power_big_int_positive_int
let power_int = power_int_positive_int
let log2p1 = num_bits_big_int
let (+) = add_big_int
let (-) = sub_big_int
let ( * ) = mult_big_int
let ( / ) = div_big_int
let neg = minus_big_int
let pred = pred_big_int
let succ = succ_big_int
let extract ?(low=0) ~len bi = extract_big_int bi low len
let modulo = mod_big_int

let unsigned bits x =
  extract ~len:bits x

let signed bits x =
  let x = extract ~len:bits x in
  let sign = extract ~low:(Stdlib.(-) bits 1) ~len:1 x in
  if equal sign zero then x
  else x - (power_int 2 bits)

let repr x =
  let repr_int x = if x < 0 then "("^string_of_int x^")" else string_of_int x in
  let repr_int64 x = if Int64.compare x 0L < 0 then "("^Int64.to_string x^"L)" else Int64.to_string x^"L" in
  match to_int x with Some x -> "BigInt.of_int "^repr_int x | None ->
  match to_int64 x with Some x -> "BigInt.of_int64 "^repr_int64 x | None ->
  "BigInt.of_string \""^to_string x^"\""

(* We also currently use BigInt as a bit-store; these help with that. *)

let blit_to_bytes ~src ?(src_off=0) ~dst ~dst_off ~len =
  let (+), (-), ( * ) = Stdlib.((+), (-), ( * )) in
  for i = 0 to len - 1 do
    Bytes.set dst (dst_off+i) @@ char_of_int @@ to_int_exn @@ extract ~low:((src_off+i)*8) ~len:8 src
  done

let to_bytes src ?off len =
  let dst = Bytes.create len in
  blit_to_bytes ~src ?src_off:off ~len ~dst ~dst_off:0;
  dst

let of_bytes src src_off len =
  let (+), ( * ) = Stdlib.((+), ( * )) in
  let rec f x i =
    if i >= len then x else
    let t = shift_left (of_int @@ int_of_char @@ Bytes.get src (src_off+i)) (i*8) in
    f (x lor t) i
  in f zero 0

let _15 = of_int 15

let rec to_string' bi =
  let (+), (-), ( * ), (/) = Stdlib.((+), (-), ( * ), (/)) in
  let bytes = (num_bits_big_int bi + 7) / 8 in
  if bytes <= 2 then to_string bi else
  if sign_big_int bi = -1 then "-" ^ to_string' (neg bi) else
  let nibbles = 2*bytes in
  String.init (2+nibbles) (function
    | 0 -> '0'
    | 1 -> 'x'
    | i ->
      let nibble = nibbles - 1 - (i - 2) in
      match int_of_big_int (shift_right bi (4*nibble) land _15) with
      | 0 -> '0' | 1 -> '1' | 2 -> '2' | 3 -> '3' | 4 -> '4' | 5 -> '5' | 6 -> '6' | 7 -> '7'
      | 8 -> '8' | 9 -> '9' | 10 -> 'a' | 11 -> 'b' | 12 -> 'c' | 13 -> 'd' | 14 -> 'e' | 15 -> 'f'
      | _ -> assert false
  )

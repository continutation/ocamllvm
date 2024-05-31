open Llvm
open MyLlvm

(* Our model of values. Ideally we could tinker with runtime representations
 * here (and in Runtime.ml) without affecting the rest of code. *)

let index_type = integer_type (global_context ()) 30

module Private = struct
  (* Helper function, indicates that "s" is a source-string with no side-effects
   * and that doesn't need parens surrounding it in any context. *)
  let is_atom s =
    let rec is_ident i =
      if i >= String.length s then true
      else match s.[i] with
      | '0'..'9' | 'A'..'Z' | 'a'..'z' | '_' | '\'' | '.' -> is_ident (i+1)
      | _ -> false
    in
    is_ident 0

  (* Surround the source-string s in parens, unless it's unnecessary
   * (a simple ident path, or already surrounded in parens).
   * This doesn't work in general, just for our "Source strings" (see below) *)
  let parens s =
    let is_string s =
      (* We're okay with the deficiencies of this function, it'll just
       * cause us to over-parenthesize strings containing escaped quotes. *)
      s.[0] = '"' && String.index_from_opt s 1 '"' = Some (String.length s - 1)
    in
    (* Note that by construction, the "s.[0] = '('" check is fine
     * because leading-paren implies surrouding parens. *)
    if s.[0] = '(' || is_atom s || s.[0] = '[' || is_string s
      then s
      else "(" ^ s ^ ")"

  (* Removes surrounding parens from source-string s, if applicable.
   * Note that it's not safe to call more than once, due to the "((f)(x))" case.
   * This is for when writing a source string to an "already-parenthesized"
   * context, like arr.(here) *)
  let unparens s =
    if s.[0] = '('
    then ( assert (s.[String.length s - 1] = ')'); String.sub s 1 (String.length s - 2) )
    else s

  (** Create a (let <sname> = <s> in <f sname>) string, except that
    * if <s> was a simple atom then just abbreviate to <f s>. *)
  let bindname ?(sname="t") s f =
    if is_atom s then f s
    else "(let " ^ sname ^ " = " ^ unparens s ^ " in " ^ unparens (f sname) ^ ")"

  let bindname2 ?(snames=("x","y")) s1 s2 f =
    match is_atom s1, is_atom s2 with
    | true, true -> f (s1, s2)
    | _ -> "(let " ^ fst snames ^ " = " ^ unparens s1 ^ " and " ^ snd snames ^ " = " ^ unparens s2 ^ " in " ^ unparens (f snames) ^ ")"

  (* Select which runtime module to use. This depends on the target, but,
   * we assume Sys.int_size >= 31 which should be pretty general. *)
  let[@ocaml.inline] int_module width =
    if width = 1 then (module Runtime.IntBool : Runtime.IntImpl)
    else if width <= 30 then (module Runtime.IntShort : Runtime.IntImpl)
    else if width <= 64 then (module Runtime.IntInt64 : Runtime.IntImpl)
    else (module Runtime.IntBig : Runtime.IntImpl)

  let[@ocaml.inline] int_modcall width func =
    let module I = (val int_module width) in "R."^I.module_name^"."^func^" "^string_of_int width^" "
end

open Private

(* Invariants about source strings:
 * 1. Can use them wherever a function call could be placed; that is,
 *    it gets surrounded in parens unless it's a function call or simpler.
 *    So, a top-level binary operator must be surrounded in parens.
 * 2. If it starts with a paren, this must imply that the whole string
 *    is parenthesied. So, no "(f) (x)"; this would need a leading space
 *    or surrounding parens.
 *)

(* Typically holds a source string that computes the desired value
 * at runtime; however, if the value is a compile-time constant we
 * just hold the constant. *)
type value =
  | Source of string
  | Integer of BigInt.t
  | Float of float
  | List of value list
  | Void
  | NullPointer

(* the value type is "polymorphic" in that, in the target source,
 * it may have one of a number of actual types. The following represent
 * source strings (or compile time values, if constant) that have a strict
 * ocaml type. *)

type intvalue =
  | ConstInt of int
  | SourceInt of string

let int_source = function SourceInt s -> s | ConstInt i -> string_of_int i

(* type charvalue =
  | ConstChar of char
  | SourceChar of string

let char_source = function SourceChar s -> s | ConstChar c -> Printf.sprintf "%C" c *)

type boolvalue =
  | ConstBool of bool
  | SourceBool of string

let bool_source = function SourceBool s -> s | ConstBool b -> if b then "true" else "false"

type bitsvalue =
  | ConstBits of BigInt.t
  | SourceBits of string

let bits_source = function SourceBits s -> s | ConstBits bi ->
  match Big_int.num_bits_big_int bi with
  | 0 -> "BigInt.zero"
  | x when x < 30 -> "BigInt.of_int " ^ parens (BigInt.to_string bi)
  | _ -> Printf.sprintf "BigInt.of_string %S" @@ BigInt.to_string' bi

let void_source _ = "()"

let rec typename_for llty =
  match classify_type llty with
  | Integer ->
    let width = integer_bitwidth llty in
    let module I = (val int_module width) in
    "R." ^ I.module_name ^ ".t"
  | Void -> "unit"
  | Half | Float | Double | X86fp80 | Fp128 | Ppc_fp128 -> "float"
  | Function ->
    let params =
      Array.fold_right (fun ty acc -> parens (typename_for ty) :: acc)
        (param_types llty)
        (if is_var_arg llty then ["vararg list"] else [])
    in
    let params =
      match params with [] -> ["unit"] | x -> x
    in
    String.concat " -> " params ^ " -> " ^ typename_for (return_type llty)
  | Struct | Array | Vector ->
    fold_flat_subtypes ~f:(fun acc ty -> parens (typename_for ty) :: acc) ~init:[] llty
    |> List.rev
    |> String.concat " * "
    |> (function "" -> "unit" | x -> x)
  | Pointer -> "R.pointer"
  | X86_mmx -> failwith "X86_mmx unsupported"
  | Label | Metadata | Token -> failwith "nonphysical type"

(* let rec rttval_for llty =
  match classify_type llty with
  | Integer ->
    "`Int " ^ string_of_int (integer_bitwidth llty)
  | Void -> "`Void"
  | Half -> "`Half"
  | Float -> "`Float"
  | Double -> "`Double"
  | X86fp80 -> "`X86fp80"
  | Fp128 -> "`Fp128"
  | Ppc_fp128 -> "`Ppc_fp128"
  | Function ->
    let params =
      Array.fold_right (fun ty acc -> rttval_for ty :: acc)
        (param_types llty)
        (if is_var_arg llty then ["`VAList"] else [])
    in
    "`Function ([" ^ String.concat "; " params ^ "], " ^ rttval_for (return_type llty) ^ ")"
  | Struct ->
    let elts =
      Array.fold_right (fun ty acc -> rttval_for ty :: acc)
        (struct_element_types llty)
        []
    in
    "`Struct [" ^ String.concat "; " elts ^ "]"
  | Array  -> "`Array (" ^ array_length llty ^ ", " ^ rttval_for (element_type llty) ^ ")"
  | Vector -> "`Vector (" ^ vector_size llty ^ ", " ^ rttval_for (element_type llty) ^ ")"
  | Pointer -> "`Pointer " ^ parens (rttval_for @@ element_type llty)
  | X86_mmx -> failwith "X86_mmx unsupported"
  | Label | Metadata | Token -> failwith "nonphysical type" *)

let rec polyval_pattern ty var =
  match classify_type ty with
  | Integer -> "`Int " ^ var, int_modcall (integer_bitwidth ty) "of_bi" ^ var
  | Half | Float | Double | X86fp80 | Fp128 | Ppc_fp128 -> "`Float " ^ var, var
  | Struct | Array | Vector ->
    let _, pats, args =
      let f (i, pats, args) ty =
        let name = var ^ "_" ^ string_of_int i in
        let pat, arg = polyval_pattern ty name in
        i+1, pat::pats, arg::args
      in fold_flat_subtypes ~f ~init:(0, [], []) ty
    in
    "`Aggregate [" ^ String.concat "; " pats ^ "]",
    "(" ^ String.concat "," args ^ ")"
  | Pointer -> "`Pointer " ^ var, var
  | Void -> "`Void", "()"
  | X86_mmx -> failwith "X86_mmx unsupported"
  | Function | Label | Metadata | Token -> failwith "nonphysical type"

(* Emit source representing the value. *)
let rec to_source llty = function
  | Source s -> s
  | Integer bi ->
    assert (classify_type llty = Integer);
    let width = integer_bitwidth llty in
    let module I = (val int_module width) in I.repr_bi width bi
  | Void -> void_source ()
  | NullPointer -> "R.null_pointer"
  | Float x ->
    Float.to_string x
  | List l ->
    let acc = to_source_aggregate [] llty (List l) in
    if List.exists (function `Elt _ -> false | `Bind (_, _) -> true) acc then
      let len, acc = List.fold_left (fun (i, acc) x ->
        match x with
        | `Elt s -> i+1, ("t" ^ string_of_int i ^ " = " ^ s) :: acc
        | `Bind (n, s) -> i+n,
          let ts = String.concat "," @@ List.init n (fun i -> "t" ^ string_of_int (n+i)) in
          (ts ^ " = " ^ s) :: acc
      ) (0, []) acc
      in
      "(let " ^ String.concat " and " acc ^ " in " ^ String.concat "," (List.init len (fun i -> "t" ^ string_of_int i)) ^ ")"
    else
      "(" ^ String.concat ", " (List.rev_map (function `Elt s -> s | `Bind (_, _) -> assert false) acc) ^ ")"
and to_source_aggregate acc llty value =
  match classify_type llty, value with
  | Struct, List l ->
    let eltys = struct_element_types llty in
    let _, acc = List.fold_left (fun (i, acc) x -> i+1, to_source_aggregate acc eltys.(i) x) (0, acc) l in
    acc
  | (Array | Vector), List l ->
    let elty = element_type llty in
    List.fold_left (fun acc x -> to_source_aggregate acc elty x) acc l
  | _, List _ -> assert false
  | (Struct | Array | Vector), Source s ->
    let agg_len = aggregate_length llty in
    begin match is_atom s, agg_len with
    | true, 0 -> acc
    | true, 1 -> `Elt s :: acc
    | true, 2 -> `Elt ("snd "^s) :: `Elt ("fst "^s) :: acc
    | _ ->
      let components = unparens s |> String.split_on_char ',' in
      if List.for_all (fun s -> is_atom s) components
      then List.fold_left (fun acc x -> `Elt x :: acc) acc components
      else `Bind (agg_len, s) :: acc
    end
  | (Struct|Array|Vector), _ -> assert false
  | Void, Void -> acc
  | _, x -> `Elt (to_source llty x) :: acc

let to_polysource (llty, value) =
  match classify_type llty with
  | Integer ->
    begin match value with
    | Source s -> "`Int (" ^ int_modcall (integer_bitwidth llty) "to_bi" ^ parens s ^ ")"
    | Integer bi -> "`Int (" ^ Runtime.IntBig.repr (integer_bitwidth llty) bi ^ ")"
    | _ -> assert false
    end
  | Half | Float | Double | X86fp80 | Fp128 | Ppc_fp128 ->
    "`Float " ^ parens (to_source llty value)
  | Struct | Array | Vector ->
    let ts = List.init (aggregate_length llty) (fun i -> "t" ^ string_of_int i) in
    "(let " ^ String.concat "," ts ^ " = " ^ to_source llty value
    ^ " in `Aggregate [" ^ String.concat ";" ts ^ "])"
  | Pointer -> "`Pointer " ^ parens (to_source llty value)
  | Void -> "(" ^ unparens (to_source llty value) ^ "; `Void)"
  | X86_mmx -> failwith "X86_mmx unsupported"
  | Function | Label | Metadata | Token -> failwith "nonphysical type"

let make_polyfunc llty funcname =
  assert (classify_type llty = Function);
  let params, args = [], [] in
  let types = param_types llty in
  let _, params, args =
    Array.fold_right (fun ty (i, params, args) ->
      let param, arg = polyval_pattern ty ("a" ^ string_of_int i)
      in (i - 1, param :: params, parens arg :: args)
    ) types (Array.length types - 1, params, args)
  in
  let args = match args with [] -> ["()"] | x -> x in
  if is_var_arg llty then
    "(function " ^ String.concat "::" params ^ "::varargs -> "
    ^ to_polysource (return_type llty, Source (parens funcname ^ " " ^ String.concat " " args ^ " varargs"))
    ^ " | _ -> assert false : R.polyfunc)"
  else
    "(function [" ^ String.concat "; " params ^ "] -> "
    ^ to_polysource (return_type llty, Source (parens funcname ^ " " ^ String.concat " " args))
    ^ " | _ -> assert false : R.polyfunc)"

(* Try to return a compile-time int for the value, otherwise return
 * a source string that will result in a runtime int.
 * Typically used for array accesses, so, the signedness of the
 * value is not important. *)
let to_unsigned_int = function
  | llty, Source s ->
    assert (classify_type llty = Integer);
    SourceInt (int_modcall (integer_bitwidth llty) "to_unsigned_int" ^ parens s)
  | llty, Integer bi ->
    assert (classify_type llty = Integer);
    ConstInt (BigInt.to_int_exn @@ BigInt.unsigned (integer_bitwidth llty) bi)
  | _ -> assert false

let to_unsigned_int_s x = to_unsigned_int x |> int_source

let to_signed_int = function
  | llty, Source s ->
    assert (classify_type llty = Integer);
    SourceInt (int_modcall (integer_bitwidth llty) "to_signed_int" ^ parens s)
  | llty, Integer bi ->
    assert (classify_type llty = Integer);
    ConstInt (BigInt.to_int_exn @@ BigInt.signed (integer_bitwidth llty) bi)
  | _ -> assert false

let to_signed_int_s x = to_signed_int x |> int_source

let of_int llty = function
  | ConstInt x -> Integer (BigInt.of_int x)
  | SourceInt s ->
    assert (classify_type llty = Integer);
    Source (int_modcall (integer_bitwidth llty) "of_int" ^ parens s)

let to_bool llty = function
  | Source s ->
    assert (classify_type llty = Integer);
    assert (integer_bitwidth llty = 1);
    SourceBool s (* depends on the fact that i1 is implemented as bool. *)
  | Integer bi ->
    assert (classify_type llty = Integer);
    assert (integer_bitwidth llty = 1);
    ConstBool (not @@ BigInt.(equal zero) bi)
  | _ -> assert false

let to_bool_s llty x = to_bool llty x |> bool_source

let shift_left value bits =
  match value with
  | ConstBits bi -> ConstBits (BigInt.shift_left bi bits)
  | SourceBits s -> SourceBits ("Big_int.shift_left_big_int "^parens s^" "^string_of_int bits)

(* Encode the value to bits. *)
let rec encode_value llty = function
  | NullPointer | Void -> ConstBits BigInt.zero
  | Integer bi ->
    assert (classify_type llty = Integer);
    ConstBits (BigInt.unsigned (integer_bitwidth llty) bi)
  | Float f ->
    ConstBits (match classify_type llty with
      | Half ->    Runtime.encode_float (5,11) f
      | Float ->   Runtime.encode_float (8,24) f
      | Double ->  Runtime.encode_float (11,53) f
      | X86fp80 -> Runtime.encode_float_x87 f
      | Fp128 ->   Runtime.encode_float (15,113) f
      | Ppc_fp128 -> failwith "NYI Ppc_fp128 to memory"
      | _ -> assert false
    )
  | Source s ->
    SourceBits (match classify_type llty with
      | Integer ->
        int_modcall (integer_bitwidth llty) "to_bi" ^ parens s
      | Half ->    "R.encode_float (5,11) " ^ parens s
      | Float ->   "R.encode_float (8,24) " ^ parens s
      | Double ->  "R.encode_float (11,53) " ^ parens s
      | X86fp80 -> "R.encode_float_x87 " ^ parens s
      | Fp128 ->   "R.encode_float (15,113) " ^ parens s
      | Ppc_fp128 -> failwith "NYI Ppc_fp128 to memory"
      | Struct ->
        (* TODO: broken? still uses array indexing. Also, should use Sizeof.struct_layout.
         * Also, temporary naming is broken, what if sname="t"? *)
        let alignof = if is_packed llty then (fun _ -> 1) else Sizeof.alignof in
        bindname ~sname:"st" s (fun sname ->
          let _, bytes, l = Array.fold_left (fun (idx, bytes, l) ty ->
              let align = alignof ty in
              let bytes = if bytes mod align = 0 then bytes else bytes + align - (bytes mod align) in
              let t = "let t = Big_int.or_big_int t @@ Big_int.shift_left_big_int "
                ^ parens (encode_value_s ty @@ Source (sname^".("^string_of_int idx^")"))
                ^ " " ^ string_of_int (bytes*8) ^ "in"
              in
              idx+1, bytes + Sizeof.sizeof ty, t::l
            ) (0, 0, ["let t = Big_int.zero_big_int in"]) @@ struct_element_types llty
          in
          assert (bytes = Sizeof.sizeof llty);
          "(" ^ String.concat "\n" (List.rev ("t"::l)) ^ ")"
        )
      | Array | Vector ->
        let ts = List.init (vector_size llty) (fun i -> "t" ^ string_of_int i) in
        Printf.sprintf
          "(let f el (i, b) = i+8*%d, Big_int.or_big_int b @@ Big_int.shift_left_big_int %s i"
            (Sizeof.sizeof @@ element_type llty)
            (parens @@ encode_value_s (element_type llty) (Source "el"))
          ^ " and " ^ String.concat "," ts ^ " = " ^ unparens s
          ^ " in (0, Big_int.zero_big_int) |> " ^ String.concat "|>" (List.map (fun t -> "f "^t) ts) ^ " |> snd)"
      | Pointer -> "R.encode_pointer " ^ parens s
      | tk -> (failwith "Unsupported encode type "^string_of_typekind tk)
    )
  | List l ->
    let layout = match classify_type llty with
      | Struct ->
        let layout = Sizeof.struct_layout llty in
        List.mapi (fun i x -> fst layout.(i), encode_value (snd layout.(i)) x) l
      | Array | Vector ->
        let elty = element_type llty in
        let sz = Sizeof.sizeof elty in
        List.mapi (fun i x -> sz*i, encode_value elty x) l
      | _ -> assert false
    in
    let const, source = List.fold_left (fun (const, source) (off, x) ->
        match shift_left x (8*off) with
        | ConstBits bi ->
          BigInt.(lor) const bi, source
        | SourceBits s -> const, s::source
      ) (BigInt.zero, []) layout
    in
    begin match const, source with
    | bi, [] -> ConstBits bi
    | bi, s ->
      let s = if BigInt.(equal zero) bi then s else bits_source (ConstBits bi) :: s in
      match s with
      | [] -> assert false
      | [x] -> SourceBits x
      | [x; y] -> SourceBits (Printf.sprintf "Big_int.or_big_int %s %s" (parens x) (parens y))
      | hd::tl -> SourceBits ("List.fold_left Big_int.or_big_int " ^ parens hd ^ " [" ^ String.concat "; " tl ^ "]")
    end
and encode_value_s llty bits =
  encode_value llty bits |> bits_source
and encode_value_s_bytes llty bits =
  let sz = Sizeof.sizeof llty in
  match encode_value llty bits with
  | SourceBits s -> "R.bytes_of_bits " ^ string_of_int sz ^ " " ^ parens s
  | ConstBits bi ->
    if BigInt.(equal zero) bi
    then "Bytes.make "^string_of_int sz^" '\\000'"
    else Printf.sprintf "Bytes.of_string %S" @@ Bytes.unsafe_to_string @@ Runtime.bytes_of_bits sz bi

(* decode value from bits. *)
let rec decode_value_s llty bits =
  decode_value llty bits |> to_source llty
and decode_value llty bits = match bits with
  | ConstBits bi ->
    begin match classify_type llty with
    | Integer -> Integer bi
    | Half ->    Float (Runtime.decode_float (5,11) bi)
    | Float ->   Float (Runtime.decode_float (8,24) bi)
    | Double ->  Float (Runtime.decode_float (11,53) bi)
    | X86fp80 -> Float (Runtime.decode_float_x87 bi)
    | Fp128 ->   Float (Runtime.decode_float (15,113) bi)
    | Ppc_fp128 -> failwith "NYI Ppc_fp128 decode"
    | Struct ->
      List (Array.fold_right (fun (off, ty) acc ->
          decode_value ty (ConstBits (BigInt.extract ~low:(off*8) ~len:(8*Sizeof.sizeof ty) bi)) :: acc
        ) (Sizeof.struct_layout llty) []
      )
    | Array | Vector ->
      let elty = element_type llty in
      let elbits = 8 * Sizeof.sizeof elty in
      List (List.init
        (aggregate_length llty)
        (fun i -> decode_value elty @@ ConstBits (BigInt.extract ~low:(i*elbits) ~len:elbits bi))
      )
    | _ -> assert false
    end
  | SourceBits s ->
    Source (match classify_type llty with
      | Integer ->
        let width = integer_bitwidth llty in
        if width = 1 then "Big_int.(eq_big_int unit_big_int) " ^ parens s
        else if width <= 30 then "Big_int.int_of_big_int " ^ parens s
        else if width <= 64 then "Big_int.int64_of_big_int " ^ parens s
        else s
      | Half ->    "R.decode_float (5,11) " ^ parens s
      | Float ->   "R.decode_float (8,24) " ^ parens s
      | Double ->  "R.decode_float (11,53) " ^ parens s
      | X86fp80 -> "R.decode_float_x87 " ^ parens s
      | Fp128 ->   "R.decode_float (15,113) " ^ parens s
      | Ppc_fp128 -> failwith "NYI Ppc_fp128 decode"
      | Struct ->
        bindname ~sname:"st" s (fun sname ->
          let l = Array.fold_right (fun (off, ty) acc ->
              let sz = Sizeof.sizeof ty in
              decode_value_s ty (SourceBits (Printf.sprintf "Big_int.extract_big_int %s %d %d" sname (off*8) (sz*8))) :: acc
            ) (Sizeof.struct_layout llty) []
          in
          "(" ^ String.concat ", " l ^ ")"
        )
      | Array | Vector ->
        let elty = element_type llty in
        let elsz = Sizeof.sizeof elty in
        bindname ~sname:"st" s (fun sname ->
          "(" ^ String.concat ", " (List.init (aggregate_length llty) (fun i ->
            SourceBits (Printf.sprintf "Big_int.extract_big_int %s %d %d" sname (i*elsz*8) (elsz*8))
            |> decode_value_s elty
          )) ^ ")"
        )
      | Pointer -> "R.decode_pointer " ^ parens s
      | tk -> (failwith "Unsupported decode type "^string_of_typekind tk)
    )

let binop op (llty, a) (llty2, b) =
  (* TODO: none of the checking is implemented. *)
  let tk = classify_type llty in
  assert (tk = classify_type llty2);
  let integer_op bits a b = match op with
    | `Add  (_nuw, _nsw) -> Runtime.IntBig.add bits a b
    | `Sub  (_nuw, _nsw) -> Runtime.IntBig.sub bits a b
    | `Mul  (_nuw, _nsw) -> Runtime.IntBig.mul bits a b
    | `UDiv (_exact) -> Runtime.IntBig.udiv bits a b
    | `SDiv (_exact) -> Runtime.IntBig.sdiv bits a b
    | `URem -> Runtime.IntBig.urem bits a b
    | `SRem -> Runtime.IntBig.srem bits a b
    | `Shl  (_nuw, _nsw) -> Runtime.IntBig.shl bits a b
    | `LShr (_exact) -> Runtime.IntBig.lshr bits a b
    | `AShr (_exact) -> Runtime.IntBig.ashr bits a b
    | `And -> Runtime.IntBig.logand bits a b
    | `Or  -> Runtime.IntBig.logor bits a b
    | `Xor -> Runtime.IntBig.logxor bits a b
  in
  let source_op bits a b =
    let fs = match op with
      | `Add  (_nuw, _nsw) -> "add"
      | `Sub  (_nuw, _nsw) -> "sub"
      | `Mul  (_nuw, _nsw) -> "mul"
      | `UDiv (_exact) -> "udiv"
      | `SDiv (_exact) -> "sdiv"
      | `URem -> "urem"
      | `SRem -> "srem"
      | `Shl  (_nuw, _nsw) -> "shl"
      | `LShr (_exact) -> "lshr"
      | `AShr (_exact) -> "ashr"
      | `And -> "logand"
      | `Or  -> "logor"
      | `Xor -> "logxor"
    in
    int_modcall bits fs ^ (parens a) ^ " " ^ (parens b)
  in
  match tk with
  | Integer ->
    let bits = integer_bitwidth llty in
    assert (bits = integer_bitwidth llty2);
    begin match a, b with
    | Integer a, Integer b -> Integer (integer_op bits a b)
    | _ -> Source (source_op bits (to_source llty a) (to_source llty2 b))
    end
  | Vector ->
    let nelements = vector_size llty in
    assert (nelements = vector_size llty2);
    let intty = element_type llty in
    let intty2 = element_type llty2 in
    if classify_type intty <> Integer then assert false;
    if classify_type intty2 <> Integer then assert false;
    let bits = integer_bitwidth intty in
    assert (bits = integer_bitwidth intty2);
    begin match a, b with
    | List al, List bl ->
      List (
        List.map2 (fun a b -> match a, b with
        | Integer a, Integer b -> Integer (integer_op bits a b)
        | _ -> Source (source_op bits (to_source intty a) (to_source intty2 b))
        ) al bl
      )
    | _, _ ->
      let a, b = to_source llty a, to_source llty2 b in
      let vas = List.init nelements (fun i -> "a" ^ string_of_int i) in
      let vbs = List.init nelements (fun i -> "b" ^ string_of_int i) in
      Source (
        "(let " ^ String.concat "," vas ^ " = " ^ unparens a
        ^ " and " ^ String.concat "," vbs ^ " = " ^ unparens b ^ " in "
        ^ String.concat ", " (List.map2 (source_op bits) vas vbs) ^ ")"
      )
    end
  | tk -> failwith ("Invalid type " ^ string_of_typekind tk ^ " for binop operations")

let icmp (op : Icmp.t) (llty, a) (llty2, b) =
  let tk = classify_type llty in
  assert (tk = classify_type llty2);
  match tk with
  | Integer ->
    let bits = integer_bitwidth llty in
    assert (bits = integer_bitwidth llty2);
    begin match a, b with
    | Integer a, Integer b -> 
      Integer (if (match op with
        | Eq  -> Runtime.IntBig.eq  bits a b
        | Ne  -> Runtime.IntBig.ne  bits a b
        | Ugt -> Runtime.IntBig.ugt bits a b
        | Uge -> Runtime.IntBig.uge bits a b
        | Ult -> Runtime.IntBig.ult bits a b
        | Ule -> Runtime.IntBig.ule bits a b
        | Sgt -> Runtime.IntBig.sgt bits a b
        | Sge -> Runtime.IntBig.sge bits a b
        | Slt -> Runtime.IntBig.slt bits a b
        | Sle -> Runtime.IntBig.sle bits a b
      ) then BigInt.one else BigInt.zero)
    | _ ->
      let a, b = to_source llty a, to_source llty2 b in
      let fs = match op with
        | Eq  -> "eq"
        | Ne  -> "ne"
        | Ugt -> "ugt"
        | Uge -> "uge"
        | Ult -> "ult"
        | Ule -> "ule"
        | Sgt -> "sgt"
        | Sge -> "sge"
        | Slt -> "slt"
        | Sle -> "sle"
      in
      Source (int_modcall bits fs ^ (parens a) ^ " " ^ (parens b))
    end
  | Vector -> failwith "vector icmp NYI"
  | Pointer ->
    Source (
      let a = parens @@ to_source llty a
      and b = parens @@ to_source llty2 b
      in match op with
      | Eq ->  "R.compare_pointer "^a^" "^b^" = 0"
      | Ne ->  "R.compare_pointer "^a^" "^b^" <> 0"
      | Ugt -> "R.compare_pointer "^a^" "^b^" > 0"
      | Uge -> "R.compare_pointer "^a^" "^b^" >= 0"
      | Ult -> "R.compare_pointer "^a^" "^b^" < 0"
      | Ule -> "R.compare_pointer "^a^" "^b^" <= 0"
      | Sgt -> "R.compare_pointer "^a^" "^b^" > 0"
      | Sge -> "R.compare_pointer "^a^" "^b^" >= 0"
      | Slt -> "R.compare_pointer "^a^" "^b^" < 0"
      | Sle -> "R.compare_pointer "^a^" "^b^" <= 0"
    )
  | tk -> failwith ("Invalid type " ^ string_of_typekind tk ^ " for icmp operations")

let cast casttype (llty, x) dstwidth =
  let source_cast srcwidth s =
    let conv = match casttype with `Signed -> "BigInt.signed" | `Unsigned -> "BigInt.unsigned" in
    int_modcall dstwidth "of_bi" ^ "("^conv^" "^string_of_int dstwidth^" @@ "^ int_modcall srcwidth "to_bi" ^ parens s ^ ")"
  in
  let integer_cast srcwidth bi =
    begin match casttype with
    | `Signed -> BigInt.signed srcwidth bi
    | `Unsigned -> BigInt.unsigned srcwidth bi
    end
  in
  match classify_type llty with
  | Integer ->
    let srcwidth = integer_bitwidth llty in
    begin match x with
    | Integer bi -> Integer (integer_cast srcwidth bi)
    | Source s -> Source (source_cast srcwidth s)
    | _ -> assert false
    end
  | Vector ->
    let intty = element_type llty in
    if classify_type intty <> Integer then assert false;
    let srcwidth = integer_bitwidth intty in
    begin match x with
    | List l ->
      List (
        List.map (function
        | Integer bi -> Integer (integer_cast srcwidth bi)
        | Source s -> Source (source_cast srcwidth s)
        | _ -> assert false
        ) l
      )
    | Source s ->
      let ts = List.init (vector_size llty) (fun i -> "t" ^ string_of_int i) in
      Source (
        "(let " ^ String.concat "," ts ^ " = " ^ unparens s ^ " in "
        ^ String.concat ", " (List.map (fun t -> source_cast srcwidth t) ts) ^ ")"
      )
    | _ -> assert false
    end
  | _ -> assert false

let rec zero_value llty : value =
  match classify_type llty with
  | Void -> Void
  | Integer -> Integer BigInt.zero
  | Pointer -> NullPointer
  | Half | Float | Double | X86fp80 | Fp128 | Ppc_fp128 -> Float 0.
  | X86_mmx -> failwith "NYI X86_mmx"
  | Label | Function | Metadata | Token -> failwith "nonphysical type"
  | Struct ->
    List (Array.fold_right (fun ty acc -> zero_value ty :: acc) (struct_element_types llty) [])
  | Array | Vector ->
    let z = zero_value @@ element_type llty in
    List (List.init (aggregate_length llty) (fun _ -> z))

let poison_value = zero_value

let _bigint_to_unsigned_int llty bi =
  assert (classify_type llty = Integer);
  BigInt.unsigned (integer_bitwidth llty) bi |> BigInt.to_int

let vec_extract (vecty, vec) (idxty, idx) =
  assert (classify_type vecty = Vector);
  let elty = element_type vecty in
  match vec, idx with
  | List l, Integer bi ->
    begin
    match _bigint_to_unsigned_int idxty bi with None -> poison_value elty | Some idx ->
    match List.nth_opt l idx with None -> poison_value elty | Some elt ->
    elt
    end
  | List l, Source s ->
    let elty = element_type vecty in
    Source (
      "(match " ^ unparens s ^ " with "
      ^ String.concat " | " (List.mapi (fun i x -> string_of_int i ^ " -> " ^ to_source elty x) l)
      ^ " | _ -> " ^ unparens (to_source elty (poison_value elty)) ^ ")"
    )
  | Source s, Integer bi ->
    begin
    match _bigint_to_unsigned_int idxty bi with None -> poison_value elty | Some idx ->
    let siz = vector_size vecty in
    if idx >= siz then poison_value elty else
    Source (match siz with
      | 1 -> s
      | 2 -> (if idx = 0 then "fst " else "snd ") ^ parens s
      | _ ->
        let ts = List.init siz (fun i -> if i = idx then "t" else "_") in
        "(let " ^ String.concat "," ts ^ " = " ^ unparens s ^ " in t)"
    )
    end
  | Source vec, Source idx ->
    let ts = List.init (vector_size vecty) (fun i -> "t" ^ string_of_int i) in
    Source (
      "(let " ^ String.concat "," ts ^ " = " ^ unparens vec ^ " in "
      ^ "match " ^ unparens idx ^ " with "
      ^ String.concat " | " (List.mapi (fun i t -> string_of_int i ^ " -> " ^ t) ts)
      ^ " | _ -> " ^ unparens (to_source elty (poison_value elty)) ^ ")"
    )
  | _ -> assert false

let vec_insert (vecty, vec) (eltty, elt) (idxty, idx) =
  match vec, idx with
  | List l, Integer bi ->
    begin
    match _bigint_to_unsigned_int idxty bi with None -> (*poison*) vec | Some idx ->
    let rec f i = function
      | [] -> (*poison*) []
      | hd::tl -> if i = idx then elt::tl else hd::f (i+1) tl
    in
    List (f 0 l)
    end
  | Source s, Integer bi ->
    begin
    match _bigint_to_unsigned_int idxty bi with None -> (*poison*) vec | Some idx ->
    let ts = List.init (vector_size vecty) (fun i -> if i = idx then "_" else "t" ^ string_of_int i) in
    Source (
      "(let " ^ String.concat "," ts ^ " = " ^ unparens s
      ^ " in " ^ String.concat "," (List.map (fun t -> if t = "_" then to_source vecty vec else t) ts)
    )
    end
  | _, Source idx ->
    let sz = vector_size vecty in
    let ts = List.init sz (fun i -> "t" ^ string_of_int i) in
    Source (
      "(let " ^ String.concat "," ts ^ " = " ^ unparens (to_source vecty vec)
      ^ " and t = " ^ unparens (to_source eltty elt)
      ^ " in match " ^ unparens idx ^ " with "
      ^ String.concat " | " (List.init sz (fun i -> string_of_int i ^ " -> " ^ String.concat "," (List.init sz (fun j -> if i = j then "t" else "t" ^ string_of_int i))))
      ^ " | _ -> (*poison*) " ^ String.concat "," ts ^ ")"
    )
  | _ -> assert false

let scale x factor =
  match x with
  | ConstInt i -> ConstInt (i * factor)
  | SourceInt s -> SourceInt ("("^string_of_int factor^"*"^s^")")

let sum ints =
  List.fold_left (fun (const, source) -> function
    | ConstInt i -> const + i, source
    | SourceInt s -> const, s :: source
  ) (0, []) ints
  |> function
  | const, [] -> ConstInt const
  | 0, [s] -> SourceInt s
  | 0, source -> SourceInt ("(" ^ String.concat "+" source ^ ")")
  | const, source -> SourceInt ("(" ^ String.concat "+" (string_of_int const :: source) ^ ")")

let rec getelementoff acc llty = function [] -> acc | hd::tl ->
  let idx = to_signed_int hd in
  match classify_type llty with
  | Void | Integer | Pointer | Half | Float | Double | X86fp80 | Fp128 | Ppc_fp128 | X86_mmx -> failwith "Can't get element of scalar"
  | Label | Function | Metadata | Token -> failwith "nonphysical type"
  | Struct ->
    let idx = match idx with
      | ConstInt x -> x
      | _ -> failwith "struct element index must be constant int"
    in
    let off, ty =
      try (Sizeof.struct_layout llty).(idx)
      with Invalid_argument _ -> failwith "struct element index out of bounds!"
    in
    getelementoff (ConstInt off :: acc) ty tl
  | Array | Vector  ->
    let elty = element_type llty in
    getelementoff (scale idx (Sizeof.sizeof elty) :: acc) elty tl

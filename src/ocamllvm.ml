open Llvm
open MyLlvm

let parens = Value.Private.parens

(* ...actually, afaict the llvm interfaces are total shit for analysis?
 * we should just implement our own bitcode reader.
 * the way we get unique names to compare, via string_of_llvalue, takes the majority
 * of the execution time (split 50% for values and blocks)... ugh. *)

(* Note: we effectivley consider vectors as aggregate data types, to support
 * legacy getelementptr-into-vector usage. If this changes in a future version
 * of llvm, we'll consider vectors as non-aggregate. *)

external reraise : exn -> 'a = "%reraise"
module StringMap = Map.Make(struct type t = string let compare = String.compare end)

let runtime_module = "R"

(* let int64repr x = if Int64.compare x 0L < 0 then "(" ^ Int64.to_string x ^ "L)" else Int64.to_string x ^ "L"
let intrepr x = if Int64.compare x 0L < 0 then "(" ^ Int64.to_string x ^ ")" else Int64.to_string x *)

let rec is_all_digits ?(i=0) s =
  if i >= String.length s then true else
  match s.[i] with '0'..'9' -> is_all_digits ~i:(i+1) s | _ -> false

(* Mangle an llvm name to an acceptable ocaml value name (that won't collide with stuff we need). *)
let mangle ?(c='c') s =
  assert (s <> "");

  (* start by special-casing temporaries *)
  if String.length s >= 2 && s.[0] = '%' && is_all_digits ~i:1 s then "t" ^ String.sub s 1 (String.length s - 1) else

  let b = Bytes.create (String.length s * 3 + 2) in
  Bytes.set b 0 c;
  Bytes.set b 1 '_';
  let rec f i j =
    if i >= String.length s then j else
    match s.[i] with
    | ('0' .. '9' | 'A' .. 'Z' | 'a' .. 'z' | '_') as c ->
      Bytes.set b j c;
      f (i+1) (j+1)
    | '.' ->
      Bytes.set b j '\'';
      f (i+1) (j+1)
    | c ->
      Bytes.set b (j+0) @@ '\'';
      Bytes.set b (j+1) @@ '\'';
      Bytes.set b (j+2) @@ "0123456789ABCDEF".[(int_of_char c lsr 4) land 15];
      Bytes.set b (j+3) @@ "0123456789ABCDEF".[int_of_char c land 15];
      f (i+1) (j+4)
  in
  Bytes.sub_string b 0 (f 0 2)

let my_block_name llb = mangle ~c:'b' @@ value_name (value_of_block llb)
let my_instr_name lli = mangle ~c:'v' @@ value_name lli
let my_function_name llf = mangle ~c:'f' @@ value_name llf
let my_function_pointer_name llf = mangle ~c:'p' @@ value_name llf
let my_global_name llv = mangle ~c:'g' @@ value_name llv

let has_any_users lli = match use_begin lli with Some _ -> true | None -> false

let phinode_argparams llb =
  match fold_left_instrs (fun acc lli ->
    match instr_opcode lli with
    | PHI -> ("~(" ^ my_instr_name lli ^ ":" ^ Value.typename_for (type_of lli) ^ ")") :: acc
    | _ -> acc
  ) [] llb
  with
  | [] -> "()"
  | l -> String.concat " " @@ List.rev l

let phinode_argvalues ~src ~dst =
  let src_name = my_block_name src in
  fold_left_instrs (fun acc lli ->
    match instr_opcode lli with
    | PHI ->
      let llv, _ = List.find (fun (_, llb) -> String.equal src_name @@ my_block_name llb) @@ incoming lli in
      (my_instr_name lli, llv) :: acc
    | _ -> acc
  ) [] dst |> List.rev

let get_element_ptr read inst =
  let get_op i =
    let t = operand inst i
    in type_of t, read t
  in
  let ty, base = get_op 0 in
  assert (classify_type ty = Pointer);
  let off = Value.scale (Value.to_signed_int @@ get_op 1) (Sizeof.sizeof @@ element_type ty) in
  let off = Value.getelementoff [off] (element_type ty) @@ List.init (num_operands inst - 2) (fun i -> get_op (i+2)) in
  let off = Value.sum off |> Value.int_source in
  Value.Source ("R.pointer_offset "^parens (Value.to_source ty base)^" "^parens off)


class llvalue_helper = object(self)
  method private unhandled llv : Value.value = failwith ("unsupported value kind " ^ string_of_valuekind @@ classify_value llv)
  method argument llv = self#unhandled llv
  method instruction llv = self#unhandled llv
  method global_variable llv = self#unhandled llv
  method global_alias llv = self#unhandled llv
  method global_ifunc llv = self#unhandled llv
  method function_value llv = self#unhandled llv
  method null_value llv = self#unhandled llv
  method basic_block llv = self#unhandled llv
  method block_address llv = self#unhandled llv
  method inline_asm llv = self#unhandled llv
  method md_node llv = self#unhandled llv
  method md_string llv = self#unhandled llv
end

let rec read_llvalue (helper : llvalue_helper) llv =
  match classify_value llv with
  | ConstantInt ->
    begin match int64_of_const llv with
    | Some x -> Value.Integer (BigInt.of_int64 x)
    | None -> Value.Integer (BigInt.of_string @@ string_of_llvalue llv) (* TODO: not sure if this is quite right. *)
    end
  | ConstantFP ->
    begin match float_of_const llv with
    | Some x -> Value.Float x
    | None -> failwith "failed to interpret float constant"
    end
  | ConstantPointerNull -> Value.NullPointer
  | ConstantAggregateZero -> Value.zero_value @@ type_of llv
  | ConstantDataVector | ConstantDataArray ->
    Value.List (List.init (aggregate_length @@ type_of llv) (fun i -> read_llvalue helper @@ const_element llv i))
  | ConstantVector | ConstantArray | ConstantStruct ->
    Value.List (List.init (num_operands llv) (fun i -> read_llvalue helper @@ operand llv i))
  | UndefValue -> Value.zero_value @@ type_of llv (* TODO *)
  | ConstantExpr -> begin match constexpr_opcode llv with
    | BitCast -> begin
      let x = operand llv 0 in
      let src = type_of x in
      let dst = type_of llv in
      match classify_type src, classify_type dst with
      | Pointer, Pointer -> read_llvalue helper x
      | _ -> Value.encode_value src @@ read_llvalue helper x |> Value.decode_value dst
      end
    | GetElementPtr -> get_element_ptr (read_llvalue helper) llv
    (* TODO: These two are just wrong. <- wait why? *)
    | PtrToInt ->
      let width = integer_bitwidth @@ type_of llv in
      Value.Source (Value.Private.int_modcall width "of_int" ^ "@@ R.ptrtoint " ^ parens (Value.to_source (type_of @@ operand llv 0) @@ read_llvalue helper @@ operand llv 0))
    | IntToPtr ->
      let width = integer_bitwidth @@ type_of @@ operand llv 0 in
      Value.Source ("R.inttoptr " ^ parens (Value.to_source (type_of @@ operand llv 0) @@ read_llvalue helper @@ operand llv 0) ^ " |> " ^ Value.Private.int_modcall width "to_unsigned_int")
    | op -> failwith ("NYI ConstantExpr " ^ string_of_opcode op)
    end
  | Argument -> helper#argument llv
  | Instruction _ -> helper#instruction llv
  | GlobalVariable -> helper#global_variable llv
  | GlobalAlias -> helper#global_alias llv
  | GlobalIFunc -> helper#global_ifunc llv
  | Function -> helper#function_value llv
  | NullValue -> helper#null_value llv
  | BasicBlock -> helper#basic_block llv
  | BlockAddress -> helper#block_address llv
  | InlineAsm -> helper#inline_asm llv
  | MDNode -> helper#md_node llv
  | MDString -> helper#md_string llv

let instruction inst : string = try
  (* Printf.eprintf "%s\n%!" @@ string_of_llvalue inst; *)
  let read = read_llvalue (object
    inherit llvalue_helper
    method! argument llv = Value.Source (my_instr_name llv)
    method! instruction llv = Value.Source (my_instr_name llv)
    method! global_variable llv = Value.Source (my_global_name llv)
    method! function_value llv = Value.Source ("Lazy.force " ^ my_function_pointer_name llv)
    method! private unhandled llv = failwith ("unsupported value kind " ^ string_of_valuekind (classify_value llv) ^ " in " ^ string_of_llvalue inst)
  end) in
  let read_s llv = read llv |> Value.to_source (type_of llv) in
  let get_op i =
    let t = operand inst i
    in type_of t, read t
  in
  let get_op_s i = read_s @@ operand inst i in
  let set_local_s obj =
    if has_any_users inst
    then "let " ^ my_instr_name inst ^ " = " ^ obj ^ " in"
    else match classify_type (type_of inst) with
    | Void -> obj ^ ";"
    | _ -> "ignore @@ " ^ obj ^ ";"
  in
  let set_local obj =
    set_local_s @@ Value.to_source (type_of inst) obj
  in
  let call_label llv =
    assert (classify_value llv = BasicBlock);
    let llb = block_of_value llv in
    my_block_name llb ^ " " ^ (
      match phinode_argvalues ~src:(instr_parent inst) ~dst:llb with
      | [] -> "()"
      | l -> String.concat " " @@ List.map (fun (name, value) -> "~"^name^":"^parens (read_s value)) l
    )
  in
  match instr_opcode inst with
  | Ret ->
    (match num_operands inst with
      | 0 -> Value.void_source ()
      | 1 -> get_op_s 0
      | _ -> assert false
    )
  | Br ->
    (match num_operands inst with
      | 1 -> call_label @@ operand inst 0
      | 3 ->
        let i1, cond = get_op 0 in
        (* ...yes, they're backwards in operand order. *)
        let iftrue = call_label (operand inst 2) in
        let iffalse = call_label (operand inst 1) in
        "if "^Value.to_bool_s i1 cond^" then "^iftrue^" else "^iffalse
      | _ -> assert false
    )
  | Switch ->
    let noperands = num_operands inst in
    assert (noperands >= 2 && (noperands mod 2) = 0);
    let switchval = get_op_s 0 in
    let default = call_label @@ operand inst 1 in
    let cases = List.init (noperands/2 - 1) (fun i -> operand inst (i*2 + 2), operand inst (i*2 + 3)) in
    (* I think only constants are allowed here so this sort doesn't even matter? *)
    let cases = List.stable_sort (fun (x,_) (y,_) -> compare (is_constant y) (is_constant x)) cases in
    let cases = List.map (fun (cval, clab) ->
      if is_constant cval then
        " | " ^ read_s cval ^ " -> " ^ call_label clab
      else
        " | t when t = " ^ read_s cval ^ " -> " ^ call_label clab
    ) cases in
    "begin match " ^ switchval ^ " with" ^ String.concat "" cases ^ " | _ -> " ^ default ^ " end"

  (* | IndirectBr -> *)
  (* | Invoke -> *)

  | Call ->
    (* TODO: very incomplete *)
    let llv = operand inst (num_operands inst - 1) in
    let intrinsic = if is_intrinsic llv then value_name llv else "" in
    (* NB: This isn't our preferred way of handling intrinsics. The preferred way is to
     * handle it like a normal call, and then let make_intrinsic generate that function. *)
    begin match intrinsic with
    | "llvm.va_start" ->
      assert (num_operands inst - 1 = 1);
      let vaptr = operand inst 0 in
      "R.va_start " ^ parens (read_s vaptr) ^ " varargs;"
    | "llvm.va_end" ->
      assert (num_operands inst - 1 = 1);
      let vaptr = operand inst 0 in
      "R.va_end " ^ parens (read_s vaptr) ^ ";"
    | _ ->
      match classify_value llv with
      | Function ->
        let fn_ty = element_type @@ type_of llv in
        let fargs = Array.length @@ param_types fn_ty in
        let nargs = num_operands inst - 1 in
        if nargs < fargs then
          failwith ("Too few args passed to " ^ my_function_name llv);
        if nargs > fargs && not (is_var_arg fn_ty) then
          failwith ("Too many args passed to " ^ my_function_name llv);
        let s = my_function_name llv ^ " "
          ^ String.concat " " (List.init fargs (fun i -> parens @@ read_s @@ operand inst i))
        in
        let s =
          if is_var_arg fn_ty then (
            s
            ^ " ["
            ^ String.concat "; " (List.init (nargs - fargs) (fun i -> Value.to_polysource @@ get_op (fargs+i)))
            ^ "]"
          ) else (
            if fargs = 0 then s ^ "()" else s
          )
        in
        set_local_s s
      | _ ->
        let args = List.init (num_operands inst - 1) (fun i -> Value.to_polysource @@ get_op i) in
        let call = "R.call_ptr " ^ parens (read_s llv) ^ " [" ^ String.concat ";" args ^ "]" in
        let pat, ret = Value.polyval_pattern (type_of inst) "ret" in
        set_local_s ("(match " ^ call ^ " with " ^ pat ^ " -> " ^ ret ^ " | _ -> assert false)")
    end

  | Alloca ->
    let ty = type_of inst in
    assert (classify_type ty = Pointer);
    let ty = element_type ty in
    set_local_s ("R.alloc " ^ string_of_int (Sizeof.sizeof ty))
  | Load ->
    let ptr = parens @@ get_op_s 0 in
    let nbytes = string_of_int @@ Sizeof.sizeof @@ type_of inst in
    set_local @@ Value.decode_value (type_of inst) (SourceBits ("R.load_bits "^parens ptr^" "^nbytes))
  | Store ->
    let llty, x = get_op 0 in
    let nbytes = string_of_int @@ Sizeof.sizeof llty in
    let ptr = parens @@ get_op_s 1 in
    "R.store_bits "^ptr^" "^nbytes^" "^(parens @@ Value.encode_value_s llty x)^";"
  | Add  -> set_local @@ Value.binop (`Add (false, false)) (get_op 0) (get_op 1)
  | Sub  -> set_local @@ Value.binop (`Sub (false, false)) (get_op 0) (get_op 1)
  | Mul  -> set_local @@ Value.binop (`Mul (false, false)) (get_op 0) (get_op 1)
  | UDiv -> set_local @@ Value.binop (`UDiv (false)) (get_op 0) (get_op 1)
  | SDiv -> set_local @@ Value.binop (`SDiv (false)) (get_op 0) (get_op 1)
  | URem -> set_local @@ Value.binop (`URem) (get_op 0) (get_op 1)
  | SRem -> set_local @@ Value.binop (`SRem) (get_op 0) (get_op 1)
  | Shl  -> set_local @@ Value.binop (`Shl (false, false)) (get_op 0) (get_op 1)
  | LShr -> set_local @@ Value.binop (`LShr (false)) (get_op 0) (get_op 1)
  | AShr -> set_local @@ Value.binop (`AShr (false)) (get_op 0) (get_op 1)
  | And  -> set_local @@ Value.binop (`And) (get_op 0) (get_op 1)
  | Or   -> set_local @@ Value.binop (`Or) (get_op 0) (get_op 1)
  | Xor  -> set_local @@ Value.binop (`Xor) (get_op 0) (get_op 1)
  | (ZExt | Trunc | SExt) as operator ->
    assert (num_operands inst = 1);
    let outty = type_of inst in
    let dstwidth = match classify_type outty with
      | Integer -> integer_bitwidth outty
      | Vector ->
        assert (classify_type (element_type outty) = Integer);
        integer_bitwidth (element_type outty)
      | _ -> assert false
    in
    let casttype = match operator with SExt -> `Signed | _ -> `Unsigned in
    set_local @@ Value.cast casttype (get_op 0) dstwidth
  | ICmp ->
    let pred = match icmp_predicate inst with Some x -> x | None -> assert false in
    set_local @@ Value.icmp pred (get_op 0) (get_op 1)
  | Select ->
    assert (num_operands inst = 3);
    let cond = get_op_s 0 in
    let tval = get_op_s 1 in
    let fval = get_op_s 2 in
    begin match classify_type @@ type_of @@ operand inst 0 with
    | Integer ->
      set_local_s ("if "^cond^" then "^tval^" else "^fval)
    | Vector ->
      failwith "vector select NYI"
    | _ -> assert false
    end
  (* | FAdd ->
  | FSub ->
  | FMul ->
  | FDiv ->
  | FRem ->
  | FPToUI ->
  | FPToSI ->
  | UIToFP ->
  | SIToFP ->
  | FPExt  ->
  | FPTrunc ->
  | FCmp -> *)

  (* TODO: actually cast, somehow? *)
  | PtrToInt ->
    let width = integer_bitwidth @@ type_of inst in
    set_local_s (Value.Private.int_modcall width "of_int" ^ "@@ R.ptrtoint " ^ parens (get_op_s 0))
  | IntToPtr ->
    let width = integer_bitwidth @@ type_of @@ operand inst 0 in
    set_local_s ("R.inttoptr " ^ parens (get_op_s 0) ^ " |> " ^ Value.Private.int_modcall width "to_unsigned_int")
  | BitCast ->
    let srcty, src = get_op 0 in
    let dstty = type_of inst in
    begin match classify_type srcty, classify_type dstty with
    | Pointer, Pointer -> set_local src (* Currently, pointer casting is both pointless and also sometimes breaks things. *)
    | _, _ -> set_local @@ Value.decode_value dstty (Value.encode_value srcty src)
    end
  | GetElementPtr ->
    set_local @@ get_element_ptr read inst
  (* | ExtractValue ->
    let agg = operand inst 0 in
    let elt_off = Value.getelementoff (fun _ -> 1) [] (type_of agg) @@ List.init (num_operands inst - 1) (fun i -> get_op (i+1)) in
    let elt_off = Value.sum elt_off |> Value.int_source in
    set_local_s (read_s agg ^ ".("^elt_off^")")
  | InsertValue ->
    let agg = operand inst 0 in
    let eltty, elt = get_op 1 in
    let elt_off = Value.getelementoff (fun _ -> 1) [] (type_of agg) @@ List.init (num_operands inst - 2) (fun i -> get_op (i+2)) in
    let elt_off = Value.sum elt_off |> Value.int_source in
    set_local_s (read_s agg ^ ".("^elt_off^") <- " ^ (Value.to_source eltty elt)) *)

  | ExtractElement -> set_local (Value.vec_extract (get_op 0) (get_op 1))
  | InsertElement -> set_local (Value.vec_insert (get_op 0) (get_op 1) (get_op 2))
  (* | ShuffleVector -> "" *)
  (* | Fence -> ""
  | AtomicCmpXchg -> ""
  | AtomicRMW -> ""
  | Resume -> ""
  | LandingPad -> "" *)

  | VAArg ->
    assert (num_operands inst = 1);
    let pat, var = Value.polyval_pattern (type_of inst) "x" in
    set_local_s (
      Printf.sprintf
        "(match R.va_arg %s with %s -> %s | x -> failwith (%S ^ R.show_polyval x))"
          (parens @@ get_op_s 0)
          pat
          var
          ("expected " ^ pat ^ " got ")
    )
  | PHI -> "()" (* phi nodes are set in args. *)
  | Unreachable -> "assert false"
  (* | Invalid | Invalid2 -> *)
  (* | UserOp1 | UserOp2 -> *)
  | x -> failwith ("unhandled opcode " ^ string_of_opcode x)
with e -> (Printf.eprintf "%s\n" @@ string_of_llvalue inst; reraise e)

let make_intrinsic llf =
  assert (is_intrinsic llf);
  let name = value_name llf in
  let uintparam argname argidx =
    let ty = type_of @@ param llf argidx in
    (* TODO: overflow checking *)
    match classify_type ty with
    | Integer -> parens @@ Value.to_unsigned_int_s (ty, Value.Source argname)
    | x -> failwith ("Integer parameter expected for intrinsic " ^ name ^ "arg "^string_of_int argidx^", got " ^ string_of_typekind x)
  in
  let pbitsparam argidx =
    let ty = element_type @@ type_of @@ param llf argidx in
    match classify_type ty with
    | Integer -> integer_bitwidth ty |> string_of_int
    | x -> failwith ("Integer pointer parameter expected for intrinsic " ^ name ^ "arg "^string_of_int argidx^", got " ^ string_of_typekind x)
  in
  let let_fun = "let "^my_function_name llf^" " in
  match String.split_on_char '.' name with
  | "llvm"::"memcpy"::_ -> let_fun ^ "dst src len isvol = "^runtime_module^".llvm_memcpy dst "^pbitsparam 0^" src "^pbitsparam 1^" "^uintparam "len" 2^" isvol"
  | "llvm"::"memmove"::_ -> let_fun ^ "dst src len isvol = "^runtime_module^".llvm_memmove dst "^pbitsparam 0^" src "^pbitsparam 1^" "^uintparam "len" 2^" isvol"
  | "llvm"::"memset"::_ -> let_fun ^ "dst byte len isvol = "^runtime_module^".llvm_memset dst "^pbitsparam 0^" byte "^uintparam "len" 2^" isvol"
  | ["llvm";"objectsize";_ret;_ptr] ->
    let_fun ^ "obj min nullunk = "^runtime_module^".llvm_objectsize obj () min nullunk false"
  | "llvm"::"lifetime"::"start"::_ -> let_fun ^ " _size _ptr = ()"
  | "llvm"::"lifetime"::"end"::_ -> let_fun ^ " _size _ptr = ()"
  | ["llvm"; "va_start"] -> "(* llvm.va_start is handled at call sites. *)"
  | ["llvm"; "va_end"] -> "(* llvm.va_end is handled at call sites. *)"
  | ["llvm"; "va_copy"] -> let_fun ^ "= R.va_copy"
  | _ -> failwith ("Unimplemented intrinsic: " ^ name)

(* just hacks for now. *)
let make_missing_extern llv =
  let name = value_name llv in
  let paramty idx = type_of @@ param llv idx in
  match classify_value llv with
  | Function ->
    let let_fun = "let "^my_function_name llv^" " in
    begin match name with
    | "close" -> Some (let_fun ^ "_fd = (*TODO*) -1L")
    | "write" -> Some (let_fun ^ "_fd buf count = match buf with R.DataPointer {bytes;off;_} -> print_string (Bytes.sub_string bytes off @@ Int64.to_int count); count | _ -> assert false")
    | "abort" -> Some (let_fun ^ "() : unit = raise "^runtime_module^".Abort")
    | "_exit" -> Some (let_fun ^ "x : unit = R.exit @@ "^Value.to_signed_int_s (paramty 0, Value.Source "x"))
    | "magic_printf" -> Some (let_fun ^ "fmt args = print_endline (\"printf(\" ^ String.concat \", \" (Printf.sprintf \"%S\" ("^runtime_module^".cstring_to_string fmt) :: List.map "^runtime_module^".show_polyval args) ^ \")\"); 10L")
    | "malloc" -> Some (let_fun ^ "x = R.alloc (Int64.to_int x)")
    | "free" -> Some (let_fun ^ " = R.dealloc")
    | _ -> None
    end
  | GlobalVariable ->
    let let_eq = "let "^my_global_name llv^" = " in
    let llty = element_type @@ type_of llv in
    begin match name with
    | "errno" -> Some (let_eq ^ " R.alloc_bits " ^ Value.encode_value_s llty (Value.zero_value llty))
    | _ -> None
    end
  | _ -> None

(** Graph of a function's basic blocks. *)
module FunctionGraph = struct
  type t = {
    llf : llvalue;
    entry : string;
    index : llbasicblock StringMap.t;
    succ : unit StringMap.t StringMap.t;
    pred : unit StringMap.t StringMap.t;
  }

  let key_of_block {llf=_;_} = my_block_name
  let block_of_key {index;_} s = StringMap.find s index

  let make llf =
    let index = fold_left_blocks (fun acc llb ->
        StringMap.add (my_block_name llb) llb acc
      ) StringMap.empty llf
    in
    let entry = my_block_name @@ entry_block llf in
    let succ = fold_left_blocks (fun acc llb ->
        match block_terminator llb with None -> assert false | Some lli ->
        let suc = fold_successors (fun succ acc -> StringMap.add (my_block_name succ) () acc) lli StringMap.empty in
        StringMap.add (my_block_name llb) suc acc
      ) StringMap.empty llf
    in
    let pred = StringMap.fold (fun prev nexts acc ->
        StringMap.fold (fun next () acc ->
          StringMap.update next (function None -> assert false | Some already ->
            Some (StringMap.add prev () already)
          ) acc
        ) nexts acc
      ) succ (StringMap.fold (fun x _ acc -> StringMap.add x StringMap.empty acc) succ StringMap.empty)
    in
    {llf; entry; index; succ; pred}

  module V = struct
    type t = string
    let compare = String.compare
    let hash = Hashtbl.hash
    let equal = String.equal
  end

  let entry g = g.entry

  let pred g v = StringMap.fold (fun k () acc -> k::acc) (StringMap.find v g.pred) []
  let succ g v = StringMap.fold (fun k () acc -> k::acc) (StringMap.find v g.succ) []
  let fold_vertex f g init = StringMap.fold (fun k _ acc -> f k acc) g.succ init
  let iter_vertex f g = StringMap.iter (fun k _ -> f k) g.succ
  let iter_succ f g v = StringMap.fold (fun k () _ -> f k) (StringMap.find v g.succ) ()
  let nb_vertex g = StringMap.cardinal g.succ
end

module FuncDominator = Graph.Dominator.Make (FunctionGraph)

(* If this is true, we can skip generating the function pointer for llf. *)
let only_function_call_usage llf =
  fold_left_uses (fun acc use ->
    if not acc then false else
    let inst = user use in
    match classify_value inst with
    | Instruction Call ->
      let x = operand inst (num_operands inst - 1) in
      begin match classify_value x with
      | Function ->
        let func_name = value_name llf in
        if value_name x <> func_name then false else
        let status = ref true in
        for i = 0 to num_operands inst - 2 do
          if value_name (operand inst i) = func_name then status := false
        done;
        !status
      | _ -> false
      end
    | _ -> false
  ) true llf

(** Call graph, including global variables. *)
module UsageGraph = struct
  type t = {
    index : llvalue StringMap.t;
    succ : unit StringMap.t StringMap.t;
    pred : unit StringMap.t StringMap.t;
  }

  let get_llvalue {index;_} s = StringMap.find s index

  let rec global_users f init llv =
    fold_left_uses (fun init use ->
      let llv = user use in
      match classify_value llv with
      | NullValue
      | InlineAsm
      | MDNode
      | MDString
      | BlockAddress
      | ConstantAggregateZero
      | ConstantArray
      | ConstantDataArray
      | ConstantDataVector
      | ConstantExpr
      | ConstantFP
      | ConstantInt
      | ConstantPointerNull
      | ConstantStruct
      | ConstantVector
      | UndefValue
        -> global_users f init llv
      | Argument -> f init (param_parent llv)
      | BasicBlock -> f init (block_parent @@ block_of_value llv)
      | Function -> f init llv
      | GlobalAlias -> f init llv
      | GlobalIFunc -> f init llv
      | GlobalVariable -> f init llv
      | Instruction _ -> f init (instr_parent llv |> block_parent)
    ) init llv

  let make llmodule =
    let index =
      let f map llv = StringMap.add (value_name llv) llv map in
      fold_left_functions f (fold_left_globals f StringMap.empty llmodule) llmodule
    in
    let pred = StringMap.fold (fun key llv acc ->
        StringMap.add
          key
          (global_users (fun map llv -> StringMap.add (value_name llv) () map) StringMap.empty llv)
          acc
      ) index StringMap.empty
    in
    let succ = StringMap.fold (fun next prevs acc ->
        StringMap.fold (fun prev () acc ->
          StringMap.update prev (function None -> assert false | Some already ->
            Some (StringMap.add next () already)
          ) acc
        ) prevs acc
      ) pred (StringMap.fold (fun key _ acc -> StringMap.add key StringMap.empty acc) index StringMap.empty)
    in
    {index; succ; pred}

  module V = struct
    type t = string
    let compare = String.compare
    let hash = Hashtbl.hash
    let equal = String.equal
  end

  let pred g v = StringMap.fold (fun k () acc -> k::acc) (StringMap.find v g.pred) []
  let succ g v = StringMap.fold (fun k () acc -> k::acc) (StringMap.find v g.succ) []
  let fold_vertex f g init = StringMap.fold (fun k _ acc -> f k acc) g.index init
  let iter_vertex f g = StringMap.iter (fun k _ -> f k) g.index
  let iter_succ f g v = StringMap.fold (fun k () _ -> f k) (StringMap.find v g.succ) ()
  let nb_vertex g = StringMap.cardinal g.index

  let self_loop g v = match StringMap.find_opt v (StringMap.find v g.pred) with Some () -> true | None -> false
end

module UseComponents = Graph.Components.Make (UsageGraph)

type module_data = {
  module_path : string;
  llmodule : llmodule;
  funcdef_count : int;
  globals : llvalue StringMap.t;
}

let load_module module_path =
  let ctxt = global_context () in
  let buf = MemoryBuffer.of_file module_path in
  let llmodule = Llvm_bitreader.parse_bitcode ctxt buf in
  MemoryBuffer.dispose buf;
  Llvm_analysis.assert_valid_module llmodule;

  (* It's necessary to name all values. TODO: shouldn't we make sure we don't collide with anything? *)
  fold_left_functions (fun () fn ->
    match is_declaration fn with true -> () | _ ->
    fold_left_params (fun acc param ->
      if value_name param = "" then set_value_name ("a" ^ string_of_int acc) param;
      acc+1
    ) 0 fn |> ignore;
    fold_left_blocks (fun acc blk ->
      if value_name (value_of_block blk) = "" then set_value_name ("b" ^ string_of_int acc) (value_of_block blk);
      fold_left_instrs (fun acc inst ->
        if value_name inst = "" then set_value_name ("v" ^ string_of_int acc) inst;
        acc+1
      ) (acc+1) blk
    ) 0 fn |> ignore
  ) () llmodule;

  { module_path;
    llmodule;
    funcdef_count = fold_left_functions (fun count fn -> if is_declaration fn then count else count+1) 0 llmodule;
    globals =
      let f map x = StringMap.add (value_name x) x map in
      fold_left_functions f (fold_left_globals f StringMap.empty llmodule) llmodule;
  }

let process_module : 'a . module_data -> init:'a -> f:('a -> string -> 'a) -> 'a = fun moddat ~init ~f ->
  let init = f init @@ Printf.sprintf "(*\n * %S\n *)" moddat.module_path in

  let handle_function letand f init fn =
    (* if moddat.funcdef_count > 1000 && counter > 0 && counter*100/moddat.funcdef_count <> (counter-1)*100/moddat.funcdef_count then
      Printf. "%d%%%! " (counter*100/moddat.funcdef_count); *)
    let fn_ty = element_type @@ type_of fn in
    let fg = FunctionGraph.make fn in
    let idom = FuncDominator.compute_idom fg @@ FunctionGraph.entry fg in
    let dom_tree = FuncDominator.idom_to_dom_tree fg idom in
    let args = if is_var_arg fn_ty then ["(varargs : "^runtime_module^".polyval list)"] else [] in
    let args = fold_right_params (fun arg acc -> ("(" ^ my_instr_name arg ^ " : " ^ Value.typename_for (type_of arg) ^ ")") :: acc) fn args in
    let args = match args with [] -> ["()"] | x -> x in
    let init =
      f init (letand ^ my_function_name fn ^ " " ^ String.concat " " args ^ " : " ^ Value.typename_for (return_type fn_ty) ^ " =")
    in
    let init = f init ("  let rec _alloca = ref []") in
    let init =
      let rec gen_block init indent name =
        let llb = FunctionGraph.block_of_key fg name in
        let init = f init (indent ^ "and " ^ name ^ " " ^ phinode_argparams llb ^ " =") in
        let init = fold_left_instrs (fun init lli ->
          (* let comment = (indent ^ "  (* " ^ String.trim (string_of_llvalue lli) ^ " *)") in *)
          if is_terminator lli
          then
            match dom_tree name with
              | [] ->
                (* let init = f init comment in *)
                f init (indent ^ "  " ^ instruction lli)
              | l ->
                let init = f init (indent ^ "  let rec __ = ()") in
                let init = List.fold_left (fun init suc -> gen_block init (indent ^ "  ") suc) init l in
                (* let init = f init comment in *)
                f init (indent ^ "  in " ^ instruction lli)
          else
            match instruction lli with
            | "()" -> init
            | s ->
              (* let init = f init comment in *)
              f init (indent ^ "  " ^ s)
        ) init llb in
        init
      in
      gen_block init "  " @@ FunctionGraph.entry fg
    in
    let init = f init ("  in " ^ my_block_name (entry_block fn) ^ " ()") in
    if only_function_call_usage fn then init else
    f init ("and " ^ my_function_pointer_name fn ^ " = lazy (R.funptr_register \""^my_function_name fn^"\" " ^ parens (Value.make_polyfunc fn_ty @@ my_function_name fn) ^ ")")
  and handle_globalvar letand f init globl = try
    (* is_global_constant
    is_thread_local/thread_local_mode
    is_externally_initialized *)
    let llv = global_initializer globl in
    let bytes = Value.encode_value_s_bytes (type_of llv) (read_llvalue (object
      inherit llvalue_helper
      method! global_variable llv = Value.Source (my_global_name llv)
      method! function_value llv = Value.Source ("Lazy.force " ^ my_function_pointer_name llv)
      method! private unhandled llv = failwith ("unsupported value kind " ^ string_of_valuekind (classify_value llv) ^ " in global " ^ value_name globl)
    end) llv) in
    f init (letand ^ my_global_name globl ^ " = R.alloc_bytes @@ " ^ bytes)
  with e -> (Printf.eprintf "%s\n" @@ string_of_llvalue globl; reraise e)
  in

  let handle letand f init llv =
    (* TODO: call 'linkage', only expose exported symbols or something? *)
    match is_declaration llv with true -> init | _ ->
    match classify_value llv with
    | Function -> handle_function letand f init llv
    | GlobalVariable -> handle_globalvar letand f init llv
    | GlobalAlias -> assert false (* what are these? *)
    | _ -> assert false
  in

  (* This topo-sorts definitions into recursive groups. *)
  let usage_graph = UsageGraph.make moddat.llmodule in
  let sccs = UseComponents.scc_array usage_graph in
  Array.fold_left (fun init globals ->
    let vllv = UsageGraph.get_llvalue usage_graph in
    match globals with
    | [] -> init
    | [hd] ->
      let llv = vllv hd in
      let can_skip_rec =
        not (UsageGraph.self_loop usage_graph hd) &&
        match classify_value llv with
        | Function -> only_function_call_usage llv
        | _ -> true
      in
      handle (if can_skip_rec then "let " else "let rec ") f init llv
    | hd::tl ->
      let init = handle "let rec " f init (vllv hd) in
      List.fold_left (fun init x -> handle "and " f init (vllv x)) init tl
  ) init sccs

let main argv =
  let moddat = load_module argv.(1) in

  print_endline ("module BigInt = struct");
  print_endline [%blob "BigInt.ml"];
  print_endline "end";
  print_endline ("module "^runtime_module^" = struct");
  print_endline [%blob "runtime.ml"];
  print_endline "end";
  print_endline "module T : sig val run : unit -> unit end = struct";

  let missing_externs = StringMap.fold (fun key llv acc ->
      match is_declaration llv with false -> acc | true ->
      if (match classify_value llv with Function -> is_intrinsic llv | _ -> false)
      then (
        make_intrinsic llv |> print_endline; acc
      ) else (
        match make_missing_extern llv with
        | Some s -> print_endline s; acc
        | None -> key :: acc
      )
    ) moddat.globals []
  in

  process_module moddat ~init:() ~f:(fun () -> print_endline);

  print_endline ("let run () = print_endline \"starting "^moddat.module_path^"\";");

  let ifglobal name ?(default = (fun () -> ())) f =
    match StringMap.find_opt name moddat.globals with
    | Some llv -> f llv
    | None -> default ()
  in

  let sgarrlen llv = string_of_int @@ array_length @@ element_type @@ type_of llv in

  ifglobal "llvm.global_ctors"
    (fun llv -> print_endline ("  "^runtime_module^".run_ctors "^my_global_name llv^" "^sgarrlen llv^";"));
  ifglobal "main"
    (fun llv -> print_endline ("  let () = "^runtime_module^".start_main "^my_function_name llv^" f_exit in"));
  ifglobal "llvm.global_dtors"
    (fun llv -> print_endline ("  "^runtime_module^".run_dtors "^my_global_name llv^" "^sgarrlen llv^";"));
  print_endline ("  R.exit 0");

  print_endline "end";
  print_endline "let () = T.run ()";

  match missing_externs with
  | [] -> ()
  | _ -> Printf.eprintf "%s\n" "Missing externs:";
    List.iter (Printf.eprintf "%s\n") missing_externs

let () = main Sys.argv

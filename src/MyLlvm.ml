open Llvm

let string_of_valuekind : ValueKind.t -> string = function
  | NullValue -> "NullValue"
  | Argument -> "Argument"
  | BasicBlock -> "BasicBlock"
  | InlineAsm -> "InlineAsm"
  | MDNode -> "MDNode"
  | MDString -> "MDString"
  | BlockAddress -> "BlockAddress"
  | ConstantAggregateZero -> "ConstantAggregateZero"
  | ConstantArray -> "ConstantArray"
  | ConstantDataArray -> "ConstantDataArray"
  | ConstantDataVector -> "ConstantDataVector"
  | ConstantExpr -> "ConstantExpr"
  | ConstantFP -> "ConstantFP"
  | ConstantInt -> "ConstantInt"
  | ConstantPointerNull -> "ConstantPointerNull"
  | ConstantStruct -> "ConstantStruct"
  | ConstantVector -> "ConstantVector"
  | Function -> "Function"
  | GlobalAlias -> "GlobalAlias"
  | GlobalIFunc -> "GlobalIFunc"
  | GlobalVariable -> "GlobalVariable"
  | UndefValue -> "UndefValue"
  | Instruction _ -> "Instruction"
  | _ -> "Unknown ValueKind"

let string_of_typekind : TypeKind.t -> string = function
  | Void -> "Void"
  | Half -> "Half"
  | Float -> "Float"
  | Double -> "Double"
  | X86fp80 -> "X86fp80"
  | Fp128 -> "Fp128"
  | Ppc_fp128 -> "Ppc_fp128"
  | Label -> "Label"
  | Integer -> "Integer"
  | Function -> "Function"
  | Struct -> "Struct"
  | Array -> "Array"
  | Pointer -> "Pointer"
  | Vector -> "Vector"
  | Metadata -> "Metadata"
  | X86_mmx -> "X86_mmx"
  | Token -> "Token"
  | _ -> "Unknown TypeKind"

let is_aggregate_type llty = match classify_type llty with
  | Struct | Array | Vector -> true
  | _ -> false

let aggregate_length llty = match classify_type llty with
  | Struct -> Array.length @@ struct_element_types llty
  | Array -> array_length llty
  | Vector -> vector_size llty
  | _ -> assert false

(* Iterate over the non-aggregate contained types of llty. *)
let rec fold_flat_subtypes ~f ~init llty =
  match classify_type llty with
  | Struct -> Array.fold_left (fun acc ty -> fold_flat_subtypes ~f ~init:acc ty) init (struct_element_types llty)
  | Array | Vector ->
    let ty = element_type llty in
    let acc = ref init in
    for _ = 1 to aggregate_length llty do
      acc := f (!acc) ty
    done;
    !acc
  | _ -> f init llty

let string_of_opcode : Opcode.t -> string = function
  | Invalid -> "Invalid"
  | Ret -> "Ret"
  | Br -> "Br"
  | Switch -> "Switch"
  | IndirectBr -> "IndirectBr"
  | Invoke -> "Invoke"
  | Invalid2 -> "Invalid2"
  | Unreachable -> "Unreachable"
  | Add -> "Add"
  | FAdd -> "FAdd"
  | Sub -> "Sub"
  | FSub -> "FSub"
  | Mul -> "Mul"
  | FMul -> "FMul"
  | UDiv -> "UDiv"
  | SDiv -> "SDiv"
  | FDiv -> "FDiv"
  | URem -> "URem"
  | SRem -> "SRem"
  | FRem -> "FRem"
  | Shl -> "Shl"
  | LShr -> "LShr"
  | AShr -> "AShr"
  | And -> "And"
  | Or -> "Or"
  | Xor -> "Xor"
  | Alloca -> "Alloca"
  | Load -> "Load"
  | Store -> "Store"
  | GetElementPtr -> "GetElementPtr"
  | Trunc -> "Trunc"
  | ZExt -> "ZExt"
  | SExt -> "SExt"
  | FPToUI -> "FPToUI"
  | FPToSI -> "FPToSI"
  | UIToFP -> "UIToFP"
  | SIToFP -> "SIToFP"
  | FPTrunc -> "FPTrunc"
  | FPExt -> "FPExt"
  | PtrToInt -> "PtrToInt"
  | IntToPtr -> "IntToPtr"
  | BitCast -> "BitCast"
  | ICmp -> "ICmp"
  | FCmp -> "FCmp"
  | PHI -> "PHI"
  | Call -> "Call"
  | Select -> "Select"
  | UserOp1 -> "UserOp1"
  | UserOp2 -> "UserOp2"
  | VAArg -> "VAArg"
  | ExtractElement -> "ExtractElement"
  | InsertElement -> "InsertElement"
  | ShuffleVector -> "ShuffleVector"
  | ExtractValue -> "ExtractValue"
  | InsertValue -> "InsertValue"
  | Fence -> "Fence"
  | AtomicCmpXchg -> "AtomicCmpXchg"
  | AtomicRMW -> "AtomicRMW"
  | Resume -> "Resume"
  | LandingPad -> "LandingPad"
  | AddrSpaceCast -> "AddrSpaceCast"
  | CleanupRet -> "CleanupRet"
  | CatchRet -> "CatchRet"
  | CatchPad -> "CatchPad"
  | CleanupPad -> "CleanupPad"
  | CatchSwitch -> "CatchSwitch"
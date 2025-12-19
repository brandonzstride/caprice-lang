
(*
  The `Atom_cell` is the payload of int and bool values.
  It is expected to be identity or a pair of concrete and
  symbolic components.
*)
module Make (Atom_cell : Utils.Comparable.P1) = struct
  type data = private Data [@@deriving eq, ord]
  type typeval = private Typeval [@@deriving eq, ord]
  type neither = private Neither [@@deriving eq, ord]

  (* symbols to identify lazy things *)
  type symbol = { id : int } [@@unboxed] [@@deriving eq, ord]

  module SymbolMap = Baby.H.Map.Make (struct
    type t = symbol [@@deriving eq, ord]
  end)

  (*
    Data values and type values are all the same type constructor
    so that they are flat, and there is no pointer indirection.
    We can pack them into the same type in an unboxed way. This way,
    the representation is as if they are all just one type.
  *)
  type _ t =
    (* non-type value *)
    | VUnit : data t
    | VInt : int Atom_cell.t -> data t
    | VBool : bool Atom_cell.t -> data t
    | VFunClosure : { param : Ident.t ; closure : Ast.t closure } -> data t
    | VVariant : any Variant.t -> data t
    | VRecord : any Record.t -> data t
    | VModule : any Record.t -> data t (* TODO: consider merging with record *)
    | VTuple : any * any -> data t
    | VFunFix : { fvar : Ident.t ; param : Ident.t ; closure : Ast.t closure } -> data t (* no mutual recursion yet *)
    | VEmptyList : data t
    | VListCons : any * data t -> data t
    (* generated values *)
    | VGenFun : (typeval t, fun_cod) Funtype.t -> data t
    | VGenPoly : { id : int ; nonce : int } -> data t
    | VLazy : symbol -> neither t (* lazily evaluated thing, so state must manage this *)
    (* type values only *)
    | VType : typeval t
    | VTypePoly : { id : int } -> typeval t
    | VTypeUnit : typeval t
    | VTypeTop : typeval t
    | VTypeBottom : typeval t
    | VTypeInt : typeval t
    | VTypeBool : typeval t
    | VTypeMu : { var : Ident.t ; closure : Ast.t closure } -> typeval t
    | VTypeList : typeval t -> typeval t
    | VTypeFun : (typeval t, fun_cod) Funtype.t -> typeval t
    | VTypeRecord : typeval t Record.t -> typeval t
    | VTypeModule : Labels.Record.t Ast.typed_item list closure -> typeval t (* not eagerly evaluting first label *)
    | VTypeVariant : typeval t Labels.Variant.Map.t -> typeval t
    | VTypeRefine : (typeval t, Ast.t closure) Refinement.t -> typeval t
    | VTypeTuple : typeval t * typeval t -> typeval t
    | VTypeSingle : typeval t -> typeval t

  and 'a closure = { captured : 'a ; env : env }

  and env = any Env.t

  and fun_cod =
    | CodValue of typeval t (* regular function codomain *)
    | CodDependent of Ident.t * Ast.t closure (* dependent function codomain *)
  
  and lazy_v =
    | LGenList of typeval t
    | LGenMu of { var : Ident.t ; closure : Ast.t closure }
    | LValue of any

  and any = Any : 'a t -> any [@@unboxed]

  module Env = Env.Make (struct type t = any end)

  type dval = data t
  type tval = typeval t

  let[@inline always] to_any : type a. a t -> any = fun v -> Any v

  type 'b f = { f : 'a. 'a t -> 'b } [@@unboxed]

  let[@inline always] map_any : 'a f -> any -> 'a = fun f (Any v) -> f.f v

  let[@inline always] handle (type a b) (v : a t) ~(data : data t -> b) ~(typeval : typeval t -> b) : b =
    match v with
    | ( VUnit
      | VInt _
      | VBool _
      | VFunClosure _
      | VVariant _
      | VRecord _
      | VModule _
      | VTuple _
      | VFunFix _
      | VEmptyList
      | VListCons _
      | VGenFun _
      | VGenPoly _) as x -> data x
    | ( VType
      | VTypePoly _
      | VTypeUnit 
      | VTypeTop
      | VTypeBottom
      | VTypeInt
      | VTypeBool
      | VTypeMu _
      | VTypeList _
      | VTypeFun _
      | VTypeRecord _
      | VTypeModule _
      | VTypeVariant _
      | VTypeRefine _
      | VTypeTuple _
      | VTypeSingle _) as x -> typeval x
    | VLazy _ -> failwith "Invariant failure: handling unforced lazy value as data or type"

  let[@inline always] handle_any (type a) (v : any) ~(data : data t -> a) ~(typeval : typeval t -> a) : a =
    map_any { f = handle ~data ~typeval } v

  (* Some setup to write intensional equality *)
  (* let rec equal : type a. a t -> a t -> bool = fun a b ->
    match a, b with
    | VUnit, VUnit
    | VInt, Vint
    | VBool, VBool
    | VFunClosure, VFunClosure
    | VVariant, VVariant
    | VRecord, VRecord
    | VTuple, VTuple
    | VFunFix, VFunFix
    (* generated values *)
    | VGenFun, VGenFun
    | VGenPoly, VGenPoly
    (* type values only *)
    | VType, VType
    | VTypePoly, VTypePoly
    | VTypeUnit, VTypeUnit
    | VTypeTop, VTypeTop
    | VTypeBottom, VTypeBottom
    | VTypeInt, VTypeInt
    | VTypeBool, VTypeBool
    | VTypeMu, VTypeMu
    | VTypeFun, VTypeFun
    | VTypeRecord, VTypeRecord
    | VTypeVariant, VTypeVariant
    | VTypeRefine, VTypeRefine
    | VTypeTuple, VTypeTuple -> failwith "need to do" *)

  let rec to_string : type a. a t -> string = function
    | VUnit ->
      "()"
    | VInt i ->
      Atom_cell.to_string Int.to_string i
    | VBool b ->
      Atom_cell.to_string Bool.to_string b
    | VFunClosure { param ; closure = _ } ->
      Format.sprintf "(fun %s -> <closure>)" (Ident.to_string param)
    | VVariant { label ; payload } -> 
      Format.sprintf "(%s %s)" (Labels.Variant.to_string label) (any_to_string payload)
    | VRecord map_body ->
      Labels.Record.Map.to_list map_body
      |> List.map (fun (key, data) -> Format.sprintf "%s = %s" (Labels.Record.to_string key) (any_to_string data))
      |> String.concat " ; "
      |> Format.sprintf "{ %s }"
    | VModule map_body ->
      Labels.Record.Map.to_list map_body
      |> List.map (fun (key, data) -> Format.sprintf "let %s = %s" (Labels.Record.to_string key) (any_to_string data))
      |> String.concat "\n"
      |> Format.sprintf "struct %s end"
    | VTuple (v1, v2) ->
      Format.sprintf "(%s, %s)" (any_to_string v1) (any_to_string v2)
    | VFunFix { fvar ; param ; closure = _ } ->
      Format.sprintf "(fix %s(%s). <closure>)" (Ident.to_string fvar) (Ident.to_string param)
    | VEmptyList ->
      "[]"
    | VListCons (hd, tl) ->
      Format.sprintf "(%s :: %s)" (any_to_string hd) (to_string tl)
    | VGenFun funtype ->
      Format.sprintf "G(%s)" (to_string (VTypeFun funtype))
    | VGenPoly { id ; nonce } ->
      Format.sprintf "G(poly id : %d, nonce : %d)" id nonce
    | VLazy { id } ->
      Format.sprintf "Lazy(id : %d)" id
    | VType ->
      "type"
    | VTypePoly { id } ->
      Format.sprintf "(poly id : %d)" id
    | VTypeUnit ->
      "unit"
    | VTypeTop ->
      "top"
    | VTypeBottom ->
      "bottom"
    | VTypeInt ->
      "int"
    | VTypeBool -> 
      "bool"
    | VTypeMu { var ; closure = _ } ->
      Format.sprintf "(mu %s. <closure>)" (Ident.to_string var)
    | VTypeList t ->
      Format.sprintf "(list %s)" (to_string t)
    | VTypeFun { domain ; codomain } ->
      begin match codomain with
      | CodValue cod_tval -> Format.sprintf "%s -> %s" (to_string domain) (to_string cod_tval)
      | CodDependent (id, _closure) -> Format.sprintf "(%s : %s) -> <closure>" (Ident.to_string id) (to_string domain)
      end
    | VTypeRecord map_body ->
      if Labels.Record.Map.is_empty map_body then "{:}" else
      Labels.Record.Map.to_list map_body
      |> List.map (fun (key, data) -> Format.sprintf "%s : %s" (Labels.Record.to_string key) (to_string data))
      |> String.concat " ; "
      |> Format.sprintf "{ %s }"
    | VTypeModule _ ->
      failwith "Unimplemented module type to string"
    | VTypeVariant map_body ->
      Labels.Variant.Map.to_list map_body
      |> List.map (fun (key, data) -> Format.sprintf "%s of %s" (Labels.Variant.to_string key) (to_string data))
      |> String.concat "\n"
      |> Format.sprintf "(%s)"
    | VTypeRefine { var ; tau ; predicate = _closure } ->
      Format.sprintf "{ %s : %s | <closure> }" (Ident.to_string var) (to_string tau)
    | VTypeTuple (t1, t2) ->
      Format.sprintf "(%s * %s)" (to_string t1) (to_string t2)
    | VTypeSingle t ->
      Format.sprintf "(singletype %s)" (to_string t)

  and any_to_string any = map_any { f = to_string } any

  module Error_messages = struct
    let refutation (v : any) (t : tval) : string =
      Format.sprintf "Refutation: %s does not have type %s"
        (any_to_string v) (to_string t)

    let bad_binop (v1 : any) (op : Binop.t) (v2 : any) : string =
      Format.sprintf "Bad binop: %s %s %s"
        (any_to_string v1) (Binop.to_string op) (any_to_string v2)

    let apply_non_function (v : any) : string =
      Format.sprintf "Bad application: %s is not a function"
        (any_to_string v)

    let missing_pattern (v : any) (patterns : Pattern.t list) : string =
      List.map Pattern.to_string patterns
      |> String.concat " | "
      |> Format.sprintf "Bad match: %s is not in pattern list %s" (any_to_string v)

    let missing_label (v : any) (label : Labels.Record.t) : string =
      Format.sprintf "Missing label: %s does not have label %s"
        (any_to_string v) (Labels.Record.to_string label)

    let project_non_record (v : any) (label : Labels.Record.t) : string =
      Format.sprintf "Bad projection: %s is not a record/module; tried to project label %s"
        (any_to_string v) (Labels.Record.to_string label)

    let cons_non_list (v_hd : any) (v_tl : any) : string =
      Format.sprintf "Bad cons: tried to put %s on front of %s, which is not a list"
        (any_to_string v_hd) (any_to_string v_tl)

    let not_non_bool (v : any) : string =
      Format.sprintf "Bad not: %s is not a boolean and cannot be negated"
        (any_to_string v)
      
    let if_non_bool (v : any) : string =
      Format.sprintf "Bad if: %s is not a boolean and cannot be used as a condition"
        (any_to_string v)

    let assert_non_bool (v : any) : string =
      Format.sprintf "Bad assert: %s is not a boolean and cannot be used for an assertion"
        (any_to_string v)

    let assume_non_bool (v : any) : string =
      Format.sprintf "Bad assume: %s is not a boolean and cannot be used for an assumption"
        (any_to_string v)

    let non_type_value (v : data t) : string =
      Format.sprintf "Bad type: %s is expected to be a type value"
        (to_string v)

    let non_bool_predicate (v : any) : string =
      Format.sprintf "Bad predicate: the refinement predicate %s is expected to be a boolean"
        (any_to_string v)
  end

  module Match_result = struct
    type t =
      | Match
      | Match_bindings of env
      | No_match
      | Failure of string
  end

  let rec matches : type a. Pattern.t -> a t -> Match_result.t = fun p v ->
    match p, v with
    | PAny, _ -> Match
    | PVariable id, v -> Match_bindings (Env.singleton id (to_any v))
    | p, VGenPoly _ -> 
      (* generated polymorphic values cannot be inspected *)
      Failure (Format.sprintf "Bad match: matching polymorphic value with pattern %s" (Pattern.to_string p))
    | PVariant { label = pattern_label ; payload = payload_pattern },
      VVariant { label = subject_label ; payload = Any v } ->
        if Labels.Variant.equal pattern_label subject_label
        then matches payload_pattern v
        else No_match
    | PTuple (p1, p2), VTuple (Any v1, Any v2) ->
      match_two (p1, v1) (p2, v2)
    | PEmptyList, VEmptyList -> Match
    | PDestructList (p1, p2), VListCons (Any v1, v2) ->
      match_two (p1, v1) (p2, v2)
    | _ -> No_match

  and match_two : type a b. Pattern.t * a t -> Pattern.t * b t -> Match_result.t = fun (p1, v1) (p2, v2) ->
    match matches p1 v1 with
    | (No_match | Failure _) as r -> r
    | Match -> matches p2 v2
    | Match_bindings e1 ->
      begin match matches p2 v2 with
      | (No_match | Failure _) as r -> r
      | Match -> Match_bindings e1
      | Match_bindings e2 -> Match_bindings (Env.extend e1 e2)
      end

  let matches_any : Pattern.t -> any -> Match_result.t = fun pat a ->
    let f (type a) (v : a t) : Match_result.t =
      matches pat v
    in
    map_any { f } a
end

(*
  Ints and bools have only a concrete component.
*)
module Concrete = Make (Utils.Identity)

include Concrete

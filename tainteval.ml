open Core_kernel.Std
open Bap.Std

module Seq = Sequence

exception Abort of string

module Taint = struct
  module T = struct
    type t = (string * int) with sexp
    let alloc = ref (-1)
    let fresh name = alloc := !alloc + 1; (name, !alloc)
    let compare (_, x) (_, y) = compare x y
    let to_string (name,i) = sprintf "%s:%d" name i
  end
  include T
  include Comparable.Make(T)
end

(** Given 8*n, return n.
  * useful for operating on memory. *)
let bits_to_bytes n =
  if n mod 8 <> 0 then raise (Abort "Width should be multiple of 8.")
  else n / 8

module Mem = Addr.Map

module T = struct
  type t =
    | BV of Bitvector.t * Taint.Set.t
    | Mem of memory
    | Un of string * typ * Taint.Set.t
  and memory = t Mem.t
  with compare, sexp

  let to_string x = Sexp.to_string (sexp_of_t x)

  let hash = Hashtbl.hash

  open Format
  let rec pp fmt = function
    | Un (n,typ,_) -> fprintf fmt "Un[%s]:%a" n Type.pp typ
    | BV (v,_) -> Bitvector.pp fmt v
    | Mem m ->
      fprintf fmt "@[<v0>%a@]" pp_list (Mem.to_alist m)
  and pp_list fmt = function
    | [] -> ()
    | (a,v) :: ms ->
      fprintf fmt "%a: %a@;%a" Addr.pp a pp v pp_list ms
end

include T

type value = T.t
with compare, sexp

(** Represents memory.
  * Supports: load and store byte sequences. *)
module Memory = struct
  type t = memory
  let empty = Mem Mem.empty
  let of_image i =
    let tbl = Image.words i `r8 in
    Mem (Table.foldi tbl ~init:Mem.empty ~f:(fun mem v m ->
        Mem.add m ~key:(Memory.min_addr mem) ~data:(BV(v, Taint.Set.empty))))
  let load ~mem ~idx endianness sz = match mem, idx with
    | (Mem mem, BV (idx, idx_taint)) ->
      if Mem.is_empty mem then None
      else
        let bytes = Size.to_bytes sz in
        let max = Addr.(idx ++ Int.(bytes - 1)) in
        let data =
          List.map ~f:snd (Mem.range_to_alist mem ~min:idx ~max) in
        if List.length data = bytes then
          let data = match endianness with
            | LittleEndian -> List.rev data
            | BigEndian ->  data in
          List.fold data ~init:None
            ~f:(fun a b -> match (a, b) with
                | Some (BV (a, a_t)), (BV (b, b_t)) -> Some (BV (Word.(a @. b), Taint.Set.union a_t b_t))
                | _, (BV (i, i_t)) -> Some (BV (i, Taint.Set.union i_t idx_taint))
                | _ -> None)
        else None
    | (Mem _, (Un (_, _, _) as un)) -> Some un
    | (_, _) -> raise (Abort "Memory or index has wrong type.")


  let store ~mem ~idx ~data:v endianness sz = match mem, idx, v with
    | (Mem mem, BV (idx, idx_t), BV (v, v_t)) ->
      let v = Word.to_bytes v endianness in
      let t = Taint.Set.union idx_t v_t in
      let (ret, _) = Seq.fold v ~init:(mem, idx)
          ~f:(fun (mem, i) byte ->
              (Mem.add mem ~key:i ~data:(BV (byte, t))),
              Word.(i ++ 1))
      in
      Mem ret
    | (Mem mem, BV (idx, i_t), Un (u_x, u_y, u_t)) ->
      let ret = ref mem in
      let ii = ref idx in
      let t = Taint.Set.union i_t u_t in
      for _ = 1 to Size.to_bytes sz do
        ret := Mem.add !ret ~key:!ii ~data:(Un(u_x, u_y, t));
        ii :=  Word.(!ii ++ 1);
      done;
      Mem !ret
    | (Mem mem, Un (_, _, _), _) ->
      print_endline "Warning: writing to unknown memory index";
      Mem mem
    | (_, _, _) -> raise (Abort "Memory, index, or value has wrong type.")
end

let bv_var var n = match Var.typ var with
  | Type.Imm sz -> Bitvector.of_int n ~width:sz
  | Type.Mem _ -> failwith "Tried to create mem bv"

module State = struct
  module StateMap = Var.Map
  type vm = T.t StateMap.t with compare, sexp 
  type t = (vm * Image.t)
  let to_string (x, _) = Sexp.to_string (sexp_of_vm x)
  let of_image i = (StateMap.empty, i) 
  let move (m, i) var va = (StateMap.add m ~key:var ~data:va, i)
  let peek_exn (s,i) v = 
    let is_mem = function
      | Type.Mem(_,_) -> true
      | _ -> false in
    match StateMap.find s v with
    | Some x -> x
    | None when is_mem (Var.typ v) -> Memory.of_image i
    | None -> BV (bv_var v 0, Taint.Set.empty)
  let peek (s,_) = StateMap.find

  (** Remove all temporary variables from a state. *)
  let remove_tmp (state,i) =
    (StateMap.filter state ~f:(fun ~key:k ~data:_ -> not (Var.is_tmp k)), i)

  let taint (s,i) var t = (
    match StateMap.find s var with
    | Some (BV(v, t0)) -> StateMap.add s var (BV(v, (Taint.Set.union t t0)))
    | None -> let neg1 = bv_var var (-1) in
      StateMap.add s var (BV(neg1, t))
    | Some (Un(x, y, t0)) -> StateMap.add s var (Un(x, y, Taint.Set.union t t0))
    | Some (Mem _) -> raise (Abort "Tried to taint all of memory")), i
end

type state = State.t

(** If v is a bitvector, perform some action on it.
  * Otherwise, handle the other value. *)
let bv_action_or_unknown v action =
  match v with
  | Mem _ -> raise (Abort "Operation cannot be performed on memory.")
  | Un (_,_,_) -> v
  | BV (v,t) -> action v t


module Z = Bitvector.Int_exn

(** Handle a unary operator. *)
let handle_unop op v =
  let open Exp.Unop in bv_action_or_unknown v
    (fun v t -> match op with
       | NEG -> BV (Z.neg v, t)
       | NOT -> BV (Z.lnot v, t))



(** Handle a binary operator. *)
let handle_binop op l r : value =
  let open Exp.Binop in
  match (l, r) with
  | (Mem _, _) | (_, Mem _) ->
    raise (Abort "Operation cannot be performed on memory.")
  | (Un (a, b, t), _) | (_, Un (a, b, t)) -> Un (a, b, t)
  | (BV (l, l_t), BV (r, r_t)) ->
    let lift_bool op x y =
      if (op x y) then Z.one else Z.zero in
    let signed op x y = op (Word.signed x) y in
    let op = match op with
      | PLUS    -> Z.add
      | MINUS   -> Z.sub
      | TIMES   -> Z.mul
      | DIVIDE  -> Z.div
      | SDIVIDE -> signed Z.div
      | MOD     -> Z.modulo
      | SMOD    -> signed Z.modulo
      | LSHIFT  -> Z.lshift
      | RSHIFT  -> Z.rshift
      | ARSHIFT -> Z.arshift
      | AND     -> Z.logand
      | OR      -> Z.logor
      | XOR     -> Z.logxor
      | EQ      -> lift_bool Bitvector.(=)
      | NEQ     -> lift_bool Bitvector.(<>)
      | LT      -> lift_bool Bitvector.(<)
      | LE      -> lift_bool Bitvector.(<=)
      | SLT     -> lift_bool Bitvector.(<=)
      | SLE     -> lift_bool Bitvector.(<=) in
    BV (op l r, Taint.Set.union l_t r_t)

let handle_cast cast_kind size v =
  let open Exp.Cast in
  let hi = size - 1 in
  let cast v = match cast_kind with
    | UNSIGNED -> Word.extract_exn ~hi v
    | SIGNED   -> Word.extract_exn ~hi (Word.signed v)
    | HIGH     -> Word.extract_exn ~lo:(Word.bitwidth v - size) v
    | LOW      -> Word.extract_exn ~hi v in
  bv_action_or_unknown v (fun v t -> BV (cast v, t))

(** Given state, evaluate a single BIL expression. *)
let rec eval_exp state exp =
  let result = match exp with
    | Bil.Load (arr, idx, endian, t) ->
      (match Memory.load (eval_exp state arr) (eval_exp state idx) endian t with
       | Some v -> v
       | None -> Un ("Load from uninitialized memory",
                     Type.imm Size.(to_bits t), Taint.Set.empty))
    | Bil.Store (arr, idx, v, endian, t) ->
      Memory.store (eval_exp state arr) (eval_exp state idx) (eval_exp state v)
        endian t
    | Bil.BinOp (op, l, r) -> handle_binop op (eval_exp state l) (eval_exp state r)
    | Bil.UnOp (op, v) -> handle_unop op (eval_exp state v)
    | Bil.Var v -> State.peek_exn state v
    | Bil.Int v -> BV (v, Taint.Set.empty)
    | Bil.Cast (cast_kind, new_type, v) ->
      handle_cast cast_kind new_type (eval_exp state v)
    | Bil.Let (v, a, b) -> (* FIXME Should there be typechecking done here? *)
      let state = State.move state v (eval_exp state a) in
      eval_exp state b
    | Bil.Unknown (str, typ) -> Un (str, typ, Taint.Set.empty)
    | Bil.Ite (cond, t_case, f_case) ->
      bv_action_or_unknown (eval_exp state cond)
        (fun v _ ->
           let case = if Word.is_zero v then f_case else t_case in
           eval_exp state case)
    | Bil.Extract (hi, lo, v) -> bv_action_or_unknown (eval_exp state v)
                                   (fun v t -> BV (Word.extract_exn ~hi ~lo v, t))
    | Bil.Concat (l, r) -> (match eval_exp state l, eval_exp state r with
        | (Mem _, _) | (_, Mem _) ->
          raise (Abort "Operation cannot be performed on memory.")
        | ((Un (_, _, _) as un), _) | (_, (Un (_, _, _) as un)) -> un
        | (BV (l, l_t), BV (r, r_t)) -> BV (Bitvector.concat l r, Taint.Set.union l_t r_t))
  in result

(** Take a detailed state and a BIL statement and yield the successor state and
  * a location to jump to, if any. *)
let rec eval_stmt taint_stack state =
  let taint_head = List.hd_exn taint_stack in
  let open Stmt in function
    | Move (v, exp) -> [(State.move state v (eval_exp state exp)), None], Taint.Set.empty
    | Jmp (exp) -> [state, Some(eval_exp state exp)], taint_head
    | While (cond, stmts) ->
      (match eval_exp state cond with
       | Mem _ -> raise (Abort "Operation cannot be performed on memory.")
       | Un (_, _, _) -> raise (Abort "Condition in While loop is Unknown.")
       | BV (v, t) ->
         let taint_stack' = (Taint.Set.union taint_head t) :: taint_stack in
         if not(Word.is_zero v) then
           let (tgts, ts) = eval_stmt_list taint_stack' state stmts in
           let tgts' = List.concat @@ List.map tgts ~f:(fun (state, addr) -> 
               (match addr with
                | None -> fst @@ eval_stmt taint_stack' state (While (cond, stmts))
                | Some _ as jump_to -> [(state, jump_to)])) in
           (tgts', ts)
         else [state, None], Taint.Set.empty)
    | If (cond, t_case_stmts, f_case_stmts) ->
      let rec f v =
      (match v with
       | Mem _ ->
         raise (Abort "Operation cannot be performed on memory.")
       | Un (_, _, t) -> f @@ BV(Addr.of_int ~width:1 1, t)
       | BV (cond, t) ->
         printf "Tainted If, taint=%s\n" (String.concat (List.map (Taint.Set.to_list t) ~f:Taint.to_string) ~sep:",");
         let taint_stack' = (Taint.Set.union taint_head t) :: taint_stack in
         let (left_tgts, left_t) = eval_stmt_list taint_stack' state t_case_stmts in
         let (right_tgts, right_t) = eval_stmt_list taint_stack' state f_case_stmts in
         printf "Outtaint = %s\n"(String.concat (List.map (Taint.Set.to_list (Taint.Set.union left_t right_t)) ~f:Taint.to_string) ~sep:",");
         let double_taint = Taint.Set.union left_t right_t in
         if not @@ List.exists (left_tgts @ right_tgts) ~f:(fun (_, x) -> Option.is_some x)
           (* If this is not a control flow, take only one branch *)
           then if Word.is_zero cond
                then (right_tgts, right_t)
                else (left_tgts, left_t)
           (* If this is control flow, take both *)
           else (left_tgts @ right_tgts, Taint.Set.union left_t right_t))
      in f @@ eval_exp state cond
    | Special str ->
      raise (Abort (Printf.sprintf "Aborting with Special '%s'" str))
    | CpuExn i -> raise (Abort (Printf.sprintf "Aborting with CpuExn %d" i))
(** Helper function:
  * evaluate a list of BIL statements from a starting state. *)
and eval_stmt_list taint_stack state = function
  | [] -> [state, None], Taint.Set.empty
  | (hd::tl) -> let (tgts, taint) = eval_stmt taint_stack state hd in
    List.fold_left (List.map tgts ~f:(fun (state, addr) ->
        (match addr with
         | None -> eval_stmt_list taint_stack state tl
         | Some _ as jump_to -> [(state, jump_to)], taint))) ~f:(fun (tgts, ts) (atgts, ats) ->
        tgts @ atgts, Taint.Set.union ts ats) ~init:([], Taint.Set.empty)

(** Evaluate a list of instructions and discard temporary state,
  * as when evaluating an assembly instruction. *)
let eval_stmts state instructions =
  let (tgts, ts) = eval_stmt_list [Taint.Set.empty] state instructions in
  (List.map ~f:(fun (st, tgt) -> (State.remove_tmp st, tgt)) tgts, ts)

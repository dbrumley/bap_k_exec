open Core_kernel.Std
open Bap_types.Std

module Seq = Sequence

exception Abort of string

module Taint = struct
  module T = struct
    type t = (string * int) with sexp
    let alloc = ref (-1)
    let fresh name = alloc := !alloc + 1; (name, !alloc)
    let compare (_, x) (_, y) = compare x y
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

module State = struct
  module StateMap = Var.Map
  type t = T.t StateMap.t
  with compare, sexp

  let empty = StateMap.empty
  let move = StateMap.add
  let peek_exn = StateMap.find_exn
  let peek = StateMap.find

  (** Remove all temporary variables from a state. *)
  let remove_tmp state =
    StateMap.filter state ~f:(fun ~key:k ~data:_ -> not (Var.is_tmp k))

  let taint s var t =
    match StateMap.find s var with
      | Some (BV(v, t0)) -> StateMap.add s var (BV(v, (Taint.Set.union t t0)))
      | None -> let neg1 = (match Var.typ var with
                              | Imm sz -> Bitvector.of_int (-1) ~width:sz
                              | Mem _ -> raise (Abort "Tried to intro tainted memory")) in
                StateMap.add s var (BV(neg1, t))
      | Some (Un(x, y, t0)) -> StateMap.add s var (Un(x, y, Taint.Set.union t t0))
      | Some (Mem _) -> raise (Abort "Tried to taint all of memory")
end

type state = State.t
with compare, sexp

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
      let state = State.move  state ~key:v ~data:(eval_exp state a) in
      eval_exp state b
    | Bil.Unknown (str, typ) -> Un (str, typ, Taint.Set.empty)
    | Bil.Ite (cond, t_case, f_case) ->
      bv_action_or_unknown (eval_exp state cond)
        (fun v _ ->
           (* TODO taint ITE properly *)
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
    | Move (v, exp) -> (State.move ~key:v ~data:(eval_exp state exp) state), None
    | Jmp (exp) -> state, Some (taint_head, (eval_exp state exp))
    | While (cond, stmts) ->
      (match eval_exp state cond with
       | Mem _ -> raise (Abort "Operation cannot be performed on memory.")
       | Un (_, _, _) -> raise (Abort "Condition in While loop is Unknown.")
       | BV (v, t) ->
         let taint_stack' = (Taint.Set.union taint_head t) :: taint_stack in
         if not(Word.is_zero v) then
           let (state, addr) = (eval_stmt_list taint_stack' state stmts) in
           (match addr with
            | None -> eval_stmt taint_stack' state (While (cond, stmts))
            | Some _ as jump_to -> (state, jump_to))
         else (state, None))
    | If (cond, t_case_stmts, f_case_stmts) ->
      (match eval_exp state cond with
       | Mem _ ->
         raise (Abort "Operation cannot be performed on memory.")
       | Un (_, _, _) -> raise (Abort "Condition in If statement is Unknown.")
       | BV (v, t) ->
         let taint_stack' = (Taint.Set.union taint_head t) :: taint_stack in
         eval_stmt_list taint_stack' state
                   (if not(Bitvector.is_zero v) then t_case_stmts
                    else f_case_stmts))
    | Special str ->
      raise (Abort (Printf.sprintf "Aborting with Special '%s'" str))
    | CpuExn i -> raise (Abort (Printf.sprintf "Aborting with CpuExn %d" i))
(** Helper function:
  * evaluate a list of BIL statements from a starting state. *)
and eval_stmt_list taint_stack state = function
  | [] -> state, None
  | (hd::tl) -> let (state, addr) = eval_stmt taint_stack state hd in
    (match addr with
     | None -> eval_stmt_list taint_stack state tl
     | Some _ as jump_to -> (state, jump_to))

(** Evaluate a list of instructions and discard temporary state,
  * as when evaluating an assembly instruction. *)
let eval_stmts state instructions =
  let (state, addr) = eval_stmt_list [Taint.Set.empty] state instructions in
  (State.remove_tmp state, addr)
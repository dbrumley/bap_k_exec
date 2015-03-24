open Core_kernel.Std
open Bap.Std
open K_policy
open K_exec
open Bap_disasm_basic

module Loc = struct
  module T = struct
    type t = Reg of var
           | Mem of addr with sexp, compare
  end
  include T
  include Comparable.Make(T)
end

module Taint = Tainteval.Taint

type t = {
  path : addr list;
  source_addrs : Addr.Set.t;
  skip_addrs : Addr.Set.t;
  model : Tainteval.State.t;
  unchecked : Taint.Set.t;
}

let sym_pred image ~f =
  Image.symbols image |>
  Table.map ~f:Symbol.name |>
  Table.filter ~f |>
  Table.to_sequence |>
  Seq.map ~f:(fun (m,_) -> Memory.min_addr m)

let image_sources image =
  sym_pred image ~f:(String.is_suffix ~suffix:"error") |>
  Seq.fold ~init:Addr.Set.empty ~f:Addr.Set.add

let image_skips image =
  sym_pred image ~f:(String.is_suffix ~suffix:"printf") |>
  Seq.fold ~init:Addr.Set.empty ~f:Addr.Set.add

let init image = {
  path = [];
  source_addrs = image_sources image;
  skip_addrs = image_skips image;
  model = Tainteval.State.empty;
  unchecked = Taint.Set.empty;
}

let remarkable x = not @@ Taint.Set.is_empty x.unchecked

let to_addr_exn = function
  | Tainteval.BV(x, _) -> x
  | _ -> failwith "Not an addr"

let step addr insn bil (st : t trace_step) =
  let s = {st.state with path = addr::st.state.path} in
  let (m, otgt) = Tainteval.eval_stmts s.model bil in
  let s' = {s with model = m} in
  let r0 = Bap_disasm_arm_env.r0 in
  (* If the code takes a jump with a tainted condition, mark checked *)
  let st' = match otgt with
    | Some (ct, _) -> let unchecked = Taint.Set.diff s'.unchecked ct in
      {st with state = {s' with unchecked = unchecked}}
    | None -> {st with state = s'} in
  match otgt with
    (* Taint and skip tainted functions *)
    | Some(_,tgt) when Addr.Set.mem (s.source_addrs) @@ to_addr_exn tgt ->
      let ts = Taint.Set.singleton (Taint.fresh "any") in
      ({st with state = {s with model = Tainteval.State.taint s.model r0 ts}}, [], true)
    (* Skip skipped functions *)
    | Some(_,tgt) when Addr.Set.mem (s.skip_addrs) @@ to_addr_exn tgt -> (st', [], true)
    (* Follow normal instructions *)
    | Some(_,tgt) -> (st', [to_addr_exn tgt], false)
    | None -> (st', [], true)

let render x = String.concat (List.map x.path ~f:Addr.to_string) ~sep:"->"
let starts image =
  sym_pred image ~f:(String.is_prefix ~prefix:"checker")

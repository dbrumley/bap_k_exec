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

let remarkable x = true
(*not @@ Taint.Set.is_empty x.unchecked*)

let to_addr_exn = function
  | Tainteval.BV(x, _) -> x
  | x -> failwith @@ sprintf "Not an addr %s" @@ Tainteval.to_string x

let ts_to_str x = String.concat (List.map ~f:Taint.to_string (Taint.Set.to_list x)) ~sep:","

let step addr insn bil (st : t trace_step) =
  printf "Processing addr: %s\nTS: %s\n" (Addr.to_string addr) (ts_to_str st.state.unchecked); 
  let s = {st.state with path = addr::st.state.path} in
  let (tgts, ts) = Tainteval.eval_stmts s.model bil in
  printf "Jumptaint: %s\n" (ts_to_str ts);
  let s' = {s with unchecked = Taint.Set.diff s.unchecked ts} in
  let merge k = let (l, r) = List.unzip k in (List.concat l, List.concat r) in
  merge @@ List.map tgts ~f:(fun (m, otgt) ->
  let s' = {s' with model = m} in
  let st' = {st with state = s'} in
  let r0 = Bap_disasm_arm_env.r0 in
  match otgt with
    (* Unknown jump target *)
    (* TODO, check if insn is return, if so use callgraph for nexts *)
    | Some(Tainteval.Un(_,_,_)) -> ([], [{st' with term = true}])
    (* Taint and skip tainted functions *)
    | Some(tgt) when Addr.Set.mem (s.source_addrs) @@ to_addr_exn tgt ->
      print_endline "CREATING TAINT";
      let ts = Taint.Set.singleton (Taint.fresh "any") in
      ([], [{st' with state = {s with model = Tainteval.State.taint s.model r0 ts;
                                      unchecked = Taint.Set.union s.unchecked ts}}])
    (* Skip skipped functions *)
    | Some(tgt) when Addr.Set.mem (s.skip_addrs) @@ to_addr_exn tgt -> ([], [st'])
    (* Follow normal instructions *)
    | Some(tgt) -> printf "Jump Target: %s\n" (Addr.to_string @@ to_addr_exn tgt);
                   ([st', to_addr_exn tgt], [])
    | None -> ([], [st']))

let render x =
  let path = String.concat (List.rev_map x.path ~f:Addr.to_string) ~sep:"->" in
  let set = String.concat (List.map (Taint.Set.to_list x.unchecked) ~f:Taint.to_string) ~sep:"," in
  sprintf "Path: %s\nLive taint:%s\n" path set

let starts image =
  sym_pred image ~f:(String.is_prefix ~prefix:"checker")

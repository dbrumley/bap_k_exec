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

let err_funcs = ref String.Set.empty

let load filename =
  err_funcs := String.Set.of_list @@ In_channel.read_lines filename;
  String.Set.iter !err_funcs ~f:(fun n -> printf "Error function: %s\n" n)

type t = {
  path : addr list;
  source_addrs : Addr.Set.t;
  skip_addrs : Addr.Set.t;
  model : Tainteval.State.t;
  unchecked : Taint.Set.t;
}

let ida_syms = ref Table.empty

let sym_pred image ~f =
  !ida_syms |>
  Table.filter ~f |>
  Table.to_sequence |>
  Seq.map ~f:(fun (m,_) -> Memory.min_addr m)

let image_sources image =
  sym_pred image ~f:(String.Set.mem !err_funcs) |>
  Seq.iter ~f:(fun a -> printf "Taint source: %s\n" (Addr.to_string a));
  sym_pred image ~f:(String.Set.mem !err_funcs) |>
  Seq.fold ~init:Addr.Set.empty ~f:Addr.Set.add

let image_skips image =
  let (plt_mem, _) = Seq.find_exn (Memmap.to_sequence (Image.tags image)) ~f:(fun (_, (k, v)) -> (k = "section") && (v = ".plt")) in
  let min = Memory.min_addr plt_mem in
  let max = Memory.max_addr plt_mem in
  printf "PLT detected: %s to %s\n" (Addr.to_string min) (Addr.to_string max);
  (* Batteries has a -- operator, but I couldn't find one in core, so... *)
  let rec wat n skips = if n > max then skips else
    wat Word.(n ++ 1) (Addr.Set.add skips n) in
  wat min Addr.Set.empty

let init image = {
  path = [];
  source_addrs = image_sources image;
  skip_addrs = image_skips image;
  model = Tainteval.State.move (Tainteval.State.of_image image) Bap_disasm_arm_env.sp (Tainteval.BV(Addr.of_int ~width:32 0xbefffc58, Taint.Set.empty));
  unchecked = Taint.Set.empty;
}

let remarkable x =
  (* First check the taintset has elements, because this is slow... *)
  if not @@ Taint.Set.is_empty x.unchecked
  then let taint' = Taint.Set.diff x.unchecked (Tainteval.State.taints x.model) in
       not @@ Taint.Set.is_empty taint'
  else false

let to_addr_exn = function
  | Tainteval.BV(x, _) -> x
  | x -> failwith @@ sprintf "Not an addr %s" @@ Tainteval.to_string x

let ts_to_str x = String.concat (List.map ~f:Taint.to_string (Taint.Set.to_list x)) ~sep:","

let step addr insn bil (st : t trace_step) =
  printf "Processing addr: %s\nTS: %s\n" (Addr.to_string addr) (ts_to_str st.state.unchecked); 
  (* Advance the PC manually *)
  let addr_off = Addr.of_int ~width:32 8 in
  let m' = Tainteval.State.move st.state.model Bap_disasm_arm_env.pc (Tainteval.BV(Addr.(addr + addr_off), Taint.Set.empty)) in
  let st = {st with state = {st.state with model = m'}} in
  (*printf "Step state: %s\n" (Tainteval.State.to_string st.state.model); *)
  let s = {st.state with path = addr::st.state.path} in
  printf "Insn: %s\n" (Insn.asm insn);
  printf "Bil:\t%s\n" (String.concat (List.map bil ~f:Stmt.to_string) ~sep:"\n\t");
  printf "Bilsexp:\t%s\n" (String.concat (List.map bil ~f:(fun x -> Sexp.to_string @@ Stmt.sexp_of_t x)) ~sep:"\n\t");
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
    (* fakdo, check if insn is return, if so use callgraph for nexts *)
    | Some(Tainteval.Un(_,_,_)) -> ([], [{st' with term = true}])
    (* Taint and skip tainted functions *)
    | Some(tgt) when Addr.Set.mem (s.source_addrs) @@ to_addr_exn tgt ->
      print_endline "CREATING TAINT";
      let name = Option.value ~default:"unk" @@ Option.map ~f:snd @@ Table.find_addr !ida_syms @@ to_addr_exn tgt in
      let ts = Taint.Set.singleton (Taint.fresh @@ sprintf "%s:%s" name (Addr.to_string addr)) in
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

let starts image = Seq.singleton (Addr.of_int ~width:32 0x13ad4)
(*  sym_pred image ~f:(String.is_prefix ~prefix:"checker") *)

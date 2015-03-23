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

type t = {
  path : addr list;
  source_addrs : Addr.Set.t;
  taint : Taint.t Loc.Map.t;
  check : unit Taint.Map.t;
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

let init image = {
  path = [];
  source_addrs = image_sources image;
  taint = Loc.Map.empty;
  check = Taint.Map.empty;
}

let remarkable x = not @@ Taint.Map.is_empty x.check

let new_taint s loc =
  let taint = Taint.fresh "any" in
  {s with taint = Loc.Map.add s.taint ~key:loc ~data:taint;
          check = Taint.Map.add s.check ~key:taint ~data:()}

let propogate_taint dst s src =
  let open Option in
  (Loc.Map.find s.taint src >>= fun taint ->
   Taint.Map.find s.check taint >>| fun _ ->
   {s with taint = Loc.Map.add s.taint ~key:dst ~data:taint}) |>
  value ~default:s

let elim_taint s loc =
  let open Option in
  (Loc.Map.find s.taint loc >>| fun taint ->
   {s with check = Taint.Map.remove s.check taint}) |>
  value ~default:s

let step_taint s _ = s

let step insn bil tgts (st : t trace_step) =
  let s' =
  if (List.mem (Insn.kinds insn) `Call)
     && (List.exists tgts ~f:(Addr.Set.mem st.state.source_addrs))
     then new_taint st.state (Loc.Reg Bap_disasm_arm_env.r0) else
  List.fold_left bil ~f:step_taint ~init:([], st.state) |> snd in
  {st with state = s'}

let render x = String.concat (List.map x.path ~f:Addr.to_string) ~sep:"->"
let starts image =
  sym_pred image ~f:(String.is_prefix ~prefix:"checker")

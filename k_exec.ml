open Core_kernel.Std
open Bap.Std

type model = {
  conc : Conceval.state;
}

let init_model = {
  conc = Conceval.State.empty
}

module AS = Addr.Set

type 'a trace_step = {
  model : model;
  state : 'a;
  k     : int;
  past  : AS.t;
  term  : bool;
}

let init_step k u = {
  model = init_model;
  state = u;
  k     = k;
  past  = AS.empty;
  term  = false;
}

type 'a trace_func = insn -> model -> 'a -> 'a trace_step

let run_insn (model : model) (insn : insn) : model = model

module Dis = Disasm_expert.Basic

let opt_error msg = function
  | None -> Or_error.error_string msg
  | Some v -> Or_error.return v

type term_cond =
  | Invalid_term
  | User_term
  | Early_term
  | K_term
  | Unmapped_term

let exec_insn _ _ s = s

let k_exec image ~start ~k ~f ~init:u_init =
  (* By the invariant of find_addr, Memory.view should not error *)
  let get_mem addr = Option.(Table.find_addr (Image.sections image) addr >>| fst >>| Memory.view ~from:addr >>| ok_exn) in
  let open Or_error in
  get_mem start |> opt_error "Could not find section" >>= fun mem ->
  Dis.create ~backend:"llvm" (Arch.to_string `arm) >>= fun dis ->
  let dis = Dis.store_asm @@ Dis.store_kinds dis in
  let open Sequence.Generator in 
  let init = init_step k u_init in
  Dis.run dis mem ~stop_on:[`May_affect_control_flow] 
    ~return:(fun _ -> return ())
    ~init
    ~invalid:(fun d mem s -> yield (Invalid_term, s.state))
    ~hit:(fun d mem insn s ->
      if s.k = 0 then yield (K_term, s.state) else
      (* Run the insn sequence *)
      let (s, tgts, fall) = List.fold_right (Dis.insns d) ~f:(exec_insn f) ~init:(s, [], false) in
      (* Decrement the step count *)
      let s = {s with k = s.k - 1} in
      if s.term then yield (User_term, s.state) else
      (* Hit all jump targets *)
      List.fold_left tgts ~f:(fun tgt m -> m >>= fun _ ->
        if AS.mem s.past tgt then return () else
        match get_mem tgt with
          | Some mem -> Dis.jump d mem {s with past = AS.add s.past tgt}
          | None     -> yield (Unmapped_term, s.state))
        ~init:(return ()) >>= fun _ ->
      (* If we're going to fall through, do so *)
      if fall
        then Dis.step d s
        else return ()
    )
    ~stopped:(fun d s -> yield @@ (Early_term, s.state)) |> run |> Or_error.return

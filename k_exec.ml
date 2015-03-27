open Core_kernel.Std
open Bap.Std

module AS = Addr.Set

type 'a trace_step = {
  state : 'a;
  addrs : AS.t;
  k     : int;
  term  : bool;
}

let init_step k u = {
  state = u;
  addrs = AS.empty;
  k     = k;
  term  = false;
}

module Dis = Disasm_expert.Basic

type 'a trace_func = addr -> Dis.full_insn -> stmt list -> 'a trace_step -> 'a tracer 
and 'a tracer = ('a trace_step * addr) list * 'a trace_step list

let opt_error msg = function
  | None -> Or_error.error_string msg
  | Some v -> Or_error.return v

type term_cond =
  | Invalid_term
  | User_term
  | Early_term
  | K_term
  | Unmapped_term

let term_to_string = function
  | Invalid_term -> "Invalid"
  | User_term -> "User"
  | Early_term -> "Early"
  | K_term -> "K"
  | Unmapped_term -> "Unmapped"

exception Abort of string


let exec_insn (f : 'a trace_func) ((jmps, falls) : 'a tracer) ((mem, opt_insn) : (mem * Dis.full_insn option)) : 'a tracer =
  let inval_dis_msg = "Invalid disasms terminate. They should not be here." in
  let insn = Option.value_exn ~message:inval_dis_msg opt_insn in
  match Bap_disasm_arm_lifter.lift mem insn with
   | Ok(bil) ->
     let (jmpss, fallss) = falls |>
       List.map ~f:(f (Memory.min_addr mem) insn bil) |>
       List.unzip in
     (List.concat @@ jmps::jmpss, List.concat fallss)
   | Error(_) -> 
       (* This isn't quite right, since it will report user_term *)
       (* I should find a way to make invalid_term happen instead *)
       (jmps, List.map falls ~f:(fun s -> {s with term = true}))

let k_exec image ~start ~k ~f ~init:u_init =
  (* By the invariant of find_addr, Memory.view should not error *)
  let get_mem addr = Option.(Table.find_addr (Image.sections image) addr >>| fst >>| Memory.view ~from:addr >>| ok_exn) in
  let open Or_error in
  get_mem start |> opt_error "Could not find section" >>= fun mem ->
  Dis.create ~backend:"llvm" (Arch.to_string @@ Image.arch image) >>= fun dis ->
  let dis = Dis.store_asm @@ Dis.store_kinds dis in
  let open Sequence.Generator in 
  let init = init_step k u_init in
  Dis.run dis mem ~stop_on:[`May_affect_control_flow] 
    ~return:(fun _ -> return ())
    ~init
    ~invalid:(fun _ mem s -> printf "INVALID: %s\n" (Memory.to_string mem); yield (Invalid_term, s.state))
    ~hit:(fun d mem _ s ->
      let addr = Memory.min_addr mem in
      if s.k = 0 || AS.mem s.addrs addr then yield (K_term, s.state) else
      let s = {s with addrs = AS.add s.addrs addr} in
      (* Run the insn sequence *)
      let (tgts, falls) = List.fold_left (Dis.insns d) ~f:(exec_insn f) ~init:([], [s]) in
      (* Decrement the step count *)
      let (tgts, falls) = List.map tgts ~f:(fun (s, dst) -> {s with k = s.k - 1}, dst),
                          List.map falls ~f:(fun s -> {s with k = s.k - 1}) in 
      (* If we're going to fall through, do so *)
      List.fold_left falls ~f:(fun m s -> m >>= fun _ ->
        if s.term then yield (User_term, s.state) else
        Dis.step d s) ~init:(return ()) >>= fun _ -> 
      (* Hit all jump targets *)
      List.fold_left tgts ~f:(fun m (s, dst) -> m >>= fun _ ->
        if s.term then yield (User_term, s.state) else
        match get_mem dst with
          | Some mem -> Dis.jump d mem s
          | None     -> yield (Unmapped_term, s.state))
        ~init:(return ())
    )
    ~stopped:(fun _ s -> print_endline "STOPPED"; yield @@ (Early_term, s.state)) |> run |> Or_error.return

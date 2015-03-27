open Core_kernel.Std
open Bap.Std
open Bap_plugins.Std
open Cmdliner
open K_policy

Plugins.load ()

module CheckErr  = CheckPolicy(Err_policy)

let check prog k err_funcs out =
  Err_policy.load err_funcs;
  let open Or_error in
  Image.create prog >>= fun (image, _) ->
  Ida.(with_file ~ida:"idal" prog (fun ida ->
    Table.iteri (Image.sections image) ~f:(fun mem s ->
      if Section.is_executable s
        then Table.iteri (get_symbols ~demangle:`internal ida (Image.arch image) mem) ~f:(fun mem sym ->
          printf "IDA sym: %s %s\n" (Addr.to_string (Memory.min_addr mem)) sym;
          Err_policy.ida_syms := Table.add !Err_policy.ida_syms mem sym |> ok_exn)
  ))) >>= fun _ ->
  return @@ CheckErr.check_image k image out

let prog =
  let doc = "Analyze the program at path $(docv)" in
  Arg.(value & pos 0 string "a.out" & info [] ~docv:"PROG" ~doc)

let k =
  let doc = "Execute forwards $(docv) blocks" in
  Arg.(value & opt int 10 & info ["k"] ~docv:"K" ~doc)

let err_funcs =
  let doc = "Read list of error generating functions from $(docv)" in
  Arg.(value & pos 1 string "err_funcs" & info [] ~docv:"ERR_FUNCS" ~doc)

let out_file =
  let doc = "Write out error paths to $(docv)" in
  Arg.(value & opt string "out" & info ["o"] ~docv:"OUT" ~doc)

let check_t = Term.(pure check $ prog $ k $ err_funcs $ out_file)

let info =
  let doc = "Analyze a program with k-step concretization" in
  Term.info "check" ~doc

let () = match Term.eval (check_t, info) with
  | `Error _ -> exit 1
  | `Ok (Error(e)) -> print_endline (Error.to_string_hum e); exit 2
  | _ -> exit 0

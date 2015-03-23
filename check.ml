open Core_kernel.Std
open Bap.Std
open Bap_plugins.Std
open Cmdliner
open K_policy

Plugins.load ()

module CheckErr  = CheckPolicy(Err_policy)

let check prog k =
  print_endline prog;
  let open Or_error in
  Image.create prog >>= fun (image, _) ->
  return @@ CheckErr.check_image k image

let prog =
  let doc = "Analyze the program at path $(docv)" in
  Arg.(value & pos 0 string "a.out" & info [] ~docv:"PROG" ~doc)

let k =
  let doc = "Execute forwards $(docv) blocks" in
  Arg.(value & opt int 10 & info ["k"] ~docv:"K" ~doc)

let check_t = Term.(pure check $ prog $ k)

let info =
  let doc = "Analyze a program with k-step concretization" in
  Term.info "check" ~doc

let () = match Term.eval (check_t, info) with
  | `Error _ -> exit 1
  | `Ok (Error(e)) -> print_endline (Error.to_string_hum e); exit 2
  | _ -> exit 0

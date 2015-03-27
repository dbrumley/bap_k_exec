open Core_kernel.Std
open Bap.Std
open K_exec

module type POLICY = sig
  type t
  val step : t trace_func
  val init : image -> t
  val remarkable : t -> bool
  val render : t -> string
  val starts : image -> addr Seq.t
end

module CheckPolicy = functor (P: POLICY) -> struct
  let check_image k image out =
    Out_channel.with_file out ~f:(fun oc ->
      Seq.iter (P.starts image) ~f:(fun start ->
        Seq.iter (k_exec image ~start ~k ~f:P.step ~init:(P.init image) |> Or_error.ok_exn) ~f:(fun (m, v) ->
          if P.remarkable v
            then (Out_channel.output_string oc @@ P.render @@ v; Out_channel.output_string oc @@ K_exec.term_to_string m)
            else ())))
end

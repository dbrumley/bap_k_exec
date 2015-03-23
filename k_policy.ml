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
  let check_image k image =
    Seq.iter (P.starts image) ~f:(fun start ->
      Seq.iter (k_exec image ~start ~k ~f:P.step ~init:(P.init image) |> Or_error.ok_exn) ~f:(fun (_, v) ->
        if P.remarkable v
          then print_endline @@ P.render @@ v
          else ()))
end

module NullPolicy : POLICY = struct
  type t = unit
  let step _ _ _ = ident
  let init _ = ()
  let remarkable _ = false
  let render _ = ""
  let starts _ = Seq.empty
end

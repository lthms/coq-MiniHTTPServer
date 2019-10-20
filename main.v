From Coq Require Import List.
From Praecia Require Import TCP FileSystem Parser HTTP URI Server.
From FreeSpec Require Import Exec Console.

Import ListNotations.

Generalizable All Variables.

(* Definition handler {ix} req : impure ix string := *)
(*   let res := *)
(*       match parse http_request req with *)
(*       | inl _ => make_response client_error_BadRequest "" *)
(*       | inr (Get uri) => *)
(*         let resource := sandbox ([Dirname "opt"; Dirname "praecia"]) uri in *)
(*         let path := uri_to_path resource in *)
(*         var fd <- open path in *)
(*         var content <- read fd in *)
(*         close fd;; *)
(*         make_response success_OK content *)
(*       end *)
(*   in pure (response_to_string res). *)

Exec (http_server (ix := TCP <+> FILESYSTEM)).

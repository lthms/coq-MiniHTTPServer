From Coq Require Import List.
From Praecia Require Import TCP Parser HTTP URI Server.
From FreeSpec Require Import Exec Console.

Import ListNotations.

Generalizable All Variables.

Definition handler {ix} req : impure ix string :=
  let res :=
      match parse http_request req with
      | inl _ => make_response client_error_BadRequest ""
      | inr (Get uri) =>
        let resource := sandbox ([Dirname "opt"; Dirname "praecia"]) uri in
        make_response success_OK (uri_to_path resource)
      end
  in pure (response_to_string res).

Exec (tcp_server handler).

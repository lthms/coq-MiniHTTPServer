From FreeSpec Require Import Core Core.Notations.
From Praecia Require Import FileSystem TCP URI HTTP Parser.
From Prelude Require Import Tactics.

Import ListNotations.
#[local] Open Scope string_scope.
#[local] Open Scope prelude_scope.

Generalizable All Variables.

Definition sandbox (base : list directory_id) (req : uri) : uri :=
  make_uri (List.app base (canonicalize (dirname req))) (filename req).

Definition read_content `{Provide ix FILESYSTEM} (path : string)
  : impure ix string :=
  open path >>= fun fd => read fd <* close fd.

(* TODO: add a notation in coq-prelude var (x : T) <- p in q *)
Definition request_handler `{Provide ix FILESYSTEM}
    (base : list directory_id) (req : request)
  : impure ix response :=
  match req with
  | Get uri =>
    do let path := uri_to_path (sandbox base uri) in
       var isf <- is_file path in
       if (isf : bool)
       then make_response success_OK <$> read_content path
       else pure (make_response client_error_NotFound "Resource not found.")
    end
  end.

Definition tcp_handler `{Provide ix FILESYSTEM}
    (base : list directory_id) (req : string)
  : impure ix string :=
  response_to_string <$> match parse http_request req with
                         | inl _ => pure (make_response client_error_BadRequest "")
                         | inr req => request_handler base req
                         end.

Definition http_server `{Provide ix FILESYSTEM, Provide ix TCP}
  : impure ix unit :=
  do var server <- new_tcp_socket "localhost:8000" in
     listen_incoming_connection server;

     var client <- accept_connection server in
     var req <- read_socket client in
     var res <- tcp_handler [Dirname "opt"; Dirname "praecia"] req in

     write_socket client res;
     close_socket client;
     close_socket server
  end.

Lemma fd_set_trustworthy_read_content `{Provide ix FILESYSTEM} (ω : fd_set) (path : string)
  : trustworthy_impure fd_set_specs ω (read_content path).

Proof.
  now prove_impure.
Qed.

Hint Resolve fd_set_trustworthy_read_content.

Lemma fd_set_preserving_read_content `{Provide ix FILESYSTEM} (path : string)
  : fd_set_preserving (read_content path).

Proof.
  intros ω ω' x run.
  unroll_impure_run run.
  intros fd'.
  unfold add_fd, del_fd.
  destruct fd_eq_dec; subst.
  + now inversion prom; ssubst.
  + reflexivity.
Qed.

#[local] Opaque read_content.

Lemma fd_set_trustworthy_is_file `{Provide ix FILESYSTEM} (ω : fd_set) (path : string)
  : trustworthy_impure fd_set_specs ω (is_file path).

Proof.
  now prove_impure.
Qed.

Hint Resolve fd_set_trustworthy_is_file.

Lemma fd_set_preserving_is_file `{Provide ix FILESYSTEM} (path : string)
  : fd_set_preserving (is_file path).

Proof.
  intros ω ω' x run.
  now unroll_impure_run run.
Qed.

#[local] Opaque is_file.

Lemma fd_set_trustworthy_request_handler `{Provide ix FILESYSTEM}
    (base : list directory_id) (req : request) (ω : fd_set)
  : trustworthy_impure fd_set_specs ω (request_handler base req).

Proof.
  destruct req.
  prove_impure; auto.
  unfold impure_map. (* FIXME: should be done by the [prove_impure] tactic *)
  now prove_impure.
Qed.

Lemma fd_set_preserving_request_handler `{Provide ix FILESYSTEM}
    (base : list directory_id) (req : request)
  : fd_set_preserving (request_handler base req).

Proof.
  intros ω ω' x run fd.
  destruct req.
  unroll_impure_run run.
  + unfold impure_map in run1. (* FIXME: should be done by unroll_impure_run tactic *)
    unroll_impure_run run1.

    apply fd_set_preserving_is_file in run0.
    apply fd_set_preserving_read_content in run.

    now transitivity (ω'' fd).
  + now apply fd_set_preserving_is_file in run0.
Qed.

#[local] Opaque request_handler.

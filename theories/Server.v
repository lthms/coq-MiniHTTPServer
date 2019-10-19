From FreeSpec Require Import Core Core.Notations.
From Praecia Require Import FileSystem TCP URI HTTP Parser.
From Prelude Require Import Tactics.

Import ListNotations.
#[local] Open Scope string_scope.
#[local] Open Scope prelude_scope.

#[local] Opaque http_request.

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
  tcp_server (tcp_handler [Dirname "opt"; Dirname "praecia"]).

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

Lemma fd_set_trustworthy_tcp_handler `{Provide ix FILESYSTEM}
    (base : list directory_id) (req : string) (ω : fd_set)
  : trustworthy_impure fd_set_specs ω (tcp_handler base req).

Proof.
  prove_impure.
  destruct (http_request req).
  + prove_impure.
  + prove_impure.
    destruct (fst p).
    now prove_impure.
Qed.

Hint Resolve fd_set_trustworthy_tcp_handler.

Lemma fd_set_preserving_tcp_handler `{Provide ix FILESYSTEM}
    (base : list directory_id) (req : string)
  : fd_set_preserving (tcp_handler base req).

Proof.
  intros ω ω' x run fd.
  unroll_impure_run run.
  destruct (http_request req).
  + now unroll_impure_run run0.
  + destruct p as [[res_id] req'].
    unroll_impure_run run0.
    ++ apply fd_set_preserving_is_file in run.
       apply fd_set_preserving_read_content in run0.

       now transitivity (ω'' fd).
    ++ now apply fd_set_preserving_is_file in run.
Qed.

Hint Resolve fd_set_preserving_tcp_handler.

#[local] Opaque tcp_handler.
#[local] Opaque response_to_string.

From Coq Require Import FunctionalExtensionality.

Lemma fd_set_preserving_repeatM {a} `{Provide ix FILESYSTEM}
    (p : impure ix a)
    (fd_preserving : fd_set_preserving p)
    (n : nat)
  : fd_set_preserving (repeatM n p).

Proof.
  intros ω ω' fd run.
  induction n.
  + now unroll_impure_run run.
  + unroll_impure_run run.
    apply IHn.
    assert (equ : ω = ω''). {
      apply functional_extensionality.
      intros fd'.
      eapply (fd_preserving ω); eauto.
    }
    now rewrite equ.
Qed.

Hint Resolve fd_set_preserving_repeatM.

Lemma repeatM_preserving_trustworthy {a} `{Provide ix FILESYSTEM}
    (p : impure ix a) (ω : fd_set)
    (fd_trust : trustworthy_impure fd_set_specs ω p)
    (fd_preserving : fd_set_preserving p)
    (n : nat)
  : trustworthy_impure fd_set_specs ω (repeatM n p).

Proof.
  induction n.
  + prove_impure.
  + prove_impure.
    ++ exact fd_trust.
    ++ assert (equ : ω = w). {
         apply functional_extensionality.
         intros fd'.
         eapply (fd_preserving ω).
         exact Hrun.
       }
       rewrite <- equ.
       apply IHn.
Qed.

#[local] Opaque repeatM.

Lemma fd_set_preserving_tcp_server_repeat_routine
   `{Provide ix TCP, MayProvide ix FILESYSTEM, Distinguish ix TCP FILESYSTEM}
    (server : socket_descriptor)
    (handler : string -> impure ix string)
    (preserve : forall (req : string), fd_set_preserving (handler req))
  : fd_set_preserving (do var client <- accept_connection server in

                          var req <- read_socket client in
                          var res <- handler req in
                          write_socket client res;

                          close_socket client
                       end).

Proof.
  intros ω ω' b run fd.
  unroll_impure_run run.
  now apply preserve in run.
Qed.

Hint Resolve fd_set_preserving_tcp_server_repeat_routine.

Lemma fd_set_trustworthy_http_server `{StrictProvide2 ix FILESYSTEM TCP} (ω : fd_set)
  : trustworthy_impure fd_set_specs ω http_server.

Proof.
  prove_impure.
  apply repeatM_preserving_trustworthy.
  + prove_impure.
    destruct (http_request x2); now prove_impure.
  + intros ω' ω'' [] run fd.
    apply fd_set_preserving_tcp_server_repeat_routine in run; auto.
Qed.

Lemma fd_set_preserving_http_server `{StrictProvide2 ix FILESYSTEM TCP}
  : fd_set_preserving http_server.

Proof.
  intros ω ω' x run fd.
  unroll_impure_run run.
  apply fd_set_preserving_repeatM in run; auto.
  now apply fd_set_preserving_tcp_server_repeat_routine.
Qed.

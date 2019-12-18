From Coq Require Import FunctionalExtensionality.
From FreeSpec Require Import Core Console.
From Praecia Require Import FileSystem TCP URI HTTP.
From Prelude Require Import All Tactics Bytes Text.

Generalizable All Variables.

Definition sandbox (base : list directory_id) (req : uri) : uri :=
  make_uri (List.app base (canonicalize (dirname req))) (filename req).

Definition read_content `{Provide2 ix FILESYSTEM CONSOLE}
    (path : bytes)
  : impure ix bytes :=
  do echo ("  reading <" ++ path ++ ">... ");
     let* fd <- open path in
     let* c <- read fd in
     close fd;
     echo ("done.\n");
     pure c
  end.

(* TODO: add a notation in coq-prelude var (x : T) <- p in q *)
Definition request_handler `{Provide2 ix FILESYSTEM CONSOLE}
    (base : list directory_id) (req : request)
  : impure ix response :=
  match req with
  | Get uri =>
    do let path := uri_to_path (sandbox base uri) in
       let* isf <- file_exists path in
       if (isf : bool)
       then make_response success_OK <$> read_content path
       else do echo ("  resource <" ++ path ++"> not found\n");
               pure (make_response client_error_NotFound "Resource not found.")
            end
    end
  end.

Definition tcp_handler `{Provide2 ix FILESYSTEM CONSOLE}
    (base : list directory_id) (req : bytes)
  : impure ix bytes :=
  do echo "new request received\n";
     echo ("  request size is " ++ Int.bytes_of_int (Bytes.length req) ++ "\n");
     response_to_string <$> match http_request req with
                            | inl _ => pure (make_response client_error_BadRequest "Bad request")
                            | inr req => request_handler base (fst req)
                            end
  end.

Definition http_server `{Provide3 ix FILESYSTEM TCP CONSOLE}
  : impure ix unit :=
  do echo "hello, world!\n";
     tcp_server (tcp_handler [Dirname "tmp"])
  end.

#[local] Opaque http_request.

Tactic Notation "prove" "impure" "with" ident(db) := prove_impure; eauto with db.

Lemma fd_set_respectful_read_content `{StrictProvide2 ix FILESYSTEM CONSOLE} (ω : fd_set) (path : bytes)
  : respectful_impure fd_set_contract ω (read_content path).

Proof.
  prove impure with praecia.
Qed.

Hint Resolve fd_set_respectful_read_content : praecia.

Lemma fd_set_preserving_read_content `{StrictProvide2 ix FILESYSTEM CONSOLE} (path : bytes)
  : fd_set_preserving (read_content path).

Proof.
  intros ω ω' x run.
  unroll_respectful_run run.
  intros fd'.
  unfold add_fd, del_fd.
  destruct fd_eq_dec; subst.
  + now inversion o_callee0; ssubst.
  + reflexivity.
Qed.

#[local] Opaque read_content.

Lemma fd_set_respectful_file_exists `{Provide ix FILESYSTEM} (ω : fd_set) (path : bytes)
  : respectful_impure fd_set_contract ω (file_exists path).

Proof.
  prove impure with praecia.
Qed.

Hint Resolve fd_set_respectful_file_exists : praecia.

Lemma fd_set_preserving_file_exists `{Provide ix FILESYSTEM} (path : bytes)
  : fd_set_preserving (file_exists path).

Proof.
  intros ω ω' x run.
  now unroll_respectful_run run.
Qed.

#[local] Opaque file_exists.

Lemma fd_set_respectful_tcp_handler `{StrictProvide2 ix FILESYSTEM CONSOLE}
    (base : list directory_id) (req : bytes) (ω : fd_set)
  : respectful_impure fd_set_contract ω (tcp_handler base req).

Proof.
  prove_impure.
  destruct (http_request req).
  + prove_impure.
  + prove_impure.
    destruct (fst p).
    prove impure with praecia.
Qed.

Hint Resolve fd_set_respectful_tcp_handler : praecia.

Lemma fd_set_preserving_tcp_handler `{StrictProvide2 ix FILESYSTEM CONSOLE}
    (base : list directory_id) (req : bytes)
  : fd_set_preserving (tcp_handler base req).

Proof.
  intros ω ω' x run fd.
  unroll_respectful_run run.
  destruct (http_request req).
  + now unroll_respectful_run run.
  + destruct p as [[res_id] req'].
    unroll_respectful_run run.
    ++ apply fd_set_preserving_file_exists in run0.
       apply fd_set_preserving_read_content in run.
       now transitivity (ω'' fd).
    ++ now apply fd_set_preserving_file_exists in run0.
Qed.

Hint Resolve fd_set_preserving_tcp_handler : praecia.

#[local] Opaque tcp_handler.
#[local] Opaque response_to_string.

Lemma fd_set_preserving_repeatM {a} `{Provide ix FILESYSTEM}
    (p : impure ix a)
    (fd_preserving : fd_set_preserving p)
    (n : nat)
  : fd_set_preserving (repeatM n p).

Proof.
  intros ω ω' fd run.
  induction n.
  + now unroll_respectful_run run.
  + unroll_respectful_run run.
    apply IHn.
    assert (equ : ω = ω''). {
      apply functional_extensionality.
      eauto with praecia.
    }
    now rewrite equ.
Qed.

Hint Resolve fd_set_preserving_repeatM : praecia.

Lemma repeatM_preserving_respectful {a} `{Provide ix FILESYSTEM}
    (p : impure ix a) (ω : fd_set)
    (fd_trust : respectful_impure fd_set_contract ω p)
    (fd_preserving : fd_set_preserving p)
    (n : nat)
  : respectful_impure fd_set_contract ω (repeatM n p).

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
    (handler : bytes -> impure ix bytes)
    (preserve : forall (req : bytes), fd_set_preserving (handler req))
  : fd_set_preserving (do let* client <- accept_connection server in

                          let* req <- read_socket client in
                          let* res <- handler req in
                          write_socket client res;

                          close_socket client
                       end).

Proof.
  intros ω ω' b run fd.
  unroll_respectful_run run.
  now apply preserve in run.
Qed.

Hint Resolve fd_set_preserving_tcp_server_repeat_routine : praecia.

Lemma fd_set_respectful_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
    (ω : fd_set)
  : respectful_impure fd_set_contract ω http_server.

Proof.
  prove_impure.
  apply repeatM_preserving_respectful.
  + prove_impure.
    destruct (http_request x3); prove impure with praecia;
       apply fd_set_respectful_tcp_handler. (* TODO: Why do we need this when it has been added as a hint? *)
  + intros ω' ω'' [] run fd.
    apply fd_set_preserving_tcp_server_repeat_routine in run; auto with praecia.
    apply fd_set_preserving_tcp_handler. (* TODO: Same here? *)
Qed.

Lemma fd_set_preserving_http_server `{StrictProvide3 ix FILESYSTEM TCP CONSOLE}
  : fd_set_preserving http_server.

Proof.
  intros ω ω' x run fd.
  unroll_respectful_run run.
  apply fd_set_preserving_repeatM in run; auto with praecia.
  apply fd_set_preserving_tcp_server_repeat_routine.
  apply fd_set_preserving_tcp_handler.
Qed.

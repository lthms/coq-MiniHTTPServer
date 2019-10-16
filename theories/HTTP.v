From FreeSpec Require Import Core.
From Praecia Require Import Parser URI FileSystem TCP.

Generalizable All Variables.

Inductive request :=
| Get (resource : uri).

Inductive status :=
| success_OK
| client_error_BadRequest
| client_error_NotFound.

Record response := make_response { code : status
                                 ; body : string
                                 }.

Axiom response_to_string : response -> string.

Definition http_request : parser request :=
  Get <$> (str "GET" *> whitespaces *> read_uri <* whitespaces <* str "HTTP/1.1").

(* TODO: use base. *)
(* TODO: add a notation in coq-prelude var (x : T) <- p in q *)
Definition request_handler `{Provide ix FILESYSTEM}
    (_base : list directory_id) (req : request)
  : impure ix response :=
  match req with
  | Get uri =>
    do let path := uri_to_path uri in
       var isf <- is_file path in
       if (isf : bool)
       then do var fd <- open path in
               var content <- (read fd <* close fd) in
               pure (make_response success_OK content)
            end
       else pure (make_response client_error_NotFound "Resource not found.")
    end
  end.

Definition tcp_handler `{Provide ix FILESYSTEM}
    (_base : list directory_id) (req : string)
  : impure ix string :=
  response_to_string <$> match parse http_request req with
                         | inl _ => pure (make_response client_error_BadRequest "")
                         | inr req => request_handler _base req
                         end.

Definition http_server `{Provide ix FILESYSTEM, Provide ix TCP} (_base : list directory_id)
  : impure ix unit :=
  do var server <- new_tcp_socket "localhost:8000" in
     listen_incoming_connection server;

     var client <- accept_connection server in
     var req <- read_socket client in
     var res <- tcp_handler _base req in

     write_socket client res;
     close_socket client;
     close_socket server
  end.

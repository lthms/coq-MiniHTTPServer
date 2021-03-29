From Comparse Require Import Monad Combinators.
From MiniHTTPServerFFI Require Import Slice SliceFacts StrExt.
From MiniHTTPServer Require Import URI.
From CoqFFI Require Import String.

Import MonadLetNotation.

Inductive request :=
| Get (resource : uri).

Inductive status :=
| success_OK
| client_error_BadRequest
| client_error_NotFound.

Definition status_to_bytes (code : status) : string :=
  match code with
  | success_OK => "200"
  | client_error_BadRequest => "400"
  | client_error_NotFound => "404"
  end.

Record response := make_response { code : status
                                 ; body : string
                                 }.

Definition whitespaces : parser Slice.t unit :=
  skip (many (char " ")).

Definition http_request : parser Slice.t request :=
  str "GET";;
  whitespaces;;
  let* uri := read_uri in
  whitespaces;;
  str "HTTP/1.1";;
  pure (Get uri).

Definition response_to_string (res : response) : string :=
  "HTTP/1.1 " ++ status_to_bytes (code res) ++ " Response\r\n" ++
  "Content-Length: " ++ (StrExt.of_int (StrExt.length (body res))) ++ "\r\n" ++
  "Connection: Closed\r\n" ++
  "\r\n" ++
  body res ++ "\r\n" ++
  "\r\n".

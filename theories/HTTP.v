From Prelude Require Import All Bytes Byte Int.
From Comparse Require Import Monad Text Combinators.
From MiniHTTPServer Require Import URI.

Inductive request :=
| Get (resource : uri).

Inductive status :=
| success_OK
| client_error_BadRequest
| client_error_NotFound.

Definition status_to_bytes (code : status) : bytes :=
  match code with
  | success_OK => "200"
  | client_error_BadRequest => "400"
  | client_error_NotFound => "404"
  end.

Record response := make_response { code : status
                                 ; body : bytes
                                 }.

Definition whitespaces : parser bytes unit :=
  skip (many (char c#" ")).

Definition http_request : parser bytes request :=
  Get <$> (str "GET" *> whitespaces *> read_uri <* whitespaces <* str "HTTP/1.1").

Definition response_to_string (res : response) : bytes :=
  "HTTP/1.1 " ++ status_to_bytes (code res) ++ " Response\r\n" ++
  "Content-Length: " ++ (bytes_of_int (Bytes.length (body res))) ++ "\r\n" ++
  "Connection: Closed\r\n" ++
  "\r\n" ++
  body res ++ "\r\n" ++
  "\r\n".

From MiniHTTPServer Require Import URI.
From Comparse Require Import Monad Combinators.

Inductive request :=
| Get (resource : uri).

Inductive status :=
| success_OK
| client_error_BadRequest
| client_error_NotFound.

Definition status_to_bytes (code : status) : bytestring :=
  match code with
  | success_OK => "200"
  | client_error_BadRequest => "400"
  | client_error_NotFound => "404"
  end.

Record response := make_response { code : status
                                 ; body : bytestring
                                 }.

Definition whitespaces : parser bytestring unit :=
  skip (many (char " ")).

Definition http_request : parser bytestring request :=
  Get <$> (str "GET" *> whitespaces *> read_uri <* whitespaces <* str "HTTP/1.1").

Definition response_to_string (res : response) : bytestring :=
  "HTTP/1.1 " ++ status_to_bytes (code res) ++ " Response\r\n" ++
  "Content-Length: " ++ (bytestring_of_int (Bytestring.length (body res))) ++ "\r\n" ++
  "Connection: Closed\r\n" ++
  "\r\n" ++
  body res ++ "\r\n" ++
  "\r\n".

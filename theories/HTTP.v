From Praecia Require Import Parser URI.
From Prelude Require Import Z.
From Coq Require Import ZArith.

Import ListNotations.
#[local] Open Scope string_scope.
#[local] Open Scope prelude_scope.

Inductive request :=
| Get (resource : uri).

Inductive status :=
| success_OK
| client_error_BadRequest
| client_error_NotFound.

Definition status_to_string (code : status) : string :=
  match code with
  | success_OK => "200"
  | client_error_BadRequest => "400"
  | client_error_NotFound => "404"
  end.

Record response := make_response { code : status
                                 ; body : string
                                 }.

#[local] Open Scope string_scope.

Definition crlf := String "013" (String "010" EmptyString).

Definition response_to_string (res : response) : string :=
  "HTTP/1.1 " ++ status_to_string (code res) ++ " Response" ++ crlf ++
  "Content-Length: " ++ (string_of_Z (Z.of_nat (String.length (body res)))) ++ crlf ++
  "Connection: Closed" ++ crlf ++
  crlf ++
  body res ++ crlf ++
  crlf.

Definition http_request : parser request :=
  Get <$> (str "GET" *> whitespaces *> read_uri <* whitespaces <* str "HTTP/1.1").

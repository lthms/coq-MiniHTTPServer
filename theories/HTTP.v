From Praecia Require Import Parser URI.

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

Definition newline := String "010" "".

Definition response_to_string (res : response) : string :=
  "HTTP/1.1 " ++ status_to_string (code res) ++ " Reason phrase" ++ newline ++
  newline ++
  body res.

Definition http_request : parser request :=
  Get <$> (str "GET" *> whitespaces *> read_uri <* whitespaces <* str "HTTP/1.1").

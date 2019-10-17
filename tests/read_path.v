From Coq Require Import String.
From Prelude Require Import Option.
From FreeSpec Require Import Exec Console.
From Praecia Require Import Parser HTTP URI.

#[local] Open Scope string_scope.

Exec
  match parse http_request "GET /test/../.././ HTTP/1.1" with
  | inr (Get uri) => echo ("Parsing succeeded: "
                           ++ uri_to_path (make_uri (canonicalize (dirname uri))
                                                    (filename uri)))

  | inl (x :: _) => echo ("Error while parsing: " ++ x)
  | inl _ => echo "Error while parsing"
  end.

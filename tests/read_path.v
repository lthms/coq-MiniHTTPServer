From Coq Require Import String.
From Prelude Require Import Option.
From FreeSpec Require Import Exec Console.
From Praecia Require Import Parser HTTP URI.

#[local] Open Scope string_scope.

Exec
  match parse http_request "GET /test/../.././foo HTTP/1.1" with
  | inl _ => echo "Error while parsing"
  | inr (Get uri) => echo ("Parsing succeeded: "
                           ++ fromMaybe "no file required" (filename uri))
  end.

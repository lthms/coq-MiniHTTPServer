From Coq Require Import ExtrOcamlNativeString String.

From MiniHTTPServer Require Import App.
From SimpleIO Require Import IO_Monad.

Definition main : io_unit := IO.unsafe_run (http_server (m:=IO) 100).

Extraction "main.ml" main.

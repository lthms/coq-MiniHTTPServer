From Base Require Import Extraction.
From FreeSpec.Core Require Import All Extraction.
From FreeSpec.Stdlib Require Import Console.
From MiniHTTPServer Require Import App.

Timeout 2 Definition run_http_server : unit :=
  let main := http_server 1000 in
  gen_main main.

Extraction "minihttpserver.ml" run_http_server.

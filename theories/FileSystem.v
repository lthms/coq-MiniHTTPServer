From Coq Require Import Int63 String.
From FreeSpec Require Import Core.

Generalizable All Variables.

Axiom file_descriptor : Type.

Inductive FILESYSTEM : interface :=
| Open (path : string) : FILESYSTEM file_descriptor
| IsFile (file : string) : FILESYSTEM bool
| Read (file : file_descriptor) : FILESYSTEM string
| Close (file : file_descriptor) : FILESYSTEM unit.

Definition open `{Provide ix FILESYSTEM} (path : string) : impure ix file_descriptor :=
  request (Open path).

Definition close `{Provide ix FILESYSTEM} (fd : file_descriptor) : impure ix unit :=
  request (Close fd).

Definition is_file `{Provide ix FILESYSTEM} (path : string) : impure ix bool :=
  request (IsFile path).

Definition read `{Provide ix FILESYSTEM} (fd : file_descriptor) : impure ix string :=
  request (Read fd).

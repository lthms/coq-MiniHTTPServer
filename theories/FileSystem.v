From Coq Require Import Int63.
From Prelude Require Import All Bytes Text.
From FreeSpec Require Import Core.
From MiniHTTPServer Require Import Init.

Generalizable All Variables.

(** * Definition  *)

Axiom file_descriptor : Type.
Axiom fd_eq_dec : forall (fd1 fd2 : file_descriptor), { fd1 = fd2 } + { ~ (fd1 = fd2) }.


Inductive FILESYSTEM : interface :=
| Open (path : bytes) : FILESYSTEM file_descriptor
| FileExists (file : bytes) : FILESYSTEM bool
| Read (file : file_descriptor) : FILESYSTEM bytes
| Close (file : file_descriptor) : FILESYSTEM unit.

Register FILESYSTEM as minihttpserver.filesystem.type.
Register Open as minihttpserver.filesystem.Open.
Register FileExists as minihttpserver.filesystem.FileExists.
Register Read as minihttpserver.filesystem.Read.
Register Close as minihttpserver.filesystem.Close.

Definition open `{Provide ix FILESYSTEM} (path : bytes) : impure ix file_descriptor :=
  request (Open path).

Definition close `{Provide ix FILESYSTEM} (fd : file_descriptor) : impure ix unit :=
  request (Close fd).

Definition file_exists `{Provide ix FILESYSTEM} (path : bytes) : impure ix bool :=
  request (FileExists path).

Definition read `{Provide ix FILESYSTEM} (fd : file_descriptor) : impure ix bytes :=
  request (Read fd).

(** * Contracts *)

Definition fd_set : Type := file_descriptor -> bool.

Definition add_fd (ω : fd_set) (fd : file_descriptor) : fd_set :=
  fun (fd' : file_descriptor) => if fd_eq_dec fd fd' then true else ω fd'.

Definition del_fd (ω : fd_set) (fd : file_descriptor) : fd_set :=
  fun (fd' : file_descriptor) => if fd_eq_dec fd fd' then false else ω fd'.

Definition member (ω : fd_set) (fd : file_descriptor) : Prop :=
  ω fd = true.

Definition absent (ω : fd_set) (fd : file_descriptor) : Prop :=
  ω fd = false.

Lemma member_not_absent (ω : fd_set) (fd : file_descriptor)
  : member ω fd -> ~ absent ω fd.

Proof.
  unfold member, absent.
  intros m a.
  now rewrite m in a.
Qed.

Hint Resolve member_not_absent : minihttp.

Lemma absent_not_member (ω : fd_set) (fd : file_descriptor)
  : absent ω fd -> ~ member ω fd.

Proof.
  unfold member, absent.
  intros a m.
  now rewrite m in a.
Qed.

Hint Resolve absent_not_member : minihttp.

Lemma member_add_fd (ω : fd_set) (fd : file_descriptor) : member (add_fd ω fd) fd.

Proof.
  unfold member, add_fd.
  destruct fd_eq_dec; auto.
Qed.

Hint Resolve member_add_fd : minihttp.

Definition fd_set_update (ω : fd_set) (a : Type) (e : FILESYSTEM a) (x : a) : fd_set :=
  match e, x with
  | Open _, fd =>
    add_fd ω fd
  | Close fd, _ =>
    del_fd ω fd
  | Read _, _ =>
    ω
  | FileExists _, _ =>
    ω
  end.


Inductive fd_set_caller_obligation (ω : fd_set) : forall (a : Type), FILESYSTEM a -> Prop :=
| fd_set_open_caller (p : bytes)
  : fd_set_caller_obligation ω file_descriptor (Open p)
| fd_set_read_caller (fd : file_descriptor) (is_member : member ω fd)
  : fd_set_caller_obligation ω bytes (Read fd)
| fd_set_close_caller (fd : file_descriptor) (is_member : member ω fd)
  : fd_set_caller_obligation ω unit (Close fd)
| fd_set_is_file_caller (p : bytes)
  : fd_set_caller_obligation ω bool (FileExists p).

Hint Constructors fd_set_caller_obligation : minihttp.


Inductive fd_set_callee_obligation (ω : fd_set) : forall (a : Type), FILESYSTEM a -> a -> Prop :=
| fd_set_open_callee (p : bytes) (fd : file_descriptor) (is_absent : absent ω fd)
  : fd_set_callee_obligation ω file_descriptor (Open p) fd
| fd_set_read_callee (fd : file_descriptor) (s : bytes)
  : fd_set_callee_obligation ω bytes (Read fd) s
| fd_set_close_callee (fd : file_descriptor) (t : unit)
  : fd_set_callee_obligation ω unit (Close fd) t
| fd_set_is_file_callee (p : bytes) (b : bool)
  : fd_set_callee_obligation ω bool (FileExists p) b.

Hint Constructors fd_set_callee_obligation : minihttp.

Definition fd_set_contract : contract FILESYSTEM fd_set :=
  {| witness_update := fd_set_update
   ; caller_obligation := fd_set_caller_obligation
   ; callee_obligation := fd_set_callee_obligation
  |}.

Definition fd_set_preserving {a} `{MayProvide ix FILESYSTEM} (p : impure ix a) :=
  forall (ω ω' : fd_set) (x : a),
    respectful_run fd_set_contract p ω ω' x -> forall fd, ω fd = ω' fd.

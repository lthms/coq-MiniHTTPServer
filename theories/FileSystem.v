From Coq Require Import Int63 String.
From FreeSpec Require Import Core.

Generalizable All Variables.

(** * Definition  *)

Axiom file_descriptor : Type.
Axiom fd_eq_dec : forall (fd1 fd2 : file_descriptor), { fd1 = fd2 } + { ~ (fd1 = fd2) }.

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

Hint Resolve member_not_absent.

Lemma absent_not_member (ω : fd_set) (fd : file_descriptor)
  : absent ω fd -> ~ member ω fd.

Proof.
  unfold member, absent.
  intros a m.
  now rewrite m in a.
Qed.

Hint Resolve absent_not_member.

Lemma member_add_fd (ω : fd_set) (fd : file_descriptor) : member (add_fd ω fd) fd.

Proof.
  unfold member, add_fd.
  destruct fd_eq_dec; auto.
Qed.

Hint Resolve member_add_fd.

Definition fd_set_update (ω : fd_set) (a : Type) (e : FILESYSTEM a) (x : a) : fd_set :=
  match e, x with
  | Open _, fd =>
    add_fd ω fd
  | Close fd, _ =>
    del_fd ω fd
  | Read _, _ =>
    ω
  | IsFile _, _ =>
    ω
  end.

Inductive fd_set_caller_obligation (ω : fd_set) : forall (a : Type), FILESYSTEM a -> Prop :=
| fd_set_open_caller (p : string)
  : fd_set_caller_obligation ω file_descriptor (Open p)
| fd_set_read_caller (fd : file_descriptor) (is_member : member ω fd)
  : fd_set_caller_obligation ω string (Read fd)
| fd_set_close_caller (fd : file_descriptor) (is_member : member ω fd)
  : fd_set_caller_obligation ω unit (Close fd)
| fd_set_is_file_caller (p : string)
  : fd_set_caller_obligation ω bool (IsFile p).

Hint Constructors fd_set_caller_obligation.

Inductive fd_set_callee_obligation (ω : fd_set) : forall (a : Type), FILESYSTEM a -> a -> Prop :=
| fd_set_open_callee (p : string) (fd : file_descriptor) (is_absent : absent ω fd)
  : fd_set_callee_obligation ω file_descriptor (Open p) fd
| fd_set_read_callee (fd : file_descriptor) (s : string)
  : fd_set_callee_obligation ω string (Read fd) s
| fd_set_close_callee (fd : file_descriptor) (t : unit)
  : fd_set_callee_obligation ω unit (Close fd) t
| fd_set_is_file_callee (p : string) (b : bool)
  : fd_set_callee_obligation ω bool (IsFile p) b.

Hint Constructors fd_set_callee_obligation.

Definition fd_set_specs : specs FILESYSTEM fd_set :=
  {| witness_update := fd_set_update
   ; requirements := fd_set_caller_obligation
   ; promises := fd_set_callee_obligation
  |}.

Definition fd_set_preserving {a} `{Provide ix FILESYSTEM} (p : impure ix a) :=
  forall (ω ω' : fd_set) (x : a),
    trustworthy_run fd_set_specs p ω ω' x -> forall fd, ω fd = ω' fd.

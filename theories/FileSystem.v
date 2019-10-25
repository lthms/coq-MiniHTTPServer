From Coq Require Import Int63 String.
From FreeSpec Require Import Core Files.

Generalizable All Variables.

(** * Definition  *)

Axiom fd_eq_dec : forall (fd1 fd2 : file_descriptor), { fd1 = fd2 } + { ~ (fd1 = fd2) }.

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

Definition fd_set_update (ω : fd_set) (a : Type) (e : FILES a) (x : a) : fd_set :=
  match e, x with
  | Open _, inr fd =>
    add_fd ω fd
  | Close fd, _ =>
    del_fd ω fd
  | Read _ _, _ =>
    ω
  | FSize _, _ =>
    ω
  | Open _, _ =>
    ω
  end.

Inductive fd_set_caller_obligation (ω : fd_set) : forall (a : Type), FILES a -> Prop :=
| fd_set_open_caller (p : string)
  : fd_set_caller_obligation ω _ (Open p)
| fd_set_read_caller (fd : file_descriptor) (n : int) (is_member : member ω fd)
  : fd_set_caller_obligation ω _ (Read fd n)
| fd_set_close_caller (fd : file_descriptor) (is_member : member ω fd)
  : fd_set_caller_obligation ω unit (Close fd)
| fd_set_is_file_caller (fd : file_descriptor)
  : fd_set_caller_obligation ω _ (FSize fd).

Hint Constructors fd_set_caller_obligation.

Inductive fd_set_callee_obligation (ω : fd_set) : forall (a : Type), FILES a -> a -> Prop :=
| fd_set_open_callee_left (p : string) (fd : file_descriptor) (is_absent : absent ω fd)
  : fd_set_callee_obligation ω _ (Open p) (inr fd)
| fd_set_open_callee_right (p : string) (e : files_err)
  : fd_set_callee_obligation ω _ (Open p) (inl e)
| fd_set_read_callee (fd : file_descriptor) (n : int) (res : files_err + (int * string))
  : fd_set_callee_obligation ω _ (Read fd n) res
| fd_set_close_callee (fd : file_descriptor) (t : unit)
  : fd_set_callee_obligation ω unit (Close fd) t
| fd_set_fsize_callee (fd : file_descriptor) (res : files_err + int)
  : fd_set_callee_obligation ω _ (FSize fd) res.

Hint Constructors fd_set_callee_obligation.

Definition fd_set_contract : contract FILES fd_set :=
  {| witness_update := fd_set_update
   ; caller_obligation := fd_set_caller_obligation
   ; callee_obligation := fd_set_callee_obligation
  |}.

Definition fd_set_preserving {a} `{MayProvide ix FILESYSTEM} (p : impure ix a) :=
  forall (ω ω' : fd_set) (x : a),
    respectful_run fd_set_contract p ω ω' x -> forall fd, ω fd = ω' fd.

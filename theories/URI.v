From Praecia Require Import Parser.
From Prelude Require Import Option.

Fixpoint of_ascii_list (l : list ascii) : string :=
  match l with
  | cons x rst => String x (of_ascii_list rst)
  | nil => EmptyString
  end.

Inductive directory_id : Type :=
| Dirname (s : string)
| Current
| Parent.

Inductive uri := make_uri { dirname : list directory_id
                          ; filename : option string
                          }.

#[local]
Fixpoint canonicalize_aux (acc : list directory_id) (dirids : list directory_id) : list directory_id :=
  match dirids with
  | cons Current rst => canonicalize_aux acc rst
  | cons Parent rst => canonicalize_aux (List.tl acc) rst
  | cons x rst => canonicalize_aux (cons x acc) rst
  | nil => List.rev acc
  end.

Definition canonicalize := canonicalize_aux nil.

Definition dirname_eq (d1 d2: list directory_id) : Prop :=
  canonicalize d1 = canonicalize d2.

Inductive canonical : list directory_id -> Prop :=
| canonical_nil : canonical nil
| canonical_cons (s : string) (rst : list directory_id) (canonical_rst : canonical rst)
  : canonical (cons (Dirname s) rst).

#[local]
Lemma canonicalize_aux_canonical (d acc : list directory_id) (acc_canon : canonical acc)
  : canonical (canonicalize_aux acc d).

Proof.
  revert acc acc_canon.
  induction d; intros acc acc_canon.
  + cbn.
    admit.
  + destruct a.
    ++ cbn.
       apply IHd.
       constructor; auto.
    ++ cbn.
       now apply IHd.
    ++ cbn.
       apply IHd.
       admit.
Admitted.

Lemma canonicalize_canonical (d : list directory_id)
  : canonical (canonicalize d).

Proof.
  apply canonicalize_aux_canonical.
  constructor.
Qed.

Remark canonical_canonicalize_cons_equ (s : string) (d : list directory_id) (canon : canonical d)
  : canonicalize (cons (Dirname s) d) = cons (Dirname s) (canonicalize d).

Proof.
Admitted.

Lemma canonicalize_canonical_equ (d : list directory_id) (canon : canonical d)
  : canonicalize d = d.

Proof.
  induction d.
  + auto.
  + inversion canon; subst.
    rewrite canonical_canonicalize_cons_equ; auto.
    rewrite IHd; auto.
Qed.

Lemma canonicalize_idempontent (d : list directory_id)
  : canonicalize (canonicalize d) = canonicalize d.

Proof.
  rewrite canonicalize_canonical_equ; [ reflexivity |].
  apply canonicalize_canonical.
Qed.

Search (string -> string -> string).

#[program, local]
Fixpoint uri_to_path_aux (d : list directory_id) (canon : canonical d) : string :=
  match d with
  | nil => EmptyString
  | cons (Dirname x) rst => append x (append "/" (uri_to_path_aux rst _))
  | cons Parent _ => _
  | cons Current _ => _
  end.

Next Obligation.
  inversion canon; auto.
Defined.

Next Obligation.
  exfalso; inversion canon.
Defined.

Next Obligation.
  exfalso; inversion canon.
Defined.

Search (?a -> option ?a -> ?a).

#[program]
Definition uri_to_path (u : uri) : string :=
  append (uri_to_path_aux (canonicalize (dirname u)) _) (fromMaybe ""%string (filename u)).

Next Obligation.
  apply canonicalize_canonical.
Qed.

(** * Parsing URI *)

Definition dir_id_sep := peak (eoi <|> ((char " " <|> char "/") *> pure tt)).

Definition dirid : parser directory_id :=
  many (char "/") *>
  (str ".." *> peak dir_id_sep *> pure Parent)
  <|> (char "." *> peak dir_id_sep *> pure Current)
  <|> (do var name <- some_until read_char (peak dir_id_sep) in
          peak (char "/");
          pure (Dirname (of_ascii_list name))
       end).

(* TODO: bad performance, can we provide some useful hints here? *)
Definition path_dirname : parser (list directory_id) :=
  many dirid.

Definition read_uri : parser uri :=
  do var dirname <- path_dirname in
     many (char "/");
     var maybe_filename <- many_until read_char (char " ") in
     pure (make_uri dirname (if Nat.eqb (List.length maybe_filename) 0
                             then None
                             else Some (of_ascii_list maybe_filename)))
  end.

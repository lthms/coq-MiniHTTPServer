From Coq Require Import List.
From Praecia Require Import Parser.
From Prelude Require Import Option Equality.

Import ListNotations.
#[local] Open Scope string_scope.
#[local] Open Scope prelude_scope.

Fixpoint of_ascii_list (l : list ascii) : string :=
  match l with
  | x :: rst => String x (of_ascii_list rst)
  | [] => EmptyString
  end.

Inductive directory_id : Type :=
| Dirname (s : string)
| Current
| Parent.

Inductive uri := make_uri { dirname : list directory_id
                          ; filename : option string
                          }.

#[local]
Fixpoint canonicalize_aux (acc : list directory_id) (dirids : list directory_id)
  : list directory_id :=
  match dirids with
  | Current :: rst => canonicalize_aux acc rst
  | Parent :: rst => canonicalize_aux (tl acc) rst
  | x :: rst => canonicalize_aux (x :: acc) rst
  | [] => rev acc
  end.

Definition canonicalize := canonicalize_aux [].

Definition dirname_eq (d1 d2: list directory_id) : Prop :=
  canonicalize d1 = canonicalize d2.

Inductive canonical : list directory_id -> Prop :=
| canonical_nil : canonical []
| canonical_cons
    (s : string) (rst : list directory_id) (canonical_rst : canonical rst)
  : canonical (Dirname s :: rst).

Lemma canonical_canonical_tl (d : list directory_id)
  : canonical d -> canonical (tl d).

Proof.
  intros canon.
  destruct d as [| x rst].
  + auto.
  + now inversion canon.
Qed.

Lemma canonical_canonical_cons (a : directory_id) (d : list directory_id)
  : canonical (a :: d) <-> canonical [a] /\ canonical d.

Proof.
  split.
  + intros canon; inversion canon; subst.
    split; repeat constructor.
    exact canonical_rst.
  + intros [c1 c2].
    inversion c1; subst.
    constructor; auto.
Qed.

Lemma canonical_canonical_app (d1 d2 : list directory_id)
  : canonical d1 /\ canonical d2 <-> canonical (d1 ++ d2).

Proof.
  revert d2.
  induction d1; intros d2.
  + cbn.
    split.
    ++ now intros [_ exact].
    ++ intros exact; split; [ constructor | auto ].
  + cbn.
    rewrite (canonical_canonical_cons a d1).
    rewrite (canonical_canonical_cons a (d1 ++ d2)).
    rewrite <- IHd1.
    now rewrite and_assoc.
Qed.

Lemma canonical_canonical_rev (d : list directory_id)
  : canonical d <-> canonical (rev d).

Proof.
  induction d.
  + reflexivity.
  + cbn.
    rewrite canonical_canonical_cons.
    rewrite <- (canonical_canonical_app (rev d) [a]).
    now rewrite IHd.
Qed.

#[local]
Lemma canonicalize_aux_canonical (d acc : list directory_id)
    (acc_canon : canonical acc)
  : canonical (canonicalize_aux acc d).

Proof.
  revert acc acc_canon.
  induction d; intros acc acc_canon.
  + cbn.
    now rewrite <- canonical_canonical_rev.
  + destruct a.
    ++ cbn.
       apply IHd.
       constructor; auto.
    ++ cbn.
       now apply IHd.
    ++ cbn.
       apply IHd.
       now apply canonical_canonical_tl.
Qed.

Lemma canonicalize_canonical (d : list directory_id)
  : canonical (canonicalize d).

Proof.
  apply canonicalize_aux_canonical.
  constructor.
Qed.

Remark canonical_canonicalize_cons_equ (s : string)
    (d : list directory_id) (canon : canonical d)
  : canonicalize (Dirname s :: d) = Dirname s :: canonicalize d.

Proof.
  induction d.
  + reflexivity.
  + inversion canon; subst.
    rename s0 into s'.
    cbn.
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

#[program, local]
Fixpoint uri_to_path_aux (d : list directory_id) (canon : canonical d) : string :=
  match d with
  | [] => EmptyString
  | Dirname x :: rst => x ++ "/" ++ uri_to_path_aux rst _
  | Parent :: _ => _
  | Current :: _ => _
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

#[program]
Definition uri_to_path (u : uri) : string :=
  "/" ++ uri_to_path_aux (canonicalize (dirname u)) _ ++ fromMaybe ""%string (filename u).

Next Obligation.
  apply canonicalize_canonical.
Qed.

(** * Parsing URI *)

Definition dir_id_sep : parser unit :=
  eoi <|> ((char "/" <|> char " ") *> pure tt).

Definition uri_char : parser ascii :=
  ensure read_char (fun x => negb (eqb x " " || eqb x "/")).

Definition dirid : parser directory_id :=
  many (char "/") *>
  (str ".." *> peak dir_id_sep *> pure Parent)
  <|> (char "." *> peak dir_id_sep *> pure Current)
  <|> (do var name <- some_until uri_char (peak dir_id_sep) in
          peak (char "/");
          pure (Dirname (of_ascii_list name))
       end).

(* TODO: poor performance, can we provide some useful hints here? *)
Definition path_dirname : parser (list directory_id) :=
  many dirid.

Definition path_filename : parser (option string) :=
  do
    var candidat <- of_ascii_list <$> many uri_char in
    match candidat with
    | "" => pure None
    | "." | ".." => fail ". or .. are reserved directory names"
    | x => pure (Some x)
    end
  end.

Definition read_uri : parser uri :=
  do var dirname <- path_dirname in
     many (char "/");
     var filename <- path_filename in

     pure (make_uri dirname filename)
  end.

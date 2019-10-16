From Praecia Require Import Parser.

Fixpoint of_ascii_list (l : list ascii) : string :=
  match l with
  | cons x rst => String x (of_ascii_list rst)
  | nil => EmptyString
  end.

Inductive directory_id : Type :=
| Dirname (s : string)
| Current
| Parent.

Inductive path := make_path { dirname : list directory_id
                            ; filename : option string
                            }.

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

Eval vm_compute in (parse path_dirname "/../.salut////./tada").

Definition read_path : parser path :=
  do var dirname <- path_dirname in
     many (char "/");
     var maybe_filename <- many_until read_char (char " ") in
     pure (make_path dirname (if Nat.eqb (List.length maybe_filename) 0
                              then None
                              else Some (of_ascii_list maybe_filename)))
  end.

Definition get_http_request : parser path :=
  str "GET" *> whitespaces *> read_path <* whitespaces <* str "HTTP/1.1".

Eval vm_compute in (parse get_http_request "GET ../..//etc/passwd HTTP/1.1"%string).
Eval vm_compute in (parse get_http_request "GET /etc/passwd HTP/1.1"%string).
Eval vm_compute in (parse get_http_request "PUT /etc/passwd HTTP/1.1"%string).

#[local]
Fixpoint canonicalize_aux (acc : list directory_id) (dirids : list directory_id) : list directory_id :=
  match dirids with
  | cons Current rst => canonicalize_aux acc rst
  | cons Parent rst => canonicalize_aux (List.tl acc) rst
  | cons x rst => canonicalize_aux (cons x acc) rst
  | nil => List.rev acc
  end.

Definition canonicalize := canonicalize_aux nil.

Eval compute in (canonicalize <$> (parse path_dirname "/home/coq/../../../coqide/./x/../ ")).
Eval compute in (canonicalize <$> (parse path_dirname "/home/coq/coqide/./x/../ ")).

Definition dirname_eq (d1 d2: list directory_id) : Prop :=
  canonicalize d1 = canonicalize d2.

Inductive canonical : list directory_id -> Prop :=
| canonical_nil : canonical nil
| canonical_cons (s : string) (rst : list directory_id) (canonical_rst : canonical rst)
  : canonical (cons (Dirname s) rst).

#[program]
Fixpoint elem {a} (n : nat) (l : list a) (bound : n < List.length l) : a :=
  match l, n with
  | nil, _ => _
  | cons x _, O => x
  | cons _ rst, S n => elem n rst _
  end.

Next Obligation.
  cbn in bound.
  now apply PeanoNat.Nat.nlt_0_r in bound.
Qed.

Next Obligation.
  cbn in bound.
  lia.
Qed.

Corollary canonical_nth (d : list directory_id)
  : canonical d <-> forall (n : nat), exists (name : string), List.nth n d (Dirname "_") = Dirname name.

Proof.
  split.
  + intros canon. induction d.
    ++ intros n.
       exists "_"%string.
       destruct n; reflexivity.
    ++ intros n.
       inversion canon; subst.
       destruct n.
       +++ now exists s.
       +++ specialize IHd with n.
           apply IHd in canonical_rst.
           destruct canonical_rst.
           now exists x.
  + intros rules.
    induction d.
    ++ constructor.
    ++ destruct a.
       +++ constructor.
           apply IHd.
           intros n.
           specialize (rules (S n)).
           destruct rules.
           eassert (rew : List.nth (S n) (cons (Dirname s) d) = List.nth n d) by reflexivity.
           rewrite rew in H.
           exists x.
           now rewrite <- H.
    +++ specialize (rules 0).
        inversion rules.
        now cbn in H.
    +++ specialize (rules 0).
        inversion rules.
        now cbn in H.
Qed.


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

Remark canonical_canonicalize_cons_equ (s : string) (d : list directory_id)
  : canonicalize (cons (Dirname s) d) = cons (Dirname s) (canonicalize d).

Proof.
Admitted.


Lemma canonicalize_canonical_equ (d : list directory_id) (canon : canonical d)
  : canonicalize d = d.

Proof.
  induction d.
  + auto.
  + inversion canon; subst.
    rewrite canonical_canonicalize_cons_equ.
    rewrite IHd; auto.
Qed.

Lemma canonicalize_idempontent (d : list directory_id)
  : canonicalize (canonicalize d) = canonicalize d.

Proof.
  rewrite canonicalize_canonical_equ; [ reflexivity |].
  apply canonicalize_canonical.
Qed.

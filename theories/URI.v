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

Inductive uri := make_uri { dirname : list directory_id
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

Definition read_uri : parser uri :=
  do var dirname <- path_dirname in
     many (char "/");
     var maybe_filename <- many_until read_char (char " ") in
     pure (make_uri dirname (if Nat.eqb (List.length maybe_filename) 0
                             then None
                             else Some (of_ascii_list maybe_filename)))
  end.

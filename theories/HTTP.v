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

Fixpoint simplify (dirids : list directory_id) : list directory_id :=
  match dirids with
  | cons Current rst => simplify rst
  | cons Parent rst => simplify rst
  | cons _ (cons Parent rst) => simplify rst
  | cons x rst => cons x (simplify rst)
  | nil => nil
  end.

Eval compute in (simplify <$> (parse path_dirname "/home/coq/../coqide/./x/../ ")).

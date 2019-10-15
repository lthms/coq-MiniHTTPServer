From Praecia Require Import Parser.

Axiom of_ascii_list : list ascii -> string.

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

Definition http_request : parser (string * path) :=
  do var method <- str "GET" in
     whitespaces;
     var path <- read_path in
     whitespaces;
     str "HTTP/1.1";

     pure (method, path)
  end.

Eval vm_compute in (parse http_request "GET /etc/passwd HTTP/1.1"%string).
Eval vm_compute in (parse http_request "GET /etc/passwd HTP/1.1"%string).
Eval vm_compute in (parse http_request "PUT /etc/passwd HTTP/1.1"%string).

From Praecia Require Import Parser.

Definition http_request : parser (string * string) :=
  do var method <- til_charc " " in
     whitespaces;
     var path <- til_charc " " in
     whitespaces;
     str "HTTP/1.1"%string;

     pure (method, path)
  end.

Eval vm_compute in (parse http_request "GET /etc/passwd HTTP/1.1"%string).
Eval vm_compute in (parse http_request "GET /etc/passwd HTP/1.1"%string).

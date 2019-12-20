From FreeSpec Require Import Core.

Inductive EVAL (a : Type) : Type :=
| Eval (x : a) : EVAL a.

Arguments Eval [a] (x).

Register EVAL as minihttpserver.eval.type.
Register Eval as minihttpserver.eval.Eval.

Definition eval `{Provide ix EVAL} {a} (x : a) : impure ix a :=
  request (Eval x).

From Coq Require Export String Ascii.
From Prelude Require Export Control.
From Prelude Require Import State Classes Either Equality.

#[global] Open Scope monad_scope.

Definition error_stack := list string.

Definition parser (a : Type) := state_t string (sum error_stack) a.

Definition with_context {a} (msg : string) (p : parser a) : parser a :=
  fun input =>
    match p input with
    | inl x => inl (cons msg x)
    | inr y => inr y
    end.

Definition parse {a} (parser : parser a) (input : string) : error_stack + a :=
  fst <$> (parser input).

Definition fail {a} (msg : string) : parser a :=
  fun s => inl (cons msg nil).

Definition read_char : parser ascii :=
  do var input <- get in
     match input with
     | String a rst => do put rst;
                          pure a
                       end
     | EmptyString => fail "expected character, found end of input"
     end
  end.

Definition char (a : ascii) : parser unit :=
  do var c <- read_char in
     if eqb a c
     then pure tt
     else fail "expected a character, found another" (* todo: easy string interpolation *)
  end.

Fixpoint str (a : string) : parser unit :=
  let fix str_aux (a : string) :=
      match a with
      | String c rst => do char c;
                           str_aux rst
      end
      | EmptyString => pure tt
      end
  in with_context "trying to consume a string" (str_aux a).

Inductive iter_step (a b : Type) : Type :=
| Continue (acc : a)
| Return (res : b).

Arguments Continue [a b] (acc).
Arguments Return [a b] (res).

#[local]
Fixpoint iter_aux {a b} (acc : a) (f : a -> ascii -> iter_step a b) (input : string)
  : option (b * string) :=
  match input with
  | String c rst =>
    match f acc c with
    | Continue x => iter_aux x f rst
    | Return b => Some (b, (String c rst))
    end
  | EmptyString => None
  end.

Definition iter {a b} (init : a) (f : a -> ascii -> iter_step a b) : parser b :=
  do var input <- get in
     match iter_aux init f input with
     | Some (x, rst) =>
       do put rst;
          pure x
        end
     | None => fail "found end of input before satisfying a predicate"
     end
  end.

Definition until (continue : ascii -> bool) : parser string :=
  do var cont <- iter id (fun (acc : string -> string) (c' : ascii) =>
                            if continue c'
                            then Return acc
                            else Continue (fun (s : string) => acc (String c' s)))
    in pure (cont EmptyString)
  end.

Definition untilc (continue : ascii -> bool) : parser string :=
  do var res <- until continue in
     read_char;
     pure res
  end.

Definition til_char (c : ascii) : parser string :=
  until (eqb c).

Definition til_charc (c : ascii) : parser string :=
  untilc (eqb c).

Definition whitespaces : parser unit :=
  do until (fun c => negb (eqb c " "));
     pure tt
  end.

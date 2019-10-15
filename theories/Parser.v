From Coq Require Export String Ascii Lia Program.Wf.
From Coq Require List.
From Prelude Require Export Control.
From Prelude Require Import State Classes Sum Equality Option.

Generalizable All Variables.

#[global] Open Scope monad_scope.

Notation "x '>>' y" := (x >>= fun _ => y) (at level 74, right associativity).
Notation "x '<*' y" := (x >>= fun r => (y >> pure r)) (at level 74, right associativity).
Notation "x '*>' y" := (x >> y) (at level 74, right associativity).

Definition error_stack := list string.

Definition parser (a : Type) := state_t string (sum error_stack) a.

Definition parse {a} (parser : parser a) (input : string) : error_stack + a :=
  fst <$> (parser input).

Class Parser {a} (p : parser a) : Prop :=
  { is_parser (input : string) :
      match p input with
      | inl _ => True
      | inr (_, output) => length output <= length input
      end
  }.

Class StrictParser {a} (p : parser a) : Prop :=
  { is_strict (input : string) :
      match p input with
      | inl _ => True
      | inr (_, output) => length output < length input
      end
  }.

#[program]
Instance strict_parser {a} (p : parser a) `{StrictParser a p}
  : Parser p.

Next Obligation.
  destruct H as [is_strict].
  specialize is_strict with input.
  destruct (p input) as [_|[x res]]; lia.
Qed.

#[program]
Instance bind_parser {a b} (p : parser a) (f : a -> parser b) `{Parser a p} `{forall x, Parser (f x)}
  : Parser (p >>= f).

Next Obligation.
  case_eq (p input).
  + now cbn.
  + intros [y input'] equ.
    assert (length input' <= length input). {
      destruct H as [is_parse].
      specialize is_parse with input.
      now rewrite equ in is_parse.
    }
    cbn.
    case_eq (f y input').
    ++ auto.
    ++ intros [z output] equ'.
       assert (length output <= length input'). {
         specialize H0 with y.
         destruct H0 as [is_parser].
         specialize is_parser with input'.
         now rewrite equ' in is_parser.
       }
       lia.
Qed.

#[program]
Instance bind_strict_1 {a b} (p : parser a) (f : a -> parser b) `{StrictParser a p} `{forall x, Parser (f x)}
  : StrictParser (p >>= f).

Next Obligation.
  case_eq (p input).
  + now cbn.
  + intros [y input'] equ.
    assert (length input' < length input). {
      destruct H as [is_strict].
      specialize is_strict with input.
      now rewrite equ in is_strict.
    }
    cbn.
    case_eq (f y input').
    ++ auto.
    ++ intros [z output] equ'.
       assert (length output <= length input'). {
         specialize H0 with y.
         destruct H0 as [is_parser].
         specialize is_parser with input'.
         now rewrite equ' in is_parser.
       }
       lia.
Qed.

#[program]
Instance bind_strict_2 {a b} (p : parser a) (f : a -> parser b) `{Parser a p} `{forall x, StrictParser (f x)}
  : StrictParser (p >>= f).

Next Obligation.
  case_eq (p input).
  + now cbn.
  + intros [y input'] equ.
    assert (length input' <= length input). {
      destruct H as [is_parser].
      specialize is_parser with input.
      now rewrite equ in is_parser.
    }
    cbn.
    case_eq (f y input').
    ++ auto.
    ++ intros [z output] equ'.
       assert (length output < length input'). {
         specialize H0 with y.
         destruct H0 as [is_strict].
         specialize is_strict with input'.
         now rewrite equ' in is_strict.
       }
       lia.
Qed.

Definition with_context {a} (msg : string) (p : parser a) : parser a :=
  fun input =>
    match p input with
    | inl x => inl (cons msg x)
    | inr y => inr y
    end.

#[program]
Instance with_context_parser {a} (p : parser a) `{Parser a p} (msg : string)
  : Parser (with_context msg p).

Next Obligation.
  unfold with_context.
  destruct H as [is_parser].
  specialize is_parser with input.
  now destruct (p input).
Qed.

#[program]
Instance with_context_strict {a} (p : parser a) `{StrictParser a p} (msg : string)
  : StrictParser (with_context msg p).

Next Obligation.
  unfold with_context.
  destruct H as [is_strict].
  specialize is_strict with input.
  now destruct (p input).
Qed.

Definition alt {a} (p q : parser a) : parser a :=
  fun input =>
    match p input with
    | inr x => inr x
    | inl _ => q input
    end.

Notation "p '<|>' q" := (alt p q) (at level 50, left associativity).

#[program]
Instance alt_strict {a} (p q : parser a) `{StrictParser a p} `{StrictParser a q}
  : StrictParser (p <|> q).

Next Obligation.
  unfold alt.
  destruct H as [is_strict_p].
  destruct H0 as [is_strict_q].
  specialize is_strict_p with input.
  specialize is_strict_q with input.
  now destruct (p input).
Qed.

#[program]
Instance alt_parser {a} (p q : parser a) `{Parser a p} `{Parser a q}
  : Parser (p <|> q).

Next Obligation.
  unfold alt.
  destruct H as [is_parser_p].
  destruct H0 as [is_parser_q].
  specialize is_parser_p with input.
  specialize is_parser_q with input.
  now destruct (p input).
Qed.

Definition fail {a} (msg : string) : parser a :=
  fun s => inl (cons msg nil).

#[program]
Instance fail_strict {a} (msg : string) : StrictParser (@fail a msg).

Definition read_char : parser ascii :=
  do var input <- get in
     match input with
     | String a rst => put rst >> pure a
     | EmptyString => fail "expected character, found end of input"
     end
  end.

#[program]
Instance pure_Parser {a} (x : a) : Parser (pure x).

#[program]
Instance get_Parser : Parser get.

#[program]
Instance read_char_strict : StrictParser read_char.

Next Obligation.
  cbn.
  destruct input.
  + now cbn.
  + cbn. lia.
Qed.

Definition char (a : ascii) : parser ascii :=
  do var c <- read_char in
     if eqb a c
     then pure a
     else fail "expected a character, found another" (* todo: easy string interpolation *)
  end.

#[program]
Instance if_parser {a} (cond : bool) (p q : parser a)
   `{Parser a p, Parser a q}
  : Parser (if cond then p else q).

Next Obligation.
  destruct cond; apply (is_parser input).
Qed.

#[program]
Remark char_strict (c : ascii) : StrictParser (char c).
Proof.
  typeclasses eauto.
Qed.

Fixpoint str_aux (a : string) : parser unit :=
  match a with
  | String c rst => char c *> str_aux rst
  | EmptyString => pure tt
  end.

Instance str_aux_parser (s : string) : Parser (str_aux s).

Proof.
  induction s.
  ++ apply pure_Parser.
  ++ change (str_aux (String a s)) with (char a *> str_aux s).
     apply bind_parser.
     +++ typeclasses eauto.
     +++ intros c.
         apply IHs.
Qed.

Instance str_aux_strict (a : ascii) (s : string) : StrictParser (str_aux (String a s)).

Proof.
  change (str_aux (String a s)) with (char a *> str_aux s).
  apply bind_strict_1; typeclasses eauto.
Qed.

Definition str (target : string) : parser string :=
  with_context "trying to consume a string" (str_aux target) *> pure target.

#[local, program]
Fixpoint many_aux {a} (acc : list a) (p : parser a) `{StrictParser a p}
    (input : string) {measure (length input)}
  : list a * string :=
  match p input with
  | inl _ => (List.rev acc, input)
  | inr (x, output) => many_aux (cons x acc) p output
  end.

Next Obligation.
  destruct H as [is_strict].
  specialize is_strict with input.
  now rewrite <- Heq_anonymous in is_strict.
Qed.

Definition many {a} (p : parser a) `{StrictParser a p} : parser (list a) :=
  fun (input : string) =>
     match many_aux nil p input with
     | (x, rst) => inr (x, rst)
     end.

#[program]
Instance many_parser `{StrictParser a p} : Parser (many p).

Next Obligation.
  unfold many.
  case_eq (many_aux nil p input); intros x rst equ.
  (* TODO *)
  admit.
Admitted.

Definition some {a} (p : parser a) `{StrictParser a p} : parser (list a) :=
  do var x <- p in
     var rst <- many p in
     pure (cons x rst)
  end.

Remark some_parser `(StrictParser a p) : StrictParser p.
typeclasses eauto.
Qed.

Definition whitespaces : parser (list ascii) :=
  many (char " ").

Remark whitespaces_parser : Parser whitespaces.
typeclasses eauto.
Qed.

Definition ensure {a} (p : parser a) (cond : a -> bool) : parser a :=
  do var res <- p in
     if cond res
     then pure res
     else fail "ensure: result of p is not valid according to cond"
  end.

Remark ensure_parser `{Parser a p} (cond : a -> bool) : Parser (ensure p cond).
typeclasses eauto.
Qed.

#[program]
Fixpoint many_until_aux {a b} (acc : list a)
    (p : parser a) `{StrictParser a p} (q : parser b)
    (input : string) {measure (length input)}
  : error_stack + (list a * string) :=
    match q input with
    | inl _ => match p input with
               | inl _ => inl (cons "p failed before q could succeed"%string nil)
               | inr (x, output) => many_until_aux (cons x acc) p q output
               end
    | inr (_, output) => inr (List.rev acc, output)
    end.

Next Obligation.
  admit.
Admitted.

Definition many_until {a b} (p : parser a) `{StrictParser a p} (q : parser b)
  : parser (list a) :=
  many_until_aux nil p q.

#[program]
Instance many_until_parser `(StrictParser a p, Parser b q) : Parser (many_until p q).

Next Obligation.
Admitted.

#[program]
Instance many_until_strict `(StrictParser a p, StrictParser b q) : StrictParser (many_until p q).

Next Obligation.
Admitted.

Definition some_until {a b} (p : parser a) `{StrictParser a p} (q : parser b)
  : parser (list a) :=
  cons <$> p <*> many_until p q.

#[program]
Instance map_parser {a b} (f : a -> b) `(Parser a p) : Parser (f <$> p).

Next Obligation.
  unfold state_map.
  case_eq (p input).
  + now cbn.
  + intros [x output] equ.
    cbn.
    destruct H as [is_parser].
    specialize is_parser with input.
    now rewrite equ in is_parser.
Qed.

#[program]
Instance map_strict {a b} (f : a -> b) `(StrictParser a p) : StrictParser (f <$> p).

Next Obligation.
  unfold state_map.
  case_eq (p input).
  + now cbn.
  + intros [x output] equ.
    cbn.
    destruct H as [is_strict].
    specialize is_strict with input.
    now rewrite equ in is_strict.
Qed.

#[program]
Instance app_parser `(Parser (a -> b) f) `(Parser a p) : Parser (f <*> p).

Next Obligation.
  case_eq (f input).
  + now cbn.
  + intros [fp input'] equ.
    assert (length input' <= length input). {
      destruct H as [is_parser].
      specialize is_parser with input.
      now rewrite equ in is_parser.
    }
    cbn.
    case_eq (p input').
    ++ admit.
    ++ admit.
Admitted.

#[program]
Instance app_strict_1 `(StrictParser (a -> b) f, Parser a p) : StrictParser (f <*> p).

Next Obligation.
Admitted.

#[program]
Instance app_strict_2 `(Parser (a -> b) f, StrictParser a p) : StrictParser (f <*> p).

Next Obligation.
Admitted.

Remark some_until_strict `(StrictParser a p, Parser b q) : StrictParser (some_until p q).
typeclasses eauto.
Qed.

Definition eoi : parser unit :=
  ensure (length <$> get) (Nat.eqb 0) >> pure tt.

#[program]
Instance eoi_parser : Parser eoi.

Next Obligation.
  induction input; now cbn.
Qed.

Definition peak {a} (p : parser a) : parser a :=
  fun (input : string) =>
    match p input with
    | inl x => inl x
    | inr (x, _) => inr (x, input)
    end.

#[program]
Instance peak_parser {a} (p : parser a) : Parser (peak p).

Next Obligation.
  unfold peak.
  destruct (p input) as [ _ | [x output] ]; auto.
Qed.

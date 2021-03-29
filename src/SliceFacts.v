From MiniHTTPServerFFI Require Import Slice StrExt.
From Comparse Require Import Monad Combinators.

Instance slice_input : Input Slice.t ascii :=
  { unpack := Slice.unpack
  ; input_to_string := Slice.to_string
  ; token_to_string := StrExt.char_to_string
  }.

Axiom slice_length : Slice.t -> nat.

Axiom slice_laws : InputLaws Slice.t ascii slice_length.

#[global] Existing Instance slice_laws.

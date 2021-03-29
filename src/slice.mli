type t

val of_string : string -> t

val of_char : char -> t

val to_string : t -> string

val length : t -> int

val unpack : t -> (char * t) option

val take : t -> int -> (t * t) option

val pack : char list -> t

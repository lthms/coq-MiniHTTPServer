type file_descriptor = Unix.file_descr

val open_file : Bytestring.t -> file_descriptor [@@impure]
val file_exists : Bytestring.t -> bool [@@impure]
val read : file_descriptor -> Bytestring.t [@@impure]
val close : file_descriptor -> unit [@@impure]

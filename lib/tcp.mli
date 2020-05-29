type socket_descriptor = Unix.file_descr

val new_tcp_socket : Bytestring.t -> socket_descriptor [@@impure]
val listen_incoming_connection : socket_descriptor -> unit [@@impure]
val read_socket : socket_descriptor -> Bytestring.t [@@impure]
val write_socket : socket_descriptor -> Bytestring.t -> unit [@@impure]
val close_socket : socket_descriptor -> unit [@@impure]
val accept_connection : socket_descriptor -> socket_descriptor [@@impure]

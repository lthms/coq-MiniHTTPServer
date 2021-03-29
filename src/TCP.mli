type socket

val new_tcp_socket : string -> socket
(** [new_tcp_socket addr] creates a [socket], where [addr] is of the
    form {v [url]:[port] v}. *)

val listen_incoming_connection : socket -> unit
(** [listen_incoming_connection sck] changes the mode of the socket
    [sck], effectively creating a server. *)

val accept_connection : socket -> socket
(** [accept_connection sck] waits for [sck] to receive an incoming connection,
    and returns a [socket] to interact with the new client. *)

val read_socket : socket -> string
(** [read_socket sck] waits for the client behind [sck] to send data
    (interpreted as a [string]). *)

val write_socket : socket -> string -> unit
(** [write_socket sck msg] sends [msg] to the client behind [sck]. *)

val close_tcp_socket : socket -> unit
(** [close_tcp_socket sck] interupts an existing connection by closing
    the link between the server and the client. *)

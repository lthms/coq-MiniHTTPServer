From Coq Require Export String.
From FreeSpec Require Export Core Exec.


Generalizable All Variables.

Axiom socket_descriptor : Type.

Inductive TCP : interface :=
| NewTCPSocket (addr : string) : TCP socket_descriptor
| ListenIncomingConnection (socket : socket_descriptor) : TCP unit
| AcceptConnection (socket : socket_descriptor) : TCP socket_descriptor
| ReadSocket (socket : socket_descriptor) : TCP string
| WriteSocket (socket : socket_descriptor) (msg : string) : TCP unit
| CloseTCPSocket (socket : socket_descriptor) : TCP unit.

Register TCP as praecia.tcp.type.
Register NewTCPSocket as praecia.tcp.NewTCPSocket.
Register ListenIncomingConnection as praecia.tcp.ListenIncomingConnection.
Register AcceptConnection as praecia.tcp.AcceptConnection.
Register ReadSocket as praecia.tcp.ReadSocket.
Register WriteSocket as praecia.tcp.WriteSocket.
Register CloseTCPSocket as praecia.tcp.CloseTCPSocket.

Definition new_tcp_socket `{Provide ix TCP} (addr : string) : impure ix socket_descriptor :=
  request (NewTCPSocket addr).

Definition listen_incoming_connection `{Provide ix TCP} (socket : socket_descriptor) : impure ix unit :=
  request (ListenIncomingConnection socket).

Definition accept_connection `{Provide ix TCP} (socket : socket_descriptor) : impure ix socket_descriptor :=
  request (AcceptConnection socket).

Definition read_socket `{Provide ix TCP} (socket : socket_descriptor) : impure ix string :=
  request (ReadSocket socket).

Definition write_socket `{Provide ix TCP} (socket : socket_descriptor) (msg : string) : impure ix unit :=
  request (WriteSocket socket msg).

Definition close_socket `{Provide ix TCP} (socket : socket_descriptor) : impure ix unit :=
  request (CloseTCPSocket socket).

Declare ML Module "praecia_plugin".

Fixpoint repeatM `{Monad m} {a} (n : nat) (p : m a) : m unit :=
  match n with
  | O => pure tt
  | S n => p >>= fun _ => repeatM n p
  end.

Definition tcp_server `{Provide ix TCP} (handler : string -> impure ix string)
  : impure ix unit :=
  do var server <- new_tcp_socket "127.0.0.1:8088" in
     listen_incoming_connection server;

     repeatM 100 do
       var client <- accept_connection server in

       var req <- read_socket client in
       var res <- handler req in
       write_socket client res;

       close_socket client
     end;

     close_socket server
  end.

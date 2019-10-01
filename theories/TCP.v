From Coq Require Export String.
From FreeSpec Require Export Core.

Generalizable All Variables.

Axiom socket_descriptor : Type.

Inductive TCP : interface :=
| NewTCPSocket (addr : string) : TCP socket_descriptor
| ListenIncomingConnection (socket : socket_descriptor) : TCP unit
| AcceptConnection (socket : socket_descriptor) : TCP socket_descriptor
| ReadSocket (socket : socket_descriptor) : TCP string
| WriteSocket (socket : socket_descriptor) (msg : string) : TCP unit
| CloseTCPSocket (socket : socket_descriptor) : TCP unit.

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

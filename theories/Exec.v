From FreeSpec Require Import Core.All Exec.All.
From MiniHTTPServer Require Import App.

(*
Register TCP as minihttpserver.tcp.type.
Register New_TCPSocket as minihttpserver.tcp.NewTCPSocket.
Register ListenIncomingConnection as minihttpserver.tcp.ListenIncomingConnection.
Register AcceptConnection as minihttpserver.tcp.AcceptConnection.
Register ReadSocket as minihttpserver.tcp.ReadSocket.
Register WriteSocket as minihttpserver.tcp.WriteSocket.
Register CloseTCPSocket as minihttpserver.tcp.CloseTCPSocket.

Register FILESYSTEM as minihttpserver.filesystem.type.
Register Open as minihttpserver.filesystem.Open.
Register FileExists as minihttpserver.filesystem.FileExists.
Register Read as minihttpserver.filesystem.Read.
Register Close as minihttpserver.filesystem.Close.

Declare ML Module "coqbase".
Declare ML Module "minihttpserver_lib".
Declare ML Module "minihttpserver_plugin".
*)

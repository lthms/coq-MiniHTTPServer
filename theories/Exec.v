From FreeSpec Require Import Core Exec.
From MiniHTTPServer Require Import App.

Register TCP as minihttpserver.tcp.type.
Register NewTCPSocket as minihttpserver.tcp.NewTCPSocket.
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

Register EVAL as minihttpserver.eval.type.
Register Eval as minihttpserver.eval.Eval.

Declare ML Module "minihttpserver_plugin".

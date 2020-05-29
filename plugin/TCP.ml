(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

open Freespec_exec.Coqbytestring
open Freespec_exec.Extends
open Freespec_exec.Coqunit
open Minihttpserver_lib

let path = "minihttpserver.tcp"

let constr_of_socket socket =
  Constr.(of_kind (Int (Uint63.of_int (Obj.magic socket))))

let of_coqstring s = bytestring_of_coqbytestring s
let to_coqstring s = bytestring_to_coqbytestring s

let socket_of_constr c =
  match Constr.kind c with
  | Constr.Int i -> (Obj.magic (snd (Uint63.to_int2 i)) : Unix.file_descr)
  | _ -> assert false

let new_tcp_socket = function
  | [addr] ->
    of_coqstring addr |> Tcp.new_tcp_socket |> constr_of_socket
  | _ -> assert false

let listen_incoming_connection = function
  | [socket] ->
    socket_of_constr socket |> Tcp.listen_incoming_connection |> (fun _ -> coqtt)
  | _ -> assert false

let accept_connection = function
  | [socket] ->
    socket_of_constr socket |> Tcp.accept_connection |> constr_of_socket
  | _ -> assert false

let read_socket = function
  | [socket] ->
     socket_of_constr socket |> Tcp.read_socket |> to_coqstring
  | _ ->
     assert false

let write_socket = function
  | [socket; str] ->
     Tcp.write_socket (socket_of_constr socket)  (of_coqstring str);
     coqtt
  | _ ->
     assert false

let close_tcp_socket = function
  | [socket] ->
    socket_of_constr socket |> Tcp.close_socket |> (fun _ -> coqtt)
  | _ ->
     assert false

let install_interface =
  register_interface path [
      ("NewTCPSocket",             new_tcp_socket);
      ("ListenIncomingConnection", listen_incoming_connection);
      ("AcceptConnection",         accept_connection);
      ("ReadSocket",               read_socket);
      ("WriteSocket",              write_socket);
      ("CloseTCPSocket",           close_tcp_socket)
    ]

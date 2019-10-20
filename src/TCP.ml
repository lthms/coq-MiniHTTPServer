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

open Freespec_exec.Coqstr
open Freespec_exec.Extends
open Freespec_exec.Coqunit
open Utils

let path = "praecia.filesystem"

let parse_address addr =
  match Str.(split (regexp ":") addr) with
  | [hostname; port] -> (Unix.inet_addr_of_string hostname, int_of_string port)
  | _ -> failwith "Invalid address"

let constr_of_socket socket =
  Constr.(of_kind (Int (Uint63.of_int (Obj.magic socket))))

let socket_of_constr c =
  match Constr.kind c with
  | Constr.Int i -> (Obj.magic (snd (Uint63.to_int2 i)) : Unix.file_descr)
  | _ -> assert false

let new_tcp_socket = function
  | [addr] ->
     let addr = string_of_coqstr addr in
     let hostname, port = parse_address addr in
     let fd = Unix.(socket PF_INET SOCK_STREAM 0) in
     Unix.setsockopt fd SO_REUSEADDR true;
     Unix.(bind fd (ADDR_INET (hostname, port)));
     constr_of_socket fd
  | _ -> assert false

let listen_incoming_connection = function
  | [socket] ->
     Unix.listen (socket_of_constr socket) 1;
     coqtt
  | _ -> assert false

let accept_connection = function
  | [socket] ->
     let new_socket, _ = Unix.accept (socket_of_constr socket) in
     constr_of_socket new_socket
  | _ -> assert false

let read_socket = function
  | [socket] ->
     read_all_from (socket_of_constr socket) |>
     string_to_coqstr
  | _ ->
     assert false

let write_all_from data fd =
  let rec aux ofs len =
    let n = Unix.write fd data ofs len in
    if n < len then aux (ofs + n) (len - n)
  in
  aux 0 (Bytes.length data)

let write_socket = function
  | [socket; str] ->
     write_all_from (bytes_of_coqstr str) (socket_of_constr socket);
     coqtt
  | _ ->
     assert false

let close_tcp_socket = function
  | [socket] ->
     Unix.close (socket_of_constr socket);
     coqtt
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

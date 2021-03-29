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

type socket = Unix.file_descr

let parse_address addr =
  match Str.(split (regexp ":") addr) with
  | [hostname; port] -> (Unix.inet_addr_of_string hostname, int_of_string port)
  | _ -> failwith "Invalid address"

let new_tcp_socket addr =
  let hostname, port = parse_address addr in
  let fd = Unix.(socket PF_INET SOCK_STREAM 0) in
  Unix.setsockopt fd SO_REUSEADDR true;
  Unix.(bind fd (ADDR_INET (hostname, port)));
  fd

let listen_incoming_connection socket =
  Unix.listen socket 1

let accept_connection socket =
  let new_socket, _ = Unix.accept socket in
  new_socket

let read_socket socket = ExtUnix.read_all_from socket

let write_all_from data fd =
  let rec aux ofs len =
    let n = Unix.write_substring fd data ofs len in
    if n < len then aux (ofs + n) (len - n)
  in
  aux 0 (String.length data)

let write_socket socket str =
  write_all_from str socket

let close_tcp_socket = Unix.close

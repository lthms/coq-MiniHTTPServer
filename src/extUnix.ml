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

let max_buffer_len = 1024

let read_all_from ?(line = true) fd =
  let char = Bytes.create 1 in
  let buffer = Buffer.create max_buffer_len in
  let rec aux () =
    let n = Unix.(handle_unix_error (fun () -> read fd char 0 1)) () in
    if n > 0 then Buffer.add_subbytes buffer char 0 n;
    let eol = line && Bytes.get char 0 = '\n' in
    if n > 0 && not eol then aux () else Buffer.contents buffer
  in
  aux ()

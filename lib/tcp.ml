open ExtUnix

type socket_descriptor = Unix.file_descr

let parse_address addr =
  match Str.(split (regexp ":") addr) with
  | [hostname; port] -> (Unix.inet_addr_of_string hostname, int_of_string port)
  | _ -> failwith "Invalid address"

let new_tcp_socket addr =
  let hostname, port = parse_address (Bytestring.to_string addr) in
  let fd = Unix.(socket PF_INET SOCK_STREAM 0) in
  Unix.setsockopt fd SO_REUSEADDR true;
  Unix.(bind fd (ADDR_INET (hostname, port)));
  fd

let listen_incoming_connection socket =
  Unix.listen socket 1

let read_socket socket = read_all_from socket |> Bytestring.of_string

let write_socket socket data =
  write_all_to socket (Bytes.of_string @@ Bytestring.to_string data)

let close_socket socket = Unix.close socket

let accept_connection socket =
  let new_socket, _ = Unix.accept socket in
  new_socket

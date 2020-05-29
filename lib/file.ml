type file_descriptor = Unix.file_descr

let open_file path = Unix.openfile (Bytestring.to_string path) [ O_RDONLY ] 0

let file_exists path = Bytestring.to_string path |> Sys.file_exists

let read fd = ExtUnix.read_all_from ~line:false fd |> Bytestring.of_string

let close = Unix.close

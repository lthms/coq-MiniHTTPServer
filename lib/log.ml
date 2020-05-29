open Coqbase

let echo msg = print_string @@ Bytestring.to_string msg

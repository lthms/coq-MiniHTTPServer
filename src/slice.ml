type t = { str_buffer : string; str_offset : int; str_len : int }

let of_string s = { str_buffer = s; str_offset = 0; str_len = String.length s }

let to_string { str_buffer; str_offset; str_len } =
  if str_len = String.length str_buffer then str_buffer
  else String.init str_len (fun idx -> String.get str_buffer (idx + str_offset))

let of_char c = Strext.char_to_string c |> of_string

let length t = t.str_len

let unpack { str_buffer; str_offset; str_len } =
  if 0 < str_len then
    Some
      ( String.get str_buffer str_offset,
        { str_buffer; str_offset = str_offset + 1; str_len = str_len - 1 } )
  else None

let take { str_buffer; str_offset; str_len } x =
  if x <= str_len then
    Some
      ( { str_buffer; str_offset; str_len = x },
        { str_buffer; str_offset = str_offset + x; str_len = str_len - x } )
  else None

let pack l =
  let str_len = List.length l in
  let str_buffer = String.init str_len (List.nth l) in
  { str_buffer; str_offset = 0; str_len }

From Prelude Require Import Option Bytes.
From FreeSpec Require Import Exec Console.
From MiniHTTPServer Require Import HTTP URI.

Exec do
  match http_request b#"GET /test/../.././ HTTP/1.1" with
  | inr (Get uri, _) => echo ("Parsing succeeded: " ++ uri_to_path (make_uri (canonicalize (dirname uri))
                                                                             (filename uri))
                                                    ++ "\n")

  | inl (x :: _) => echo ("Error while parsing\n")
  | inl _ => echo "Error while parsing"
  end
end.

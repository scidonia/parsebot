(* Driver: build a large HTTP/1.1 chunked body, feed it to the extracted
   parse_chunked_body (char list -> char list option), time it.

   Body layout per RFC 9112 §7.1: *chunk last-chunk CRLF, where each data
   chunk is  size CRLF data CRLF  and the last chunk is  0 CRLF CRLF. *)

let hex_digit n =
  if n < 10 then Char.chr (Char.code '0' + n)
  else Char.chr (Char.code 'a' + n - 10)

let hex_of_int (n : int) : string =
  let rec go n acc =
    if n = 0 then (if acc = "" then "0" else acc)
    else go (n / 16) (String.make 1 (hex_digit (n mod 16)) ^ acc)
  in
  go n ""

let rec of_string (s : string) (i : int) (acc : char list) : char list =
  if i < 0 then acc else of_string s (i - 1) (s.[i] :: acc)

let rec list_len acc = function
  | [] -> acc
  | _ :: t -> list_len (acc + 1) t

(* nchunks data chunks of payload_size bytes each, then the terminating
   0 CRLF CRLF.  Returns the input as a char list plus the total byte count. *)
let build_body (nchunks : int) (payload_size : int) : char list * int =
  let buf = Buffer.create (nchunks * (payload_size + 32)) in
  let payload = String.make payload_size 'x' in
  let size_hex = hex_of_int payload_size in
  let chunk_header = size_hex ^ "\r\n" in
  let total = ref 0 in
  for _ = 1 to nchunks do
    Buffer.add_string buf chunk_header;
    Buffer.add_string buf payload;
    Buffer.add_string buf "\r\n";
    total := !total + String.length chunk_header + payload_size + 2
  done;
  Buffer.add_string buf "0\r\n\r\n";
  total := !total + 5;
  (of_string (Buffer.contents buf) (Buffer.length buf - 1) [], !total)

let () =
  let nchunks = int_of_string Sys.argv.(1) in
  let payload_size = int_of_string Sys.argv.(2) in
  let w, input_bytes = build_body nchunks payload_size in
  Printf.printf "input: %d chunks x %d bytes = %d bytes\n%!"
    nchunks payload_size input_bytes;
  let t0 = Sys.time () in
  let r = Chunked.parse_chunked_body w in
  let t1 = Sys.time () in
  (match r with
   | None -> Printf.printf "decode: FAIL\n"
   | Some data -> Printf.printf "decode: OK, %d bytes\n" (list_len 0 data));
  let dt = t1 -. t0 in
  Printf.printf "time: %.3f s\n" dt;
  if dt > 0.0 then
    Printf.printf "throughput: %.1f MB/s\n" (float_of_int input_bytes /. dt /. 1_048_576.0)

(* Driver: read a TOML file, feed it to the extracted parse_doc (surface
   parser), parse_then_validate (parse + state-machine run), and direct_parse
   (interleaved), time each.  After extraction, nat/big_int are arbitrary
   precision (Big_int_Z over Zarith); ascii is char. *)

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let rec of_string (s : string) (i : int) (acc : char list) : char list =
  if i < 0 then acc else of_string s (i - 1) (s.[i] :: acc)

let mb_s (bytes : int) (dt : float) : float =
  float_of_int bytes /. dt /. 1_048_576.0

let () =
  let path = Sys.argv.(1) in
  let s = read_file path in
  let w = of_string s (String.length s - 1) [] in
  let n = String.length s in
  let fuel = Big_int_Z.big_int_of_int (2 * n + 1) in
  Printf.printf "input bytes: %d\n%!" n;
  (* 1. surface parser only *)
  let t0 = Sys.time () in
  let d = Toml.parse_doc fuel w in
  let t1 = Sys.time () in
  (match d with
   | None -> Printf.printf "parse_doc: FAIL\n"
   | Some doc -> Printf.printf "parse_doc: OK (%d stmts)\n" (List.length doc));
  Printf.printf "parse_doc time: %.3f s (%.1f MB/s)\n" (t1 -. t0) (mb_s n (t1 -. t0));
  (* 2. parse-then-validate: surface parse + state-machine run *)
  let t2 = Sys.time () in
  let r = Toml.parse_then_validate w in
  let t3 = Sys.time () in
  (match r with
   | None -> Printf.printf "parse_then_validate: FAIL\n"
   | Some ns -> Printf.printf "parse_then_validate: OK (%d bindings)\n" (List.length ns));
  Printf.printf "parse_then_validate time: %.3f s (%.1f MB/s)\n" (t3 -. t2) (mb_s n (t3 -. t2));
  (* 3. direct (interleaved) parse *)
  let t4 = Sys.time () in
  let r2 = Toml.direct_parse fuel [] w in
  let t5 = Sys.time () in
  (match r2 with
   | None -> Printf.printf "direct_parse: FAIL\n"
   | Some ns -> Printf.printf "direct_parse: OK (%d bindings)\n" (List.length ns));
  Printf.printf "direct_parse time: %.3f s (%.1f MB/s)\n" (t5 -. t4) (mb_s n (t5 -. t4))

(* Driver: compare the list-based surface parser (parse_doc) against the
   buffer-based one (parse_doc_at).  Both are extracted with nat -> int, so
   the only difference is input representation: char list vs. (int -> char)
   accessor over a flat string. *)

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
  let n = String.length s in
  let w = of_string s (n - 1) [] in
  let fuel = 2 * n + 1 in
  Printf.printf "input bytes: %d\n%!" n;

  let t0 = Sys.time () in
  let d1 = Buffer.parse_doc fuel w in
  let t1 = Sys.time () in
  (match d1 with
   | None -> Printf.printf "parse_doc (list): FAIL\n"
   | Some doc -> Printf.printf "parse_doc (list): OK (%d stmts)\n" (List.length doc));
  Printf.printf "  list   : %.3f s  %.1f MB/s\n" (t1 -. t0) (mb_s n (t1 -. t0));

  let t2 = Sys.time () in
  let d2 = Buffer.parse_doc_at fuel (fun i -> s.[i]) 0 n in
  let t3 = Sys.time () in
  (match d2 with
   | None -> Printf.printf "parse_doc_at (buffer): FAIL\n"
   | Some doc -> Printf.printf "parse_doc_at (buffer): OK (%d stmts)\n" (List.length doc));
  Printf.printf "  buffer : %.3f s  %.1f MB/s\n" (t3 -. t2) (mb_s n (t3 -. t2));

  match d1, d2 with
  | Some a, Some b -> Printf.printf "agree: %b\n" (a = b)
  | None, None -> Printf.printf "agree: true (both fail)\n"
  | _ -> Printf.printf "MISMATCH!\n"

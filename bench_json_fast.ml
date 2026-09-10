(* Benchmark: zero-copy parse_json_fast (buffer = string, span-recorded) vs
   the certified list-based parse_json.  Correctness (parse_json_fast refines
   parse_json via decode) is proven in JsonFast.v; here we only time. *)

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

let summarize_fast (j : Json_fast.json_fast) : string =
  match j with
  | Json_fast.JNull_f -> "null"
  | Json_fast.JBool_f _ -> "bool"
  | Json_fast.JNum_f _ -> "num(span)"
  | Json_fast.JStr_f _ -> "str(span)"
  | Json_fast.JArr_f xs -> Printf.sprintf "array[%d]" (List.length xs)
  | Json_fast.JObj_f ms -> Printf.sprintf "object[%d]" (List.length ms)

(* Warm up, then time k runs (wall clock, µs); report the minimum per-run time. *)
let bench (k : int) (f : unit -> 'a option) : 'a option * float =
  for _ = 1 to 3 do ignore (f ()) done;
  let best = ref infinity in
  let r = ref None in
  for _ = 1 to k do
    let t0 = Unix.gettimeofday () in
    let v = f () in
    let t1 = Unix.gettimeofday () in
    let dt = t1 -. t0 in
    if dt < !best then best := dt;
    r := v
  done;
  (!r, !best)

let () =
  let path = Sys.argv.(1) in
  let s = read_file path in
  let n = String.length s in
  let w = of_string s (n - 1) [] in
  Printf.printf "input bytes: %d\n%!" n;

  let rf, dt_fast = bench 20 (fun () -> Json_fast.parse_json_fast s) in
  (match rf with
   | None -> Printf.printf "parse_json_fast      : FAIL\n"
   | Some v -> Printf.printf "parse_json_fast      : OK   %s\n" (summarize_fast v));
  Printf.printf "  zero-copy tokenize   %8.4f s  %8.1f MB/s\n" dt_fast (mb_s n dt_fast);

  let rr, dt_ref = bench 20 (fun () -> Json.parse_json w) in
  (match rr with
   | None -> Printf.printf "parse_json (list)    : FAIL\n"
   | Some _ -> Printf.printf "parse_json (list)    : OK\n");
  Printf.printf "  certified list-based %8.4f s  %8.1f MB/s\n" dt_ref (mb_s n dt_ref);

  Printf.printf "speedup (tokenize vs list): %.2fx\n" (dt_ref /. dt_fast);

  (* decode materializes spans -> full json.  span_to_list is now extracted to
     an O(len) String.sub slice (see span_to_list_nth in JsonFast.v). *)
  let rd, dt_dec = bench 20 (fun () ->
      match Json_fast.parse_json_fast s with
      | Some v -> Some (Json_fast.decode s v)
      | None -> None) in
  (match rd with
   | None -> Printf.printf "parse_json_fast+dec  : FAIL\n"
   | Some _ -> Printf.printf "parse_json_fast+dec  : OK\n");
  Printf.printf "  + decode (full json)  %8.4f s  %8.1f MB/s\n" dt_dec (mb_s n dt_dec);
  Printf.printf "speedup (tokenize+decode vs list): %.2fx\n" (dt_ref /. dt_dec)

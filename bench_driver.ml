(* Driver: read a JSON file, feed it to the extracted parse_json, time it.
   After extraction directives, parse_json : char list -> json option
   with arbitrary-precision numbers (Big_int_Z.big_int = Zarith Z.t). *)

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let rec of_string (s : string) (i : int) (acc : char list) : char list =
  if i < 0 then acc else of_string s (i - 1) (s.[i] :: acc)

let rec list_len acc = function [] -> acc | _ :: t -> list_len (acc + 1) t

let summarize (j : Json.json) : string =
  match j with
  | Json.JNull -> "null"
  | Json.JBool _ -> "bool"
  | Json.JNumber n -> Printf.sprintf "number(%s)" (Big_int_Z.string_of_big_int n)
  | Json.JString _ -> "string"
  | Json.JArray xs -> Printf.sprintf "array[%d]" (list_len 0 xs)
  | Json.JObject xs -> Printf.sprintf "object[%d]" (list_len 0 xs)

let () =
  let path = Sys.argv.(1) in
  let s = read_file path in
  let w = of_string s (String.length s - 1) [] in
  Printf.printf "input bytes: %d\n" (String.length s);
  let t0 = Sys.time () in
  let r = Json.parse_json w in
  let t1 = Sys.time () in
  (match r with
   | None -> Printf.printf "parse: FAIL\n"
   | Some v -> Printf.printf "parse: OK (%s)\n" (summarize v));
  Printf.printf "time: %.3f s\n" (t1 -. t0)

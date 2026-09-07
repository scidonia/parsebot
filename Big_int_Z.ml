(* Hand-written companion module for Rocq extraction: a Big_int-compatible API
   over Zarith's Z.t.  Rocq's ExtrOcamlNatBigInt / ExtrOcamlZBigInt map nat, N,
   positive and Z to Big_int_Z.big_int; this file provides the concrete type
   and operations (Zarith, per the extracted-code convention). *)

type big_int = Z.t

let zero_big_int = Z.zero
let unit_big_int = Z.one
let succ_big_int = Z.succ
let pred_big_int = Z.pred
let add_big_int = Z.add
let mult_big_int = Z.mul
let minus_big_int = Z.neg
let eq_big_int = Z.equal
let le_big_int = Z.leq
let sign_big_int = Z.sign
let big_int_of_int = Z.of_int
let string_of_big_int = Z.to_string
let mult_int_big_int (i : int) (b : big_int) : big_int = Z.mul (Z.of_int i) b
let quomod_big_int (a : big_int) (b : big_int) : big_int * big_int = Z.ediv_rem a b

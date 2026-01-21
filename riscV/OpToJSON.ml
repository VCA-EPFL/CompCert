(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printing of operators, conditions, addressing modes *)

open Printf
open Camlcoq
open Integers
open Op

let comparison_name = function
  | Ceq -> "Ceq"
  | Cne -> "Cne"
  | Clt -> "Clt"
  | Cle -> "Cle"
  | Cgt -> "Cgt"
  | Cge -> "Cge"

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Ccomp\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Ccompu\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "{\"type\": \"Ccompimm\", \"comparison\": \"%s\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (comparison_name c) (camlint_of_coqint n) reg r1
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "{\"type\": \"Ccompuimm\", \"comparison\": \"%s\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (comparison_name c) (camlint_of_coqint n) reg r1
  | (Ccompf c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Ccompf\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Ccompl c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Ccompl\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Ccomplu c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Ccomplu\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Ccomplimm(c, n), [r1]) ->
      fprintf pp "{\"type\": \"Ccomplimm\", \"comparison\": \"%s\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (comparison_name c) (camlint_of_coqint n) reg r1
  | (Ccompluimm(c, n), [r1]) ->
      fprintf pp "{\"type\": \"Ccompluimm\", \"comparison\": \"%s\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (comparison_name c) (camlint_of_coqint n) reg r1
  | (Cnotcompf c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Cnotcompf\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Ccompfs c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Ccompfs\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | (Cnotcompfs c, [r1;r2]) ->
      fprintf pp "{\"type\": \"Cnotcompfs\", \"comparison\": \"%s\", \"regs\": [\"%a\", \"%a\"]}" (comparison_name c) reg r1 reg r2
  | _ ->
      fprintf pp "<bad condition>"

let print_operation reg pp = function
  | Omove, [r1] -> fprintf pp "{\"type\": \"Omove\", \"regs\": [\"%a\"]}" reg r1
  | Ointconst n, [] -> fprintf pp "{\"type\": \"Ointconst\", \"args\": [\"%ld\"]}" (camlint_of_coqint n)
  | Olongconst n, [] -> fprintf pp "{\"type\": \"Olongconst\", \"args\": [\"%ld\"]}" (camlint_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "{\"type\": \"Ofloatconst\", \"args\": [\"%F\"]}" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "{\"type\": \"Osingleconst\", \"args\": [\"%F\"]}" (camlfloat_of_coqfloat32 n)
  | Oaddrsymbol(id, ofs), [] ->
     fprintf pp "{\"type\": \"Oaddrsymbol\", \"args\": [\"%s\", \"%Ld\"]}" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Oaddrstack ofs, [] ->
     fprintf pp "{\"type\": \"Oaddrstack\", \"args\": [\"%Ld\"]}" (camlint64_of_ptrofs ofs)
  | Ocast8signed, [r1] -> fprintf pp "{\"type\": \"Ocast8signed\", \"regs\": [\"%a\"]}" reg r1
  | Ocast16signed, [r1] -> fprintf pp "{\"type\": \"Ocast16signed\", \"regs\": [\"%a\"]}" reg r1
  | Oadd, [r1;r2] -> fprintf pp "{\"type\": \"Oadd\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "{\"type\": \"Oaddimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oneg, [r1] -> fprintf pp "{\"type\": \"Oneg\", \"regs\": [\"%a\"]}" reg r1
  | Osub, [r1;r2] -> fprintf pp "{\"type\": \"Osub\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omul, [r1;r2] -> fprintf pp "{\"type\": \"Omul\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omulhs, [r1;r2] -> fprintf pp "{\"type\": \"Omulhs\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "{\"type\": \"Omulhu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Odiv, [r1;r2] -> fprintf pp "{\"type\": \"Odiv\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "{\"type\": \"Odivu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omod, [r1;r2] -> fprintf pp "{\"type\": \"Omod\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omodu, [r1;r2] -> fprintf pp "{\"type\": \"Omodu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "{\"type\": \"Oand\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "{\"type\": \"Oandimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oor, [r1;r2] -> fprintf pp "{\"type\": \"Oor\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oorimm n, [r1] -> fprintf pp "{\"type\": \"Oorimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oxor, [r1;r2] -> fprintf pp "{\"type\": \"Oxor\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "{\"type\": \"Oxorimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oshl, [r1;r2] -> fprintf pp "{\"type\": \"Oshl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "{\"type\": \"Oshlimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oshr, [r1;r2] -> fprintf pp "{\"type\": \"Oshr\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "{\"type\": \"Oshrimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oshru, [r1;r2] -> fprintf pp "{\"type\": \"Oshru\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "{\"type\": \"Oshruimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oshrximm n, [r1] -> fprintf pp "{\"type\": \"Oshrximm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1

  | Omakelong, [r1;r2] -> fprintf pp "{\"type\": \"Omakelong\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "{\"type\": \"Olowlong\", \"regs\": [\"%a\"]}" reg r1
  | Ohighlong, [r1] -> fprintf pp "{\"type\": \"Ohighlong\", \"regs\": [\"%a\"]}" reg r1
  | Ocast32signed, [r1] -> fprintf pp "{\"type\": \"Ocast32signed\", \"regs\": [\"%a\"]}" reg r1
  | Ocast32unsigned, [r1] -> fprintf pp "{\"type\": \"Ocast32unsigned\", \"regs\": [\"%a\"]}" reg r1
  | Oaddl, [r1;r2] -> fprintf pp "{\"type\": \"Oaddl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oaddlimm n, [r1] -> fprintf pp "{\"type\": \"Oaddlimm\", \"args\": [\"%Ld\"], \"regs\": [\"%a\"]}" (camlint64_of_coqint n) reg r1
  | Onegl, [r1] -> fprintf pp "{\"type\": \"Onegl\", \"regs\": [\"%a\"]}" reg r1
  | Osubl, [r1;r2] -> fprintf pp "{\"type\": \"Osubl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omull, [r1;r2] -> fprintf pp "{\"type\": \"Omull\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omullhs, [r1;r2] -> fprintf pp "{\"type\": \"Omullhs\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omullhu, [r1;r2] -> fprintf pp "{\"type\": \"Omullhu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Odivl, [r1;r2] -> fprintf pp "{\"type\": \"Odivl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Odivlu, [r1;r2] -> fprintf pp "{\"type\": \"Odivlu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omodl, [r1;r2] -> fprintf pp "{\"type\": \"Omodl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omodlu, [r1;r2] -> fprintf pp "{\"type\": \"Omodlu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oandl, [r1;r2] -> fprintf pp "{\"type\": \"Oandl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oandlimm n, [r1] -> fprintf pp "{\"type\": \"Oandlimm\", \"args\": [\"%Ld\"], \"regs\": [\"%a\"]}" (camlint64_of_coqint n) reg r1
  | Oorl, [r1;r2] -> fprintf pp "{\"type\": \"Oorl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oorlimm n, [r1] ->  fprintf pp "{\"type\": \"Oorlimm\", \"args\": [\"%Ld\"], \"regs\": [\"%a\"]}" (camlint64_of_coqint n) reg r1
  | Oxorl, [r1;r2] -> fprintf pp "{\"type\": \"Oxorl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oxorlimm n, [r1] -> fprintf pp "{\"type\": \"Oxorlimm\", \"args\": [\"%Ld\"], \"regs\": [\"%a\"]}" (camlint64_of_coqint n) reg r1
  | Oshll, [r1;r2] -> fprintf pp "{\"type\": \"Oshll\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oshllimm n, [r1] -> fprintf pp "{\"type\": \"Oshllimm\", \"args\": [\"%Ld\"], \"regs\": [\"%a\"]}" (camlint64_of_coqint n) reg r1
  | Oshrl, [r1;r2] -> fprintf pp "{\"type\": \"Oshrl\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oshrlimm n, [r1] -> fprintf pp "{\"type\": \"Oshrlimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oshrlu, [r1;r2] -> fprintf pp "{\"type\": \"Oshrlu\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Oshrluimm n, [r1] -> fprintf pp "{\"type\": \"Oshrluimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1
  | Oshrxlimm n, [r1] -> fprintf pp "{\"type\": \"Oshrxlimm\", \"args\": [\"%ld\"], \"regs\": [\"%a\"]}" (camlint_of_coqint n) reg r1

  | Onegf, [r1] -> fprintf pp "{\"type\": \"Onegf\", \"regs\": [\"%a\"]}" reg r1
  | Oabsf, [r1] -> fprintf pp "{\"type\": \"Oabsf\", \"regs\": [\"%a\"]}" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "{\"type\": \"Oaddf\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "{\"type\": \"Osubf\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "{\"type\": \"Omulf\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "{\"type\": \"Odivf\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Onegfs, [r1] -> fprintf pp "{\"type\": \"Onegfs\", \"regs\": [\"%a\"]}" reg r1
  | Oabsfs, [r1] -> fprintf pp "{\"type\": \"Oabsfs\", \"regs\": [\"%a\"]}" reg r1
  | Oaddfs, [r1;r2] -> fprintf pp "{\"type\": \"Oaddfs\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Osubfs, [r1;r2] -> fprintf pp "{\"type\": \"Osubfs\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Omulfs, [r1;r2] -> fprintf pp "{\"type\": \"Omulfs\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Odivfs, [r1;r2] -> fprintf pp "{\"type\": \"Odivfs\", \"regs\": [\"%a\", \"%a\"]}" reg r1 reg r2
  | Osingleoffloat, [r1] -> fprintf pp "{\"type\": \"Osingleoffloat\", \"regs\": [\"%a\"]}" reg r1
  | Ofloatofsingle, [r1] -> fprintf pp "{\"type\": \"Ofloatofsingle\", \"regs\": [\"%a\"]}" reg r1
  | Ointoffloat, [r1] -> fprintf pp "{\"type\": \"Ointoffloat\", \"regs\": [\"%a\"]}" reg r1
  | Ointuoffloat, [r1] -> fprintf pp "{\"type\": \"Ointuoffloat\", \"regs\": [\"%a\"]}" reg r1
  | Ofloatofint, [r1] -> fprintf pp "{\"type\": \"Ofloatofint\", \"regs\": [\"%a\"]}" reg r1
  | Ofloatofintu, [r1] -> fprintf pp "{\"type\": \"Ofloatofintu\", \"regs\": [\"%a\"]}" reg r1
  | Olongoffloat, [r1] -> fprintf pp "{\"type\": \"Olongoffloat\", \"regs\": [\"%a\"]}" reg r1
  | Olonguoffloat, [r1] -> fprintf pp "{\"type\": \"Olonguoffloat\", \"regs\": [\"%a\"]}" reg r1
  | Ofloatoflong, [r1] -> fprintf pp "{\"type\": \"Ofloatoflong\", \"regs\": [\"%a\"]}" reg r1
  | Ofloatoflongu, [r1] -> fprintf pp "{\"type\": \"Ofloatoflongu\", \"regs\": [\"%a\"]}" reg r1
  | Ointofsingle, [r1] -> fprintf pp "{\"type\": \"Ointofsingle\", \"regs\": [\"%a\"]}" reg r1
  | Ointuofsingle, [r1] -> fprintf pp "{\"type\": \"Ointuofsingle\", \"regs\": [\"%a\"]}" reg r1
  | Osingleofint, [r1] -> fprintf pp "{\"type\": \"Osingleofint\", \"regs\": [\"%a\"]}" reg r1
  | Osingleofintu, [r1] -> fprintf pp "{\"type\": \"Osingleofintu\", \"regs\": [\"%a\"]}" reg r1
  | Olongofsingle, [r1] -> fprintf pp "{\"type\": \"Olongofsingle\", \"regs\": [\"%a\"]}" reg r1
  | Olonguofsingle, [r1] -> fprintf pp "{\"type\": \"Olonguofsingle\", \"regs\": [\"%a\"]}" reg r1
  | Osingleoflong, [r1] -> fprintf pp "{\"type\": \"Osingleoflong\", \"regs\": [\"%a\"]}" reg r1
  | Osingleoflongu, [r1] -> fprintf pp "{\"type\": \"Osingleoflongu\", \"regs\": [\"%a\"]}" reg r1
  | Ocmp c, args -> fprintf pp "{\"type\": \"Ocmp\", \"condition\": %a}" (print_condition reg) (c, args)
  | Osel (c, ty), r1::r2::args -> fprintf pp "{\"type\": \"Osel\", \"condition\": %a, \"true\": \"%a\", \"false\": \"%a\"}" (print_condition reg) (c, args) reg r1 reg r2
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "{\"type\": \"Aindexed\", \"args\": [\"%Ld\"], \"regs\": [\"%a\"]}" (camlint64_of_ptrofs n) reg r1
  | Aglobal(id, ofs), [] ->
      fprintf pp "{\"type\": \"Aglobal\", \"args\": [\"%s\", \"%Ld\"]}" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Ainstack ofs, [] -> fprintf pp "{\"type\": \"Ainstack\", \"args\": [\"%Ld\"]}" (camlint64_of_ptrofs ofs)
  | _ -> fprintf pp "<bad addressing>"

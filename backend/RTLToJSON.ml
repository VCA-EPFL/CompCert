(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printers for RTL code *)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTL
open ASTToJSON

(* Printing of RTL code *)

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> fprintf pp "{\"type\": \"symb\", \"name\": \"%a\"}" reg r
  | Coq_inr s -> fprintf pp "{\"type\": \"symb\", \"name\": \"%s\"}" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int s in
  if s <> dfl then fprintf pp "\tgoto %d\n" s

let print_instruction pp (pc, i) =
  fprintf pp "    %d: " pc;
  match i with
  | Inop s ->
      fprintf pp "{\"type\": \"Inop\", \"next\": %d}" (P.to_int s)
  | Iop(op, args, res, s) ->
      fprintf pp "{\"type\": \"Iop\", \"dest\": %a, \"operation\": %a, \"next\": %d}"
         reg res (OpToJSON.print_operation reg) (op, args) (P.to_int s)
  | Iload(chunk, addr, args, dst, s) ->
      fprintf pp "{\"type\": \"Iload\", \"chunk\": %s, \"dest\": %a, \"operation\": %a, \"next\": %d}"
         (name_of_chunk chunk) reg dst
         (OpToJSON.print_addressing reg) (addr, args) (P.to_int s)
  | Istore(chunk, addr, args, src, s) ->
      fprintf pp "{\"type\": \"Istore\", \"chunk\": %s, \"source\": %a, \"operation\": %a, \"next\": %d}"
         (name_of_chunk chunk) reg src
         (OpToJSON.print_addressing reg) (addr, args) (P.to_int s)
  | Icall(sg, fn, args, res, s) ->
      fprintf pp "{\"type\": \"Icall\", \"dest\": %a, \"function\": %a, \"args\": [%a], \"next\": %d}"
        reg res ros fn regs args (P.to_int s)
  | Itailcall(sg, fn, args) ->
      fprintf pp "{\"type\": \"Itailcall\", \"function\": %a, \"args\": [%a]}"
        ros fn regs args
  | Ibuiltin(ef, args, res, s) ->
      fprintf pp "{\"type\": \"Ibuiltin\", \"dest\": \"%a\", \"function\": \"%s\", \"args\": \"%a\", \"next\": %d}"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args
        (P.to_int s)
  | Icond(cond, args, s1, s2) ->
      fprintf pp "{\"type\": \"Icond\", \"condition\": %a, \"true\": %d, \"false\": %d}"
        (OpToJSON.print_condition reg) (cond, args)
        (P.to_int s1) (P.to_int s2)
  | Ijumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "{\"type\": \"Ijumptable\", \"source\": \"%a\", \"table\": {" reg arg;
      for i = 0 to Array.length tbl - 1 do
        if i == Array.length tbl - 1 then
          fprintf pp "%d: %d" i (P.to_int tbl.(i))
        else
          fprintf pp "%d: %d, " i (P.to_int tbl.(i))
      done;
      fprintf pp "}"
  | Ireturn None ->
      fprintf pp "{\"type\": \"Ireturn\"}"
  | Ireturn (Some arg) ->
      fprintf pp "{\"type\": \"Ireturn\", \"source\": \"%a\"}" reg arg

let print_function pp (id, f) =
  fprintf pp "\"%s\": {\n  \"args\": [%a],\n  \"entrypoint\": %d,\n  \"body\": {\n" (extern_atom id) regs f.fn_params (P.to_int f.fn_entrypoint);
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.fn_code)) in
  let first = ref true in
  List.iter (fun i -> if !first then (first := false; print_instruction pp i) else fprintf pp ",\n%a" print_instruction i) instrs;
  fprintf pp "\n  }"

let print_globdef first pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> if !first then (first := false; print_function pp (id, f)) else fprintf pp ",\n%a" print_function (id, f)
  | _ -> ()

let print_program pp (prog: RTL.program) =
  let first = ref true in
  fprintf pp "{\n";
  List.iter (print_globdef first pp) prog.prog_defs;
  fprintf pp "\n}"

let destination : string option ref = ref None

let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program oc prog;
      close_out oc

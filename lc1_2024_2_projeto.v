(** * Projeto de LC1 - 2024-2 (30 pontos)  *)

(*
Nome e matrícula dos participantes:
1.
2.
3.
*)

(* begin hide *)
Require Import Arith.
Require Import List.
Require Import Lia.
Require Import Permutation.
(* end hide *)

(** ** Introdução  *)
(** Esta é a introdução ... *)

Inductive ord: list nat -> Prop :=
| ord_nil: ord nil
| ord_one: forall h, ord (h::nil)
| ord_all: forall x y l, x <= y -> ord (y::l) -> ord (x::y::l).

(** ** Conclusão  *)
(** Esta é a conclusão ... *)

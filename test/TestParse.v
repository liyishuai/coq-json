From Coq Require Import
         List.
Import ListNotations.

From JSON Require Import
     Lexer Printer.

Definition parse_empty := from_string "{}".

Goal parse_empty = inr (JSON__Object []).
Proof. reflexivity. Qed.

Definition parse_singleton := from_string "{""a"": 1}".

Goal parse_singleton = inr (JSON__Object [("a", JSON__Number 1)]).
Proof. reflexivity. Qed.

Definition parse_nested := from_string "{""a"": {""b"": 2}}".

Goal parse_nested = inr (JSON__Object [("a", JSON__Object [("b", JSON__Number 2)])]).
Proof. reflexivity. Qed.

Definition parse_null_value := from_string "{""a"": null}".

Goal parse_null_value = inr (JSON__Object [("a", JSON__Null)]).
Proof. reflexivity. Qed.

Definition parse_bool_value := from_string "{""a"": true}".

Goal parse_bool_value = inr (JSON__Object [("a", JSON__True)]).
Proof. reflexivity. Qed.

Definition parse_list_value := from_string "{""a"": [1, 2, 3]}".

Goal parse_list_value = inr (JSON__Object [("a", JSON__Array [JSON__Number 1; JSON__Number 2; JSON__Number 3])]).
Proof. reflexivity. Qed.

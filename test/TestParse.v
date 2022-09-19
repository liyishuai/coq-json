
From JSON Require Import
     Lexer Printer.

Definition parse_empty := from_string "{}".

Compute parse_empty.

Definition parse_singleton := from_string "{""a"": 1}".

Compute parse_singleton.

Definition parse_nested := from_string "{""a"": {""b"": 2}}".

Compute parse_nested.

Definition parse_null_value := from_string "{""a"": null}".

Compute parse_null_value.

Definition parse_bool_value := from_string "{""a"": true}".

Compute parse_bool_value.

Definition parse_list_value := from_string "{""a"": [1, 2, 3]}".

Compute parse_list_value.
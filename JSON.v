From Coq Require Export
     String
     ZArith.

Inductive json :=
  JSON__Object : list (string * json) -> json
| JSON__Array  : list json            -> json
| JSON__String : string               -> json
| JSON__Number : Z                    -> json
| JSON__True
| JSON__False
| JSON__Null.
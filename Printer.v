From JSON Require Export
     JSON.
From Coq Require Export
     Ascii
     DecimalString
     DecimalZ
     String.
Open Scope string_scope.

Fixpoint to_string (j : json) : string :=
  match j with
  | JSON__Object l =>
    let member_to_string (nv : string * json) :=
        let (n, v) := nv in
        String DoubleQuote n ++ String DoubleQuote (String ":" (to_string v)) in
    String "{" ((concat "," (map member_to_string l)) ++ "}")
  | JSON__Array l =>
    String "[" ((concat "," (map to_string l)) ++ "]")
  | JSON__String s => String DoubleQuote (s ++ """")
  | JSON__Number z => NilZero.string_of_int (Z.to_int z)
  | JSON__True     => "true"
  | JSON__False    => "false"
  | JSON__Null     => "null"
  end.

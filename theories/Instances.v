From ExtLib Require Export
     Extras.
From Ceres Require Export
     Ceres.
From JSON Require Export
     JSON.
Export
  FunNotation.
Open Scope sexp_scope.

#[global]
Instance Serialize__json : Serialize json :=
  fix to_sexp (j : json) : sexp :=
    match j with
    | JSON__Object l => List $ map (fun sj => let (s, j) := sj : string * json in
                                        [Atom s; to_sexp j]) l
    | JSON__Array  l => List $ map to_sexp l
    | JSON__String s => Atom s
    | JSON__Number z => Atom z
    | JSON__True     => Atom "true"
    | JSON__False    => Atom "false"
    | JSON__Null     => Atom "null"
    end.

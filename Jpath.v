From Ceres Require Export
     Ceres.
From JSON Require Export
     JSON.
Export
  ListNotations.

Inductive jpath :=
  Jpath__This
| Jpath__Array  : jpath -> nat -> jpath
| Jpath__Object : jpath -> string -> jpath.

Fixpoint jget (p : jpath) (j : json) : option json :=
  match p with
  | Jpath__This        => Some j
  | Jpath__Array p' n  => jget p' j >>= get_nth n
  | Jpath__Object p' s => jget p' j >>= get_json' s
  end.

#[global]
Instance Serialize__jpath : Serialize jpath :=
  let fix jpath_to_list (p : jpath) : list sexp :=
      match p with
      | Jpath__This       => []
      | Jpath__Array  p n => jpath_to_list p ++ [to_sexp n]
      | Jpath__Object p s => jpath_to_list p ++ [Atom s]
      end in
  List ∘ jpath_to_list.

Declare Scope json_scope.

Module JpathNotations.

Notation "'this'" := Jpath__This   : json_scope.
Infix "#" := Jpath__Array  (at level 50) : json_scope.
Infix "@" := Jpath__Object (at level 50) : json_scope.

End JpathNotations.

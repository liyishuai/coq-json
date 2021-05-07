From Ceres Require Export
     Ceres.
From JSON Require Export
     JSON.
Export
  ListNotations.

Inductive jpath :=
  Jpath__This
| Jpath__Array  : nat -> jpath -> jpath
| Jpath__Object : string -> jpath -> jpath.

Fixpoint jget (p : jpath) (j : json) : option json :=
  match p with
  | Jpath__This        => Some j
  | Jpath__Array n p'  => get_nth   n j >>= jget p'
  | Jpath__Object s p' => get_json' s j >>= jget p'
  end.

Instance Serialize__jpath : Serialize jpath :=
  let fix jpath_to_list (p : jpath) : list sexp :=
      match p with
      | Jpath__This       => []
      | Jpath__Array  n p => to_sexp n::jpath_to_list p
      | Jpath__Object s p => Atom s   ::jpath_to_list p
      end in
  List ∘ jpath_to_list.

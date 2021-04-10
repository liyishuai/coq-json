From ExtLib Require Export
     List
     Traversable
     Monad
     OptionMonad.
From Coq Require Export
     Basics
     Bool
     String
     List
     ZArith.
Export
  MonadNotation
  IfNotations.
Open Scope lazy_bool_scope.
Open Scope monad_scope.
Open Scope program_scope.

Inductive json :=
  JSON__Object : list (string * json) -> json
| JSON__Array  : list json            -> json
| JSON__String : string               -> json
| JSON__Number : Z                    -> json
| JSON__True
| JSON__False
| JSON__Null.

Definition get_json (k : string) (j : json) : json :=
  if j is JSON__Object l
  then if find (eqb k ∘ fst) l is Some (_, v)
       then v
       else JSON__Null
  else JSON__Null.

Definition get_Z (k : string) (j : json) : option Z :=
  if get_json k j is JSON__Number z then Some z else None.

Definition get_N (k : string) (j : json) : option N :=
  z <- get_Z k j;;
  if z is Zneg _
  then None
  else Some (Z.to_N z).

Definition get_string (k : string) (j : json) : option string :=
  if get_json k j is JSON__String str then Some str else None.

Definition get_bool (k : string) (j : json) : option bool :=
  match get_json k j with
  | JSON__True  => Some true
  | JSON__False => Some false
  | _         => None
  end.

Definition get_list {T} (f : json -> option T) (j : json) : option (list T) :=
  if j is JSON__Array l
  then sequence (map f l)
  else None.

Definition eqb_list {A} (f : A -> A -> bool) : list A -> list A -> bool :=
  fix eqb_list_ (xs ys : list A) : bool :=
    match xs, ys with
    | nil, nil => true
    | x :: xs, y :: ys => f x y &&& eqb_list_ xs ys
    | _, _ => false
    end.

Fixpoint eqb_json (j k : json) : bool :=
  match j, k with
  | JSON__Object lj, JSON__Object lk =>
    eqb_list (fun (jm km : string * json) =>
                let (js, jj) := jm in
                let (ks, kj) := km in
                (js =? ks) &&& eqb_json jj kj) lj lk
  | JSON__Array lj, JSON__Array lk => eqb_list eqb_json lj lk
  | JSON__String s, JSON__String t => s =? t
  | JSON__Number z, JSON__Number y => (z =? y)%Z
  | JSON__True    , JSON__True
  | JSON__False   , JSON__False
  | JSON__Null    , JSON__Null => true
  | _, _ => false
  end%string.

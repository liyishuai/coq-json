From JSON Require Export
     Instances.
Open Scope string_scope.

Definition or_json' (j k : json) : string + json :=
  match j, k with
  | JSON__Object lj, JSON__Object lk => inr $ JSON__Object $ app lj lk
  | JSON__Object _, x
  | x, JSON__Object _ => inl $ "Not an Object: " ++ to_string k
  | _, _ => inl $ "Neither is an Object: " ++ to_string j ++
               " or: " ++ to_string k
  end.

Definition or_json (j k : json) : json :=
  if or_json' j k is inr x then x else j.

Module MemberOrder <: TotalLeBool.
Definition t : Set := string * json.

#[deprecated(since="8.14", note="Use Ascii.compare instead.")]
Definition ascii_compare (a b : ascii) : comparison :=
  N.compare (N_of_ascii a) (N_of_ascii b).

#[deprecated(since="8.14", note="Use Ascii.compare_antisym instead.")]
Lemma ascii_compare_antisym (a b : ascii) :
    ascii_compare a b = CompOpp (ascii_compare b a).
Proof. apply N.compare_antisym. Qed.

#[deprecated(since="8.14", note="Use String.compare instead.")]
Fixpoint string_compare (s1 s2 : string) : comparison :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | EmptyString, String _ _  => Lt
  | String _ _ , EmptyString => Gt
  | String c1 s1', String c2 s2' =>
    match ascii_compare c1 c2 with
    | Eq => string_compare s1' s2'
    | ne => ne
    end
  end.

#[deprecated(since="8.14", note="Use String.compare_antisym instead.")]
Lemma string_compare_antisym : forall s1 s2 : string,
    string_compare s1 s2 = CompOpp (string_compare s2 s1).
Proof.
  induction s1, s2; intuition.
  simpl.
  rewrite ascii_compare_antisym.
  destruct (ascii_compare a0 a); simpl; intuition.
Qed.

#[deprecated(since="8.14", note="Use String.leb instead.")]
Definition string_leb (s1 s2 : string) : bool :=
  if string_compare s1 s2 is Gt then false else true.

#[deprecated(since="8.14", note="Use String.leb_total instead.")]
Lemma string_leb_total (s1 s2 : string) :
  string_leb s1 s2 = true \/ string_leb s2 s1 = true.
Proof.
  unfold string_leb.
  rewrite string_compare_antisym.
  destruct (string_compare s2 s1); intuition.
Qed.

Definition leb (x y : t) : bool :=
  string_leb (fst x) (fst y).

Theorem leb_total (x y : t) : leb x y = true \/ leb y x = true.
Proof.
  unfold leb.
  apply string_leb_total.
Qed.

End MemberOrder.

Module Import MemberSort := Sort MemberOrder.

Fixpoint sort_json (j : json) : json :=
  match j with
  | JSON__Object lj =>
    JSON__Object (sort (map (fun sj => let (s, j') := sj : string * json in
                                  (s, sort_json j')) lj))
  | JSON__Array lj => JSON__Array (map sort_json lj)
  | _ => j
  end.

Definition eqb_list {A} (f : A -> A -> bool) : list A -> list A -> bool :=
  fix eqb_list_ (xs ys : list A) : bool :=
    match xs, ys with
    | nil, nil => true
    | x :: xs, y :: ys => f x y &&& eqb_list_ xs ys
    | _, _ => false
    end.

Fixpoint eqb_json' (j k : json) : bool :=
  match j, k with
  | JSON__Object lj, JSON__Object lk =>
    eqb_list (fun (jm km : string * json) =>
                let (js, jj) := jm in
                let (ks, kj) := km in
                (js =? ks) &&& eqb_json' jj kj) lj lk
  | JSON__Array lj, JSON__Array lk => eqb_list eqb_json' lj lk
  | JSON__String s, JSON__String t => s =? t
  | JSON__Number z, JSON__Number y => (z =? y)%Z
  | JSON__True    , JSON__True
  | JSON__False   , JSON__False
  | JSON__Null    , JSON__Null => true
  | _, _ => false
  end%string.

Definition eqb_json (j k : json) : bool :=
  eqb_json' (sort_json j) (sort_json k).

Module JNotations.

Infix "+"  := or_json  : json_scope.
Infix "=?" := eqb_json : json_scope.

End JNotations.

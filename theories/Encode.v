From ExtLib Require Export
     Extras.
From JSON Require Export
     JSON.
Export
  FunNotation
  ListNotations.

Class JEncode T := encode : T -> json.

#[global]
Instance JEncode__json   : JEncode json := id.
#[global]
Instance JEncode__unit   : JEncode unit := const JSON__Null.
#[global]
Instance JEncode__String : JEncode string := JSON__String.
#[global]
Instance JEncode__Z      : JEncode Z := JSON__Number.
#[global]
Instance JEncode__N      : JEncode N := encode ∘ Z.of_N.
#[global]
Instance JEncode__nat    : JEncode nat := encode ∘ Z.of_nat.
#[global]
Instance JEncode__bool   : JEncode bool :=
  fun b : bool => if b then JSON__True else JSON__False.

#[global]
Instance JEncode__list {T} `{JEncode T} : JEncode (list T) :=
  JSON__Array ∘ map encode.

#[global]
Instance JEncode__option {T} `{JEncode T} : JEncode (option T) :=
  fun x => if x is Some x then encode x else JSON__Object [].

Definition jkv' (k : string) (v : json) : json :=
  JSON__Object [(k, v)].

Definition jkv (k : string) (v : json) : json :=
  if v is JSON__Object [] then JSON__Object [] else jkv' k v.

Definition jobj' {T} (encode : T -> json) (k : string) (v : T) : json :=
  jkv k $ encode v.

Definition jobj {T} `{JEncode T} : string -> JEncode T := jobj' encode.

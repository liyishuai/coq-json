From Coq Require Export
     ssr.ssrfun.
From Parsec Require Export
     Parser.
From ExtLib Require Export
     Extras
     MonadExc
     EitherMonad.
From JSON Require Export
     Jpath
     Printer.
Export
  JpathNotations
  FunNotation.
Open Scope string_scope.
Open Scope parser_scope.
Open Scope json_scope.

Class JDecode T := decode : json -> string + T.

#[global]
Instance JDecode__json : JDecode json := inr.

#[global]
Instance JDecode__string : JDecode string :=
  fun j : json =>
    if j is JSON__String str then inr str
    else inl $ "Not a String: " ++ to_string j.

#[global]
Instance JDecode__Z : JDecode Z :=
  fun j : json =>
    if j is JSON__Number z then inr z
    else inl $ "Not a Number: " ++ to_string j.

#[global]
Instance JDecode__N : JDecode N :=
  fmap Z.to_N ∘ decode.

#[global]
Instance JDecode__nat : JDecode nat :=
  fmap Z.to_nat ∘ decode.

#[global]
Instance JDecode__bool : JDecode bool :=
  fun j : json =>
    match j with
    | JSON__True  => inr true
    | JSON__False => inr false
    | _         => inl $ "Not a Boolean: " ++ to_string j
    end.

Definition decode__list {T} `{JDecode T} : JDecode (list T) :=
  fun j : json =>
    if j is JSON__Array l then sequence $ map decode l
    else inl $ "Not an Array: " ++ to_string j.

Definition decode__option {T} `{JDecode T} : JDecode (option T) :=
  fun j : json =>
    catch (Some <$> decode j) (const $ inr None).

#[global]
Instance JDecode__unit : JDecode unit :=
  fun j : json =>
    if j is JSON__Null then inr tt
    else inl $ "Not a Null: " ++ to_string j.

Definition decode__jpath (p : jpath) : JDecode json :=
  fun j : json =>
    if jget p j is Some j' then inr j'
    else inl $ CeresSerialize.to_string p ++ " not found in: " ++ to_string j.

Definition dparse {T} (pr : parser T) (s : string) : string + T :=
  match parse pr s with
  | inl os     => inl (odflt "Parser out of fuel" os)
  | inr (t, _) => inr t
  end.

Definition dpath' {T} (d : JDecode T) (s : string) (j : json) : string + T :=
  (decode__jpath (this@s) j <|> inr JSON__Null) >>= d.

Definition dpath {T} `{JDecode T} : string -> JDecode T := dpath' decode.

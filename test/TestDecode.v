From JSON Require Import
     Decode.

Definition decode__okey : JDecode (option string) := dpath' decode__option "key".

Compute decode__okey (JSON__Object []).

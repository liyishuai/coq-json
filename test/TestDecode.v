From JSON Require Import
     Decode.

Definition decode__okey : JDecode (option string) := dpath' decode__option "key".

Goal decode__okey (JSON__Object []) = inr None.
Proof. reflexivity. Qed.

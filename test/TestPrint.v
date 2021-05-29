From JSON Require Import
     Printer.
Import
  ListNotations.
Open Scope list_scope.

Example j1 : json :=
  JSON__Object
         [("version", JSON__Object [("major", JSON__Number 1); ("minor", JSON__Number 1)]); ("code", JSON__Number 200);
         ("reason", JSON__String "OK");
         ("fields", JSON__Object [("ETag", JSON__String "tag-foo"); ("Content-Length", JSON__String "11")]);
         ("body", JSON__String "content-bar")].

Compute to_string j1.

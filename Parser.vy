%{From JSON Require Export JSON.
From Coq Require Extraction.
From Coq Require Export
     List.
Export
  ListNotations.
Open Scope list_scope.
%}

%token TRUE FALSE NULL AS AE OS OE COLON COMMA EOF
%token<Z>      NUMBER
%token<string> NAME

%start<json> parse_json

%type<json>      p_element
%type<list json> p_elements p_array
%type<string * json>        p_member
%type<list (string * json)> p_members p_object
%%

parse_json : p_element EOF { $1 }

p_element :
  OS p_object OE  { JSON__Object $2 }
| AS p_array  AE  { JSON__Array  $2 }
| NAME            { JSON__String $1 }
| NUMBER          { JSON__Number $1 }
| TRUE            { JSON__True  }
| FALSE           { JSON__False }
| NULL            { JSON__Null  }

p_array :
             { [] }
| p_elements { $1 }

p_elements :
  p_element { [$1] }
| p_element COMMA p_elements { $1 :: $3 }

p_object :
            { [] }
| p_members { $1 }

p_members :
  p_member { [$1] }
| p_member COMMA p_members { $1 :: $3 }

p_member :
  NAME COLON p_element { ($1, $3) }

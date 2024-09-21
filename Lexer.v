From JSON Require Import
     Parser.
From Parsec Require Import
     Core.
Import
  IfNotations
  MenhirLibParser.Inter.

Open Scope char_scope.

Definition lex__NUMBER : parser token :=
  let lex__POS : parser Z := Z_of_N <$> parseDec in
  NUMBER <$> lex__POS <|>
  firstExpect "-" (NUMBER ∘ Z.opp <$> lex__POS).

Definition lex__NAME : parser token :=
  let ischar (a : ascii) : bool :=
      (Space <=? a) &&& negb ((a =? DoubleQuote) ||| (a =? "\")) in
  firstExpect DoubleQuote $
    name <- string_of_list_ascii <$> many
       (chooseFrom
          [satisfy ischar;
           firstExpect "\" $ chooseFrom
                       [expect "\";
                        expect "/";
                        expect DoubleQuote;
                        firstExpect "n" $ ret Char.chr_newline;
                        firstExpect "b" $ ret "008";
                        firstExpect "t" $ ret "009";
                        firstExpect "f" $ ret "012";
                        firstExpect "r" $ ret "013"]]);;
  firstExpect DoubleQuote (ret (NAME name)).

Close Scope char_scope.

Fixpoint expectString (s : string) : parser string :=
  match s with
  | "" => ret ""
  | String a s' => liftA2 String (expect a) (expectString s')
  end.

Definition lex__token : parser token :=
  many (chooseFrom [parseHTAB; parseLF; parseCR; parseSP]);;
  chooseFrom
    [expectString "true" ;; ret (TRUE  tt);
     expectString "false";; ret (FALSE tt);
     expectString "null" ;; ret (NULL  tt);
     expectString ","    ;; ret (COMMA tt);
     expectString ":"    ;; ret (COLON tt);
     expectString "{"    ;; ret (OS    tt);
     expectString "}"    ;; ret (OE    tt);
     expectString "["    ;; ret (AS    tt);
     expectString "]"    ;; ret (AE    tt);
     lex__NUMBER; lex__NAME].

CoFixpoint TheEnd : buffer := Buf_cons (EOF tt) TheEnd.

Open Scope buffer_scope.
CoFixpoint push_back (b: buffer) (l: list token) : buffer :=
  match b with
  | EOF _ :: _    => l ++ TheEnd
  | head  :: tail => head :: push_back tail l
  end.

Definition lexer' (acc: buffer * list ascii) (str: string)
  : string + buffer * list ascii :=
  let (buf, lchar) := acc in
  match parse' (many lex__token) lchar str with
  | inl (Some err)     => inl err
  | inl None           => inr acc
  | inr (l, remainder) => inr (push_back buf l, remainder)
  end.

Definition from_string' (acc: buffer * list ascii) (str: string)
  : string + option json * buffer * list ascii :=
  match lexer' acc str with
  | inl e => inl e
  | inr (b, remainder) =>
      match parse_json bigNumber b with
      | Parsed_pr    j b'      => inr (Some j, b', remainder)
      | Fail_pr_full _ (EOF _) => inr (None  , b , remainder)
      | _ => inl "Passed lexer but failed JSON parser"
      end
  end.

Definition from_string (str: string) : option string + json :=
  match from_string' (TheEnd, []) str with
  | inl e              => inl (Some e)
  | inr (None  , _, _) => inl None
  | inr (Some j, _, _) => inr j
  end.

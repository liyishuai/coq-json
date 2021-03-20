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
  NAME ∘ string_of_list_ascii <$> many1
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
                        firstExpect "r" $ ret "013"]]).

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

Definition lexer (str : string) : option string + buffer :=
  match Parser.parse (many lex__token) str with
  | inl err => inl err
  | inr (l, _) => inr (app_buf l TheEnd)
  end.

Definition from_string (str : string) : parse_result json :=
  match lexer str with
  | inl _ => Fail_pr
  | inr b => parse_json bigNumber b
  end.

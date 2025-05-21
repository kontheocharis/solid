module Surface.Parsing

import Data.List

import Surface.Presyntax
import Utils
import Common

import Control.Monad.Trans
import Data.List
import Data.String
import Data.DPair
import Data.Fin
import Debug.Trace

%default covering

-- Setup:

public export
data ParseErrorKind : Type where
  TrailingChars : ParseErrorKind
  Empty : ParseErrorKind
  EndOfInput : ParseErrorKind
  UnexpectedChar : Char -> ParseErrorKind
  ReservedWord : String -> ParseErrorKind
  InvalidLiteral : String -> ParseErrorKind
  CannotUseLetFlags : LetFlags -> ParseErrorKind

public export
record ParserState where
  constructor MkParserState
  seen : SnocList Char
  toSee : List Char

emptyState : ParserState
emptyState = MkParserState [<] []

stateLoc : ParserState -> Loc
stateLoc (MkParserState seen toSee) = MkLoc (toList seen ++ toSee) (length seen)

public export
record ParseError where
  constructor MkParseError
  kind : ParseErrorKind
  state : ParserState

public export
Show ParseErrorKind where
  show TrailingChars = "Trailing characters"
  show Empty = "Empty input"
  show EndOfInput = "Unexpected end of input"
  show (UnexpectedChar c) = "Unexpected character: " ++ show c
  show (InvalidLiteral s) = "Invalid literal: " ++ s
  show (ReservedWord s) = "Reserved word: " ++ s
  show (CannotUseLetFlags f) = "Cannot use let flags here"

public export
Show ParseError where
  show (MkParseError k ts) = show k ++ " at " ++ show (stateLoc ts)

public export
record Parser (a : Type) where
  constructor MkParser
  runParser : ParserState -> Either ParseError (a, ParserState)

Functor Parser where
  map f p = MkParser $ \ts => case runParser p ts of
    Left s => Left s
    Right (a, ts') => Right (f a, ts')

Applicative Parser where
  pure a = MkParser $ \ts => Right (a, ts)
  (<*>) f x = MkParser $ \ts => case runParser f ts of
    Left s => Left s
    Right (f', ts') => case runParser x ts' of
      Left s => Left s
      Right (x', ts'') => Right (f' x', ts'')

Monad Parser where
  (>>=) f p = MkParser $ \ts => case runParser f ts of
    Left s => Left s
    Right (a, ts') => runParser (p a) ts'

Alternative Parser where
  empty = MkParser $ \ts => Left $ MkParseError Empty ts
  (<|>) p q = MkParser $ \ts => case runParser p ts of
    Left _ => runParser q ts
    Right (a, ts') => Right (a, ts')

fail : ParseErrorKind -> Parser a
fail s = MkParser $ \ts => Left $ MkParseError s ts

optional : Parser a -> Parser (Maybe a)
optional p = MkParser $ \ts => case runParser p ts of
  Left _ => Right (Nothing, ts)
  Right (a, ts') => Right (Just a, ts')

indexNext : ParserState -> Maybe (Char, Lazy ParserState)
indexNext (MkParserState seen (s :: toSee)) = Just (s, MkParserState (seen :< s) toSee)
indexNext (MkParserState seen []) = Nothing

peek : Parser (Maybe Char)
peek = MkParser $ \ts => case indexNext ts of
  Nothing => Right (Nothing, ts)
  Just (c, _) => Right (Just c, ts)

satisfy : (Char -> Bool) -> Parser Char
satisfy p = MkParser $ \ts => case indexNext ts of
  Nothing => Left $ MkParseError EndOfInput ts
  Just (c, p') => if p c
    then Right (c, p')
    else Left $ MkParseError (UnexpectedChar c) ts

char : Char -> Parser ()
char c = satisfy (== c) *> pure ()

many : Parser a -> Parser (List a)
many p = MkParser $ \ts => case runParser p ts of
  Left _ => Right ([], ts)
  Right (a, ts') => case runParser (many p) ts' of
      Left _ => Right ([a], ts')
      Right (as, ts'') => Right (a :: as, ts'')

many1 : Parser a -> Parser (DPair (List a) NonEmpty)
many1 p = do
  a <- p
  as <- many p
  pure ((a :: as) ** IsNonEmpty)

between : Parser a -> Parser b -> Parser c -> Parser c
between l r p = do
  _ <- l
  a <- p
  _ <- r
  pure a

sepBy : Parser a -> Parser b -> Parser (List b)
sepBy sep p = do
  a <- p
  as <- many $ do
    _ <- sep
    p
  pure (a :: as)

sepByOptEnd : Parser a -> Parser b -> Parser (List b)
sepByOptEnd sep p = do
  xs <- sepBy sep p
  _ <- optional $ sep
  pure xs

sepByReqEnd : Parser a -> Parser b -> Parser (List b)
sepByReqEnd sep p = do
  xs <- sepBy sep p
  _ <- sep
  pure xs

string : String -> Parser ()
string s = traverse_ char (unpack s)

-- @@TODO: Deal with \r

public export
indentation : Parser ()
indentation = (char ' ' <|> char '\t')

public export
space : Parser ()
space = indentation <|> (char '\n' <* many1 indentation)

public export
anySpace : Parser ()
anySpace = do
  _ <- satisfy isSpace
  pure ()

whitespace : Parser () -> Parser ()
whitespace sp = do
  _ <- many sp
  (( do
      p <- string "--"
      _ <- many (satisfy (\c => c /= '\n' && c /= '\r'))
      whitespace sp
    ) <|> (pure ()))
  pure ()

atom : Parser a -> Parser a
atom p = p <* whitespace space

symbol : String -> Parser ()
symbol s = atom $ string s

betweenGrouping : Parser a -> Parser b -> Parser c -> Parser c
betweenGrouping l r p = between (l <* whitespace anySpace) (whitespace anySpace >> r) p

parens : Parser a -> Parser a
parens p = betweenGrouping (symbol "(") (symbol ")") p

curlies : Parser a -> Parser a
curlies p = betweenGrouping (symbol "{") (symbol "}") p

brackets : Parser a -> Parser a
brackets p = betweenGrouping (symbol "[") (symbol "]") p

located : (Loc -> a -> b) -> Parser a -> Parser b
located f p = MkParser $ \ts => case runParser p ts of
  Left s => Left s
  Right (a, ts') => Right (f (stateLoc ts) a, ts')

public export
parse : Parser a -> String -> Either ParseError a
parse p s = case runParser (whitespace anySpace >> p <* whitespace anySpace) (MkParserState [<] (unpack s)) of
    Left s => Left s
    Right (a, MkParserState _ []) => Right a
    Right (a, ts@(MkParserState _ (_ :: _))) => Left $ MkParseError TrailingChars ts

-- Actual language:

reserved : List String
reserved = []

identifier : Parser String
identifier = atom $ do
  c <- satisfy isAlpha
  cs <- many $ satisfy (\c => isAlphaNum c || c == '-' || c == '_')
  let n = pack (c :: cs)
  if n `elem` reserved
    then fail $ ReservedWord n
    else pure n

public export
tm : Parser PTm

singleTm : Parser PTm

app : Parser PTm

paramLike : (PiMode -> a -> b) -> (Char -> Parser b) -> Parser a -> Parser b
paramLike f orElse p = peek >>= \case
  Nothing => fail Empty
  Just '(' => (parens (f Explicit <$> p)) <|> orElse '(' -- might be a parenthesised expression
  Just '[' => (brackets (f Implicit <$> p))
  Just c' => orElse c'

piParam : Parser (PParam Functions)
piParam = atom . located (|>) $
  (paramLike (|>) (\_ => do
    t <- app
    pure $ \l => MkPParam l (Explicit, "_") (Just t)
  ) $ do
    n <- identifier
    ty <- (symbol ":" >> do
        t <- tm
        pure $ Just t) <|> pure Nothing
    pure $ \m, l => MkPParam l (m, n) ty)

lamParam : Parser (PParam Functions)
lamParam = atom . located (|>) $
  (paramLike (|>) (\_ => do
    n <- identifier
    pure $ \l => MkPParam l (Explicit, n) Nothing
  ) $ do
    n <- identifier
    ty <- (symbol ":" >> do
        t <- tm
        pure $ Just t) <|> pure Nothing
    pure $ \m, l => MkPParam l (m, n) ty)

pairParam : Parser (PParam Pairs)
pairParam = atom . located (|>) $ do
  (m, n) <- paramLike (,) (\_ => (Explicit,) <$> identifier) $ identifier
  ty <- (symbol ":" >> do
      t <- tm
      pure $ Just t) <|> pure Nothing
  pure $ \l => MkPParam l (m, n) ty

piArg : Parser (PArg Functions)
piArg = atom . located (|>) $
  (paramLike (|>) (\_ => do
    t <- singleTm
    pure $ \l => MkPArg l Nothing t
  ) $ do
    n <- identifier
    symbol "="
    t <- tm
    pure $ \m, l => MkPArg l (Just $ (m, n)) t)

pairArg : Parser (PArg Pairs)
pairArg = atom . located (|>) $ do
  n <- optional $ (paramLike (,) (\_ => (Explicit,) <$> identifier) identifier) <* symbol "="
  t <- tm
  pure $ \l => MkPArg l n t

piTel : Parser (PTel Functions)
piTel = MkPTel . fst <$> many1 piParam

lamTel : Parser (PTel Functions)
lamTel = MkPTel . fst <$> many1 lamParam

pairTel : Parser (PTel Pairs)
pairTel = MkPTel <$> parens (sepByOptEnd (symbol ",") pairParam)

piSpine : Parser (PSpine Functions)
piSpine = MkPSpine <$> many piArg

pairSpine : Parser (PSpine Pairs)
pairSpine = MkPSpine <$> parens (sepByOptEnd (symbol ",") pairArg)


-- letFlags : Parser LetFlags
-- letFlags = many

stage : Parser Stage
stage = (symbol "obj" >> pure Obj) <|> (symbol "mta" >> pure Mta)

irr : Parser Bool
irr = (symbol "irr" >> pure True) <|> pure False

decl : Parser (String, Maybe PTy)
decl = do
  n <- identifier
  ty <- optional (symbol ":" >> tm)
  pure (n, ty)

endStatement : Parser ()
endStatement = (symbol ";" <|> symbol "\n") <* whitespace anySpace

blockStatement : Parser PBlockStatement
blockStatement = atom . located (|>) $ do
  s <- optional stage
  irr <- irr
  let flags = MkLetFlags s irr
  (decl >>= \case
    (n, Just ty) => -- can be a bind or let with type, or a let rec
      -- let with type
      (symbol "=" >> do
        v <- tm
        pure $ \l => PLet l flags n (Just ty) v)
      -- bind with type
      <|> (symbol "<-" >> do
        when (not $ letFlagsAreDefault flags) (fail $ CannotUseLetFlags flags)
        v <- tm
        pure $ \l => PBind l n (Just ty) v)
      -- let rec
      <|> (endStatement >> symbol n >> do
        tel <- optional lamTel
        symbol "="
        v <- tm
        let v' = case tel of
              Nothing => v
              Just tel => PLam tel v
        pure $ \l => PLetRec l flags n ty v')
    (n, Nothing) => -- can only be a bind or let without type
      -- let without type
      (symbol ":=" >> do
        v <- tm
        pure $ \l => PLet l flags n Nothing v)
      -- bind without type
      <|> (symbol "<-" >> do
        when (not $ letFlagsAreDefault flags) (fail $ CannotUseLetFlags flags)
        v <- tm
        pure $ \l => PBind l n Nothing v)
    ) <|> (do
      -- just a term statement
      t <- tm
      pure $ \l => PBlockTm l t)


block : Parser PTm
block = located PLoc . curlies $ do
  statements <- sepBy endStatement blockStatement
  pure $ PBlock False statements

name : Parser PTm
name = located PLoc $ PName <$> identifier

lam : Parser PTm
lam = located PLoc $ do
  symbol "\\"
  tel <- lamTel
  symbol "=>"
  body <- tm
  pure $ PLam tel body

app = located PLoc $ do
  f <- singleTm
  sp <- piSpine
  pure $ PApp f sp

pi : Parser PTm
pi = located PLoc $ do
  tel <- piTel
  symbol "->"
  ty <- tm
  pure $ PPi tel ty

unit : Parser PTm
unit = located PLoc $ symbol "()" >> pure PUnit

sigma : Parser PTm
sigma = located PLoc $ do
  t <- pairTel
  pure $ PSigmas t

pairs : Parser PTm
pairs = located PLoc $ do
  sp <- pairSpine
  pure $ PPairs sp

hole : Parser PTm
hole = located PLoc $
  (string "?" >> PHole . Just <$> identifier) <|> (symbol "?" >> pure (PHole Nothing))

literal : Parser PTm
literal = located PLoc $ do
  (string "\'" >> do
      c <- parseChar
      _ <- symbol "\'"
      pure $ PLit (Chr c)
    )
    <|> (string "\"" >> do
            s <- many parseStringChar
            _ <- symbol "\""
            pure $ PLit (Str (pack s))
        )
    <|> ( do
          n <- pack . fst <$> many1 (satisfy isDigit)
          case parsePositive n of
            Nothing => fail $ InvalidLiteral n
            Just np => pure $ PLit (Num np)
      )
  where
    parseStringChar =
      ((string "\\\\") >> pure '\\')
        <|> (string "\\\"" >> pure '\"')
        <|> (satisfy (/= '"') >>= \x => pure x)

    parseChar =
      (string "\\\\" >> pure '\\')
        <|> (string "\\'" >> pure '\'')
        <|> (satisfy (/= '\'') >>= \x => pure x)

singleTm = do
  hd <- atom $ choice [block, parens tm, name, literal, unit, sigma, pairs, hole]
  n <- optional (string ".")
  case n of
    Nothing => pure hd
    Just _ => identifier >>= \n => pure $ PProj hd n

tm = atom $ choice [lam, pi, app]

public export
topLevelBlock : Parser PTm
topLevelBlock = located PLoc $ do
  statements <- sepBy endStatement blockStatement
  pure $ PBlock True statements

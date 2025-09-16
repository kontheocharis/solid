-- Parsing for the surface language
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

-- Setup the basics for parsing

-- @@Todo: currently this parser does wayy too much backtracking, which probably
-- makes it ridiculously slow for certain inputs. This should be fixed.

public export
data ParseErrorKind : Type where
  TrailingChars : ParseErrorKind
  Empty : ParseErrorKind
  EndOfInput : ParseErrorKind
  UnexpectedChar : Char -> ParseErrorKind
  ReservedWord : String -> ParseErrorKind
  InvalidLiteral : String -> ParseErrorKind

public export
record ParseState where
  constructor MkParseState
  seen : SnocList Char
  toSee : List Char

emptyState : ParseState
emptyState = MkParseState [<] []

stateLoc : ParseState -> Loc
stateLoc (MkParseState seen toSee) = MkLoc (toList seen ++ toSee) (length seen)

public export
record ParseError where
  constructor MkParseError
  kind : ParseErrorKind
  state : ParseState

public export
Show ParseErrorKind where
  show TrailingChars = "Trailing characters"
  show Empty = "Empty input"
  show EndOfInput = "Unexpected end of input"
  show (UnexpectedChar c) = "Unexpected character: " ++ show c
  show (InvalidLiteral s) = "Invalid literal: " ++ s
  show (ReservedWord s) = "Reserved word: " ++ s

public export
Show ParseError where
  show (MkParseError k ts) = show k ++ " at " ++ show (stateLoc ts)

public export
record Parse (a : Type) where
  constructor MkParse
  runParse : ParseState -> Either ParseError (a, ParseState)

Functor Parse where
  map f p = MkParse $ \ts => case runParse p ts of
    Left s => Left s
    Right (a, ts') => Right (f a, ts')

Applicative Parse where
  pure a = MkParse $ \ts => Right (a, ts)
  (<*>) f x = MkParse $ \ts => case runParse f ts of
    Left s => Left s
    Right (f', ts') => case runParse x ts' of
      Left s => Left s
      Right (x', ts'') => Right (f' x', ts'')

Monad Parse where
  (>>=) f p = MkParse $ \ts => case runParse f ts of
    Left s => Left s
    Right (a, ts') => runParse (p a) ts'

Alternative Parse where
  empty = MkParse $ \ts => Left $ MkParseError Empty ts
  (<|>) p q = MkParse $ \ts => case runParse p ts of
    Left _ => runParse q ts
    Right (a, ts') => Right (a, ts')

fail : ParseErrorKind -> Parse a
fail s = MkParse $ \ts => Left $ MkParseError s ts

optional : Parse a -> Parse (Maybe a)
optional p = MkParse $ \ts => case runParse p ts of
  Left _ => Right (Nothing, ts)
  Right (a, ts') => Right (Just a, ts')

indexNext : ParseState -> Maybe (Char, Lazy ParseState)
indexNext (MkParseState seen (s :: toSee)) = Just (s, MkParseState (seen :< s) toSee)
indexNext (MkParseState seen []) = Nothing

peek : Parse (Maybe Char)
peek = MkParse $ \ts => case indexNext ts of
  Nothing => Right (Nothing, ts)
  Just (c, _) => Right (Just c, ts)

satisfy : (Char -> Bool) -> Parse Char
satisfy p = MkParse $ \ts => case indexNext ts of
  Nothing => Left $ MkParseError EndOfInput ts
  Just (c, p') => if p c
    then Right (c, p')
    else Left $ MkParseError (UnexpectedChar c) ts

char : Char -> Parse ()
char c = satisfy (== c) *> pure ()

many : Parse a -> Parse (List a)
many p = MkParse $ \ts => case runParse p ts of
  Left _ => Right ([], ts)
  Right (a, ts') => case runParse (many p) ts' of
      Left _ => Right ([a], ts')
      Right (as, ts'') => Right (a :: as, ts'')

many1 : Parse a -> Parse (l : List a ** NonEmpty l)
many1 p = do
  a <- p
  as <- many p
  pure ((a :: as) ** IsNonEmpty)

between : Parse a -> Parse b -> Parse c -> Parse c
between l r p = do
  _ <- l
  a <- p
  _ <- r
  pure a

sepBy : Parse a -> Parse b -> Parse (List b)
sepBy sep p = do
  a <- p
  as <- many $ do
    _ <- sep
    p
  pure (a :: as)

sepByOptEnd : Parse a -> Parse b -> Parse (List b)
sepByOptEnd sep p = do
  xs <- sepBy sep p
  _ <- optional $ sep
  pure xs

sepByReqEnd : Parse a -> Parse b -> Parse (List b)
sepByReqEnd sep p = do
  xs <- sepBy sep p
  _ <- sep
  pure xs

string : String -> Parse ()
string s = traverse_ char (unpack s)

-- @@TODO: Deal with \r

public export
indentation : Parse ()
indentation = (char ' ' <|> char '\t')

public export
space : Parse ()
space = indentation <|> (char '\n' <* many1 indentation)

public export
anySpace : Parse ()
anySpace = do
  _ <- satisfy isSpace
  pure ()

whitespace : Parse () -> Parse ()
whitespace sp = do
  _ <- many sp
  (( do
      p <- string "--"
      _ <- many (satisfy (\c => c /= '\n' && c /= '\r'))
      whitespace sp
    ) <|> (pure ()))
  pure ()

atom : Parse a -> Parse a
atom p = p <* whitespace space

symbol : String -> Parse ()
symbol s = atom $ string s

betweenGrouping : Parse a -> Parse b -> Parse c -> Parse c
betweenGrouping l r p = between (l <* whitespace anySpace) (whitespace anySpace >> r) p

parens : Parse a -> Parse a
parens p = betweenGrouping (symbol "(") (symbol ")") p

curlies : Parse a -> Parse a
curlies p = betweenGrouping (symbol "{") (symbol "}") p

brackets : Parse a -> Parse a
brackets p = betweenGrouping (symbol "[") (symbol "]") p

located : (Loc -> a -> b) -> Parse a -> Parse b
located f p = MkParse $ \ts => case runParse p ts of
  Left s => Left s
  Right (a, ts') => Right (f (stateLoc ts) a, ts')

public export
parse : Parse a -> String -> Either ParseError a
parse p s = case runParse (whitespace anySpace >> p <* whitespace anySpace) (MkParseState [<] (unpack s)) of
    Left s => Left s
    Right (a, MkParseState _ []) => Right a
    Right (a, ts@(MkParseState _ (_ :: _))) => Left $ MkParseError TrailingChars ts

-- Actual language:

reserved : List String
reserved = []

identifier : Parse String
identifier = atom $ do
  c <- satisfy isAlpha
  cs <- many $ satisfy (\c => isAlphaNum c || c == '-' || c == '_' || c == '?')
  let n = pack (c :: cs)
  if n `elem` reserved
    then fail $ ReservedWord n
    else pure n

public export
tm : Parse PTm

singleTm : Parse PTm

app : Parse PTm

paramLike : (PiMode -> a -> b) -> (Char -> Parse b) -> Parse a -> Parse b
paramLike f orElse p = peek >>= \case
  Nothing => fail Empty
  Just '(' => (parens (f Explicit <$> p)) <|> orElse '(' -- might be a parenthesised expression
  Just '[' => (brackets (f Implicit <$> p))
  Just c' => orElse c'

piParam : Parse (PParam Functions)
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

lamParam : Parse (PParam Functions)
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

pairParam : Parse (PParam Pairs)
pairParam = atom . located (|>) $ do
  (m, n) <- paramLike (,) (\_ => (Explicit,) <$> identifier) $ identifier
  ty <- (symbol ":" >> do
      t <- tm
      pure $ Just t) <|> pure Nothing
  pure $ \l => MkPParam l (m, n) ty

piArg : Parse (PArg Functions)
piArg = atom . located (|>) $
  (paramLike (|>) (\_ => do
    t <- singleTm
    pure $ \l => MkPArg l Nothing t
  ) $ do
    n <- optional (identifier <* symbol "=")
    t <- tm
    pure $ \m, l => MkPArg l (Just (m, fromMaybe "_" n)) t)

pairArg : Parse (PArg Pairs)
pairArg = atom . located (|>) $ do
  n <- optional $ (paramLike (,) (\_ => (Explicit,) <$> identifier) identifier) <* symbol "="
  t <- tm
  pure $ \l => MkPArg l n t

piTel : Parse (PTel Functions)
piTel = MkPTel . fst <$> many1 piParam

lamTel : Parse (PTel Functions)
lamTel = MkPTel . fst <$> many1 lamParam

pairTel : Parse (PTel Pairs)
pairTel = MkPTel <$> parens (sepByOptEnd (symbol ",") pairParam)

piSpine : Parse (PSpine Functions)
piSpine = MkPSpine <$> many piArg

pairSpine : Parse (PSpine Pairs)
pairSpine = MkPSpine <$> parens (sepByOptEnd (symbol ",") pairArg)
        
directive : Parse Directive
directive = do
  string "#"
  s <- identifier
  pure $ MkDirective s

decl : Parse (String, Maybe PTy)
decl = do
  n <- identifier
  ty <- optional (symbol ":" >> tm)
  pure (n, ty)

endStatement : Parse ()
endStatement = (symbol ";" <|> symbol "\n") <* whitespace anySpace

-- (name : type) = value
letWithType : String -> PTy -> Parse (Loc -> PBlockStatement)
letWithType n ty = do
  symbol "="
  v <- tm
  pure $ \l => PLet l n (Just ty) v

-- (name : type) <- value
bindWithType : String -> PTy -> Parse (Loc -> PBlockStatement) 
bindWithType n ty = do
  symbol "<-"
  v <- tm
  pure $ \l => PBind l n (Just ty) v

-- (name : type) ; name [params] = value
letRec : String -> PTy -> Parse (Loc -> PBlockStatement)
letRec n ty = do
  endStatement
  symbol n
  tel <- optional lamTel
  symbol "="
  v <- tm
  let v' = case tel of
        Nothing => v
        Just tel => PLam tel v
  pure $ \l => PLetRec l n ty v'

-- (name : type)
justDecl : String -> PTy -> Parse (Loc -> PBlockStatement)
justDecl n ty = pure $ \l => PDecl l n ty

-- (name) := value
letWithoutType : String -> Parse (Loc -> PBlockStatement)
letWithoutType n = do
  symbol ":="
  v <- tm
  pure $ \l => PLet l n Nothing v

-- (name) <- value
bindWithoutType : String -> Parse (Loc -> PBlockStatement)
bindWithoutType n = do
  symbol "<-"
  v <- tm
  pure $ \l => PBind l n Nothing v
  
-- value
termStatement : Parse (Loc -> PBlockStatement)
termStatement = do 
  t <- tm
  pure $ \l => PBlockTm l t

blockStatement = atom . located (|>) $ do
  ds <- optional $ sepBy (whitespace anySpace) directive
  whitespace anySpace 
  wrapInDirectives (fromMaybe [] ds) <$> ((decl >>= \case
      (n, Just ty) => letWithType n ty <|> bindWithType n ty <|> letRec n ty <|> justDecl n ty
      (n, Nothing) => letWithoutType n <|> bindWithoutType n
    ) <|> termStatement)
  where
    wrapInDirectives : List Directive -> (a -> PBlockStatement) -> (a -> PBlockStatement)
    wrapInDirectives [] y a = y a
    wrapInDirectives (x :: xs) y a = PDirSt x (wrapInDirectives xs y a)

block : Parse PTm
block = located PLoc . curlies $ do
  statements <- sepBy endStatement blockStatement
  pure $ PBlock False statements

name : Parse PTm
name = located PLoc $ PName <$> identifier

lam : Parse PTm
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

pi : Parse PTm
pi = located PLoc $ do
  tel <- piTel
  symbol "->"
  ty <- tm
  pure $ PPi tel ty

unit : Parse PTm
unit = located PLoc $ symbol "()" >> pure PUnit

sigma : Parse PTm
sigma = located PLoc $ do
  t <- pairTel
  pure $ PSigmas t

pairs : Parse PTm
pairs = located PLoc $ do
  sp <- pairSpine
  pure $ PPairs sp

hole : Parse PTm
hole = located PLoc $
  (string "?" >> PHole . Just <$> identifier) <|> (symbol "?" >> pure (PHole Nothing))

literal : Parse PTm
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
        <|> satisfy (/= '"')

    parseChar =
      (string "\\\\" >> pure '\\')
        <|> (string "\\'" >> pure '\'')
        <|> satisfy (/= '\'')

dirTm : Parse PTm
dirTm = located PLoc $ do
  d <- directive
  t <- tm
  pure $ PDirTm d t
  
oneOf : List (Lazy (Parse a)) -> Parse a
oneOf = choice

singleTm = do
  hd <- atom $ oneOf [block, parens tm, name, literal, unit, sigma, pairs, hole]
  n <- optional (string ".")
  case n of
    Nothing => pure hd
    Just _ => identifier >>= \n => pure $ PProj hd n

tm = atom $ oneOf [dirTm, lam, pi, app]

-- This is what should be parsed at the top level
public export
topLevelBlock : Parse PTm
topLevelBlock = located PLoc $ do
  statements <- sepBy endStatement blockStatement
  pure $ PBlock True statements

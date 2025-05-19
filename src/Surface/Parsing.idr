module Surface.Parsing

import Data.List

import Surface.Presyntax
import Utils

import Control.Monad.Trans
import Data.List
import Data.String
import Data.DPair
import Data.Fin

%default covering

-- Setup:

public export
data ParseError : Type where
  TrailingChars : ParseError
  Empty : ParseError
  EndOfInput : ParseError
  UnexpectedChar : Char -> ParseError
  ReservedWord : String -> ParseError

public export
Show ParseError where
  show TrailingChars = "Trailing characters"
  show Empty = "Empty input"
  show EndOfInput = "Unexpected end of input"
  show (UnexpectedChar c) = "Unexpected character: " ++ show c
  show (ReservedWord s) = "Reserved word: " ++ s

public export
record ParserState where
  constructor MkParserState
  stream : List Char
  pos : Fin (length stream)

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
  empty = MkParser $ \ts => Left Empty
  (<|>) p q = MkParser $ \ts => case runParser p ts of
    Left _ => runParser q ts
    Right (a, ts') => Right (a, ts')

fail : ParseError -> Parser a
fail s = MkParser $ \ts => Left s

optional : Parser a -> Parser (Maybe a)
optional p = MkParser $ \ts => case runParser p ts of
  Left _ => Right (Nothing, ts)
  Right (a, ts') => Right (Just a, ts')

indexNext : ParserState -> Maybe (Char, Lazy ParserState)
indexNext (MkParserState [] pos) impossible
indexNext (MkParserState (_ :: []) FZ) = Nothing
indexNext (MkParserState (x :: y :: ys) FZ) = Just (y, MkParserState (x :: y :: ys) (FS FZ))
indexNext (MkParserState (x :: xs) (FS n)) = case indexNext (MkParserState xs n) of
  Nothing => Nothing
  Just (c, MkParserState xs' n') => Just (c, MkParserState (x :: xs') (FS n'))

peek : Parser (Maybe Char)
peek = MkParser $ \ts => case indexNext ts of
  Nothing => Right (Nothing, ts)
  Just (c, _) => Right (Just c, ts)


satisfy : (Char -> Bool) -> Parser Char
satisfy p = MkParser $ \ts => case indexNext ts of
  Nothing => Left EndOfInput
  Just (c, p') => if p c
    then Right (c, p')
    else Left $ UnexpectedChar c

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

string : String -> Parser ()
string s = traverse_ char (unpack s)

whitespace : Parser ()
whitespace =  do
  _ <- many (satisfy isSpace)
  (( do
      p <- string "--"
      _ <- many (satisfy (\c => c /= '\n' && c /= '\r'))
      whitespace
    ) <|> (pure ()))
  pure ()

atom : Parser a -> Parser a
atom p = p <* whitespace

symbol : String -> Parser ()
symbol s = atom $ string s

parens : Parser a -> Parser a
parens p = between (symbol "(") (symbol ")") p

curlies : Parser a -> Parser a
curlies p = between (symbol "{") (symbol "}") p

brackets : Parser a -> Parser a
brackets p = between (symbol "[") (symbol "]") p

located : (Loc -> a -> b) -> Parser a -> Parser b
located f p = MkParser $ \ts => case runParser p ts of
  Left s => Left s
  Right (a, ts') => Right (f (MkLoc ts.stream ts.pos) a, ts')

-- Actual language:

reserved : List String
reserved = []

identifier : Parser String
identifier = do
  c <- satisfy isAlpha
  cs <- many $ satisfy (\c => isAlphaNum c || c == '-' || c == '_')
  let n = pack (c :: cs)
  if n `elem` reserved
    then fail $ ReservedWord n
    else pure n

public export
tm : Parser PTm

singleTm : Parser PTm

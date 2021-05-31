module Parser.ParserValue ( pValue, parserValue ) where

import Value
import ProgAsValue
import Parser.ParserBase

import Data.Char
import Text.Parsec
import Control.Applicative hiding ( (<|>) )

-- Parsea un Value
pRawVal :: PStateWhile p => ParserW p Value
pRawVal =  try pAtom 
       <|> parens' pDot
       <?> "raw value"

pAtom :: PStateWhile p => ParserW p Value
pAtom = VAtom Nil <$ string "nil"

pDot :: PStateWhile p => ParserW p Value
pDot = Dot <$> pRawVal <* spaces <* char '.' <* spaces <*> pRawVal

pListVal :: PStateWhile p => ParserW p Value
pListVal =  pAtom
        <|> parens' pSList
        <?> "syntax sugar value"

pSList :: PStateWhile p => ParserW p Value
pSList = foldr Dot (VAtom Nil) <$> sepBy1 pListVal (many1 space)

pNumVal :: PStateWhile p => ParserW p Value
pNumVal = (iToV . fst . foldl buildNum (0,0) . reverse) <$> pList pDigit
    where buildNum :: (Int,Int) -> Int -> (Int,Int)
          buildNum (s,e) n = (s + n * 10^e,e+1)

pDigit :: PStateWhile p => ParserW p Int
pDigit = (\c -> ord c - ord '0') <$> choice pD
    where pD :: PStateWhile p => [ParserW p Char]
          pD = map char "0123456789"

pList :: PStateWhile p => ParserW p a -> ParserW p [a]
pList pa = (:) <$> pa <*> pList' pa
        <?> "pList"

pList' :: PStateWhile p => ParserW p a -> ParserW p [a]
pList' pa = (:) <$> pa <*> pList' pa
         <|> return []

-- Parsea un programa y lo convierte en Value
pProgValue :: PStateWhile p => ParserW p Value
pProgValue = progToValue <$> pProg
          
pValue ::PStateWhile p => ParserW p Value
pValue =  try pRawVal
      <|> try pProgValue
      <|> try pNumVal
      <|> pListVal
      <?> "value"
          
parserValue :: String -> Either ParseError Value
parserValue = runParser (pValue >>= \v -> eof >> return v) initState ""

-- función auxiliar
parens' :: PStateWhile p => ParserW p a -> ParserW p a
parens' pa = char '(' *> pa <* char ')'

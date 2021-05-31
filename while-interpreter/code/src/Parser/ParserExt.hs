{-# LANGUAGE RankNTypes #-}
{- Parser para el lenguaje extendido -}
module Parser.ParserExt ( pProg
                        , pProgs 
                        , initState) where

import Parser.ParserValue ( pValue )
import Parser.ParserBase hiding (PState (..),initState,pProg)

import Expr ( Expr, valAsExpr )
import ProgAsValue 
import Value ( Value , iToV)
import ExtendedLanguage.ExtLanguage

import Text.Parsec
import qualified Text.Parsec.Token as P
import qualified Data.Map as M
import Control.Monad ( void )
import Control.Arrow ( (&&&) )
import Control.Applicative ( (<$), (<$>), (<*), (<*>) )

type PattName = String

type PattsDefs = M.Map PattName Value

-- Estado del parser extendido
data PExtState = PExtState { maxv     :: Int
                           , mapv     :: VarNames
                           , lexer    :: P.TokenParser PExtState
                           , pnames   :: ProgNames
                           , patts    :: PattsDefs
                           , nextPatt :: Int
                           }
                           
instance PStateWhile PExtState where
    getMaxv       = maxv
    getMapv       = mapv
    getLexer      = lexer
    setMaxv v st  = st { maxv  = v }
    setMapv m st  = st { mapv  = m }
    setLexer l st = st { lexer = l }

addPName :: Name -> ExtProg -> PExtState -> PExtState
addPName name prog pst = pst { pnames = M.insert name prog (pnames pst) }

addPattDef :: PattName -> Value -> PExtState -> PExtState
addPattDef patt val pst = pst { patts = M.insert patt val (patts pst) }

getPattDef :: PattName -> ParserW PExtState Value
getPattDef patt = getState >>= \st ->
                  maybe (parserFail "") return $ M.lookup patt $ patts st

keywords :: [String]
keywords = keywordsBase ++
           [ "if"
           , "then"
           , "else"
           , "fi"
           , "rewrite"
           , "by"
           , "==>"
           , "case"
           , "of"
           , "end"
           , "prog"
           , "pattern"
           , "quote"
           ]

language :: forall u . P.LanguageDef u
language = langBase { P.opStart       = oneOf "~:=.[]"
                    , P.reservedNames = keywords
                    }
           
lexerExt :: P.TokenParser u
lexerExt = P.makeTokenParser language

builtinPatts :: [(String,Value)]
builtinPatts = [ ("var"   , dvar    )
               , ("quote" , dquote  )
               , ("cons"  , dcons   )
               , ("hd"    , dhd     )
               , ("tl"    , dtl     )
               , ("=?"    , deq     )
               , ("*"     , dstar   )
               , ("univ"  , duniv   )
               , (":="    , dassign )
               , (";"     , dseq    )
               , ("while" , dwhile  )
               ]

initPatts :: PattsDefs
initPatts = M.fromList builtinPatts

initState :: PExtState
initState = PExtState { maxv     = 0
                      , mapv     = M.empty
                      , lexer    = lexerExt
                      , pnames   = M.empty
                      , patts    = initPatts
                      , nextPatt = -12
                      }

-- Parser de comandos simples
pESimpleComm :: ParserW PExtState ExtComm
pESimpleComm = choice ( map try
                      [ pCall
                      , pEassign
                      , pEwhile
                      , pif
                      , pifElse
                      , pRewrite
                      , pCase
                      ]
                      )
             <?> "comando"

getNextPatt :: ParserW PExtState Int
getNextPatt = nextPatt <$> getState

updatePattValue :: ParserW PExtState ()
updatePattValue = getNextPatt >>= \i ->
                  modifyState (\st -> st {nextPatt = i-1})

newPattValue :: ParserW PExtState Value
newPattValue =  getNextPatt >>= \i -> updatePattValue >> return (iToV i)

updatePattsDef :: PattName -> Value -> ParserW PExtState ()
updatePattsDef patt v = modifyState (addPattDef patt v)

pPattsDefs :: ParserW PExtState ()
pPattsDefs =  reserved "pattern" >> identifier >>= pPattVal
          <?> "pattern def"
    where pPattVal :: PattName -> ParserW PExtState ()
          pPattVal pn =  void $
                         try (colon >> pValue >>= updatePattsDef pn >> 
                              white >> semi)
                     <|> (newPattValue >>= updatePattsDef pn >> semi)

-- Expresion correspondiente del reemplazo de un pattern
pPattExpr :: ParserW PExtState Expr
pPattExpr = valAsExpr <$> (pPatt >>= getPattDef)

pEExpr :: ParserW PExtState Expr
pEExpr =  pExpr' pPattExpr

pEComm :: ParserW PExtState ExtComm
pEComm = (foldr1 ESeq <$> sepEndBy1 pESimpleComm semi)
      <|> parens pEComm

pEassign :: ParserW PExtState ExtComm
pEassign = EAssgn <$> pvar <* reservedOp ":=" <*> pEExpr

pEwhile :: ParserW PExtState ExtComm
pEwhile = EWhile <$ reserved "while" <*> pEExpr <*
                    reserved "do"    <*> pEComm <*
                    reserved "od"

pif :: ParserW PExtState ExtComm
pif =  If <$ reserved "if"   <*> pEExpr <*
             reserved "then" <*> pEComm <*
             reserved "fi"

pifElse :: ParserW PExtState ExtComm
pifElse = IfElse <$ reserved "if"   <*> pEExpr <*
                    reserved "then" <*> pEComm <*
                    reserved "else" <*> pEComm <*
                    reserved "fi"

pRewrite :: ParserW PExtState ExtComm
pRewrite = reserved "rewrite" >> 
           brackets (sepBy1 pvar comma) >>= \vars ->
           reserved "by" >>
           many1 (pRule $ length vars) >>= \rules ->
           reserved "end" >>
           return (Rewrite vars rules)

pRule :: Int -> ParserW PExtState Rule
pRule n = brackets (sepBy1 pPattern comma) >>= \pats ->
          checkNPatterns n pats >>
          reserved "==>" >>
          (pRuleE pats <|>
           pRuleC pats)
          <?>
          "rule"
    where pRuleE pats = brackets (sepBy1 pEExpr comma) >>= 
                        \es -> checkNPatterns n es >> 
                        return (RuleE $ zip pats es)
          pRuleC pats = pEComm >>= \c -> return (RuleC pats c)

checkNPatterns :: Int -> [a] -> ParserW PExtState ()
checkNPatterns n ls | n == length ls = return ()
                    | otherwise     = parserFail $ 
                                      unwords [ "La cantidad de patrones"
                                              , "debe coincidir con la cantidad"
                                              , "de variables"
                                              ]

pPatt :: ParserW PExtState PattName
pPatt = try identifier <|> choice (map (pBuiltinPatts . fst) builtinPatts)
    where pBuiltinPatts :: PattName -> ParserW PExtState PattName
          pBuiltinPatts str = try $ spaces >>
                                    string "'" >>
                                    reserved str >>
                                    string "'" >> spaces >>
                                    return str

pPattern :: ParserW PExtState Pattern
pPattern = (PNil <$ reserved "nil")
           <|>
           try (valAsPatt <$> (pPatt >>= getPattDef))
           <|>
           (PVar <$> pvar)
           <|>
           parens (PDot <$> pPattern <* reservedOp "." <*> pPattern)
           <?>
           "pattern"

pCase :: ParserW PExtState ExtComm
pCase = reserved "case" >> pvar >>= \v ->
        reserved "of" >> 
        many1 pCasePattern >>= \ps ->
        reserved "end" >>
        return (Case v ps)
          
pCasePattern :: ParserW PExtState (Pattern,ExtComm)
pCasePattern = pPattern >>= \p ->
               reserved "==>" >>
               pEComm >>= \c ->
               return (p,c)
               
pCall :: ParserW PExtState ExtComm
pCall = Call <$> pvar <* reservedOp ":=" <*> pName <* white <*> pvar

pName :: ParserW PExtState Name
pName = identifier >>= \name ->
        checkPName name >>
        return name

checkPName :: Name -> ParserW PExtState ()
checkPName name = pnames <$> getState >>= \pns -> 
                  maybe (parserFail $ "Programa " ++ name ++ " no definido.") 
                        (const $ return ()) (M.lookup name pns)

-- Parser de programas
pProg :: ParserW PExtState ExtProg
pProg = reserved "prog" >>
        identifier >>= \pname ->
        colon >>
        reserved "read" >>
        pvar >>= \v ->
        semi >>
        pEComm >>= \comm ->
        reserved "write" >>
        pvar >>= \w ->
        semi >>
        maxv <$> getState >>= \mv ->
        resetStateVars >>
        let prog = ExtProg { xread = v
                           , xwrite = w
                           , xcomm = comm
                           , maxvar = mv} in
            getState >>= \st -> 
            maybe (modifyState (addPName pname prog) >> return prog)
                  (const $ parserFail $ "Múltiples declaraciones para " 
                                        ++ pname)
                  (M.lookup pname $ pnames st)
               
pProgs :: ParserW PExtState (ExtProg,ProgNames)
pProgs = white >>
         many (pPattsDefs >> white) >>
         many1 pProg >>
         pnames <$> getState >>= \pns ->
         maybe (parserFail "Programa 'main' no encontrado.")
               (return . (id &&& const pns))
               (M.lookup "main" pns)

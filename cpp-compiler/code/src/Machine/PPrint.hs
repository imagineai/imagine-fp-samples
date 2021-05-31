module Machine.PPrint ( pprintCode ) where

import Machine.Code  ( RegName(..), Register(..), Size(..), MemAddress(..)
                     , MemArray(..), Mem(..), Location(..), Value(..), Label
                     , CmpFlags(..), Instruction(..), Code
                     )
import Machine.Monad ( Header(..), stringLabels )

pprintCode :: Code -> Header -> String
pprintCode c h = unlines 
                 [ pprintHeader h
                 , pprintMainHeader
                 , unlines (map pprintLI c)
                 ]

pprintHeader :: Header -> String
pprintHeader h = let sls = stringLabels h
                 in unlines (map pprintH sls)

pprintMainHeader :: String
pprintMainHeader = unlines 
                   [ ""
                   , ".globl main"
                   , ".type main, @function"
                   ]

pprintH :: (Label,String) -> String
pprintH (l,str) = unlines 
                  [ ""
                  , pprintLabelDots l
                  , whites10 ++ ".string " ++ show str
                  , whites10 ++ ".text"
                  , ""
                  ]

pprintLI :: (Label,Instruction) -> String
pprintLI (l, i) = pprintLabelDots l ++ pprintInstruction i

pprintLabelDots :: Label -> String
pprintLabelDots ""  = take 16 $ repeat ' '
pprintLabelDots str = str' ++ ": " ++ take (14 - length str') (repeat ' ')
    where str' :: String
          str' = pprintLabel str

pprintLabel :: Label -> String
pprintLabel "start" = "main"
pprintLabel "main" = ".main"
pprintLabel l      = l

pprintInstruction :: Instruction -> String
pprintInstruction (MOV s v l)  = pprintI "mov" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintLocation l
pprintInstruction (LEAQ ma r)  = "leaq" ++ whites4 ++ 
                                 pprintMemAddr ma ++ ", " ++ pprintRegister r
pprintInstruction (ADD s v l)  = pprintI "add" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintLocation l
pprintInstruction (SUB s v l)  = pprintI "sub" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintLocation l
pprintInstruction (IMUL s v r) = pprintI "imul" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintRegister r
pprintInstruction (NEG s l)    = pprintI "neg" s ++ whites4 ++ pprintLocation l
pprintInstruction (DIVL l)     = "divl" ++ whites4 ++ pprintLocation l
pprintInstruction CLTD         = "cltd"
pprintInstruction CLTQ         = "cltq"
pprintInstruction (AND s v l)  = pprintI "and" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintLocation l
pprintInstruction (OR s v l)   = pprintI "or" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintLocation l
pprintInstruction (CMP s v v') = pprintI "cmp" s ++ whites4 ++ 
                                 pprintValue v ++ ", " ++ pprintValue v' 
pprintInstruction (SET flag l) = pprintWithFlag "set" flag ++ whites4 ++ 
                                 pprintLocation l
pprintInstruction (J flag la)  = pprintWithFlag "j" flag ++ whites4 ++ 
                                 pprintLabel la
pprintInstruction (JMP la)     = "jmp"  ++ whites4 ++ pprintLabel la
pprintInstruction (CALL la)    = "call" ++ whites4 ++ pprintLabel la
pprintInstruction (ENTER v v') = "enter" ++ whites4 ++
                                  pprintValue v ++ ", " ++ pprintValue v' 
pprintInstruction SYSCALL      = "syscall"
pprintInstruction LEAVE        = "leave"
pprintInstruction RET          = "ret"
pprintInstruction NOP          = "nop"

pprintWithFlag :: String -> CmpFlags -> String
pprintWithFlag s E  = s ++ "e"
pprintWithFlag s NE = s ++ "ne"
pprintWithFlag s G  = s ++ "g"
pprintWithFlag s GE = s ++ "ge"
pprintWithFlag s L  = s ++ "l"
pprintWithFlag s LE = s ++ "le"

pprintI :: String -> Size -> String
pprintI is Byte = is ++ "b"
pprintI is Word = is ++ "w"
pprintI is Long = is ++ "l"
pprintI is Quad = is ++ "q"

pprintValue :: Value -> String
pprintValue (C i)     = "$" ++ show i
pprintValue (Loc loc) = pprintLocation loc
pprintValue (Str l)   = "$" ++ l

pprintLocation :: Location -> String
pprintLocation (MA ma) = pprintMem ma
pprintLocation (Reg r) = pprintRegister r

pprintMem :: Mem -> String
pprintMem (MAdd ma) = pprintMemAddr ma
pprintMem (MAR mar) = pprintMemAddArray mar

pprintMemAddr :: MemAddress -> String
pprintMemAddr (MAddr i r) = show i ++ "(" ++ pprintRegister r ++ ")"

pprintMemAddArray :: MemArray -> String
pprintMemAddArray (MemArr (MAddr i r) r' s) = 
               show i ++ "(" ++ pprintRegister r  ++ "," ++ 
                                pprintRegister r' ++ "," ++ 
                                pprintSize s ++
                         ")"

pprintSize :: Size -> String
pprintSize Byte = "1"
pprintSize Word = "2"
pprintSize Long = "4"
pprintSize Quad = "8"

pprintRegister :: Register -> String
pprintRegister (R s RAX) = pprintRegABCD "a"  s
pprintRegister (R s RBX) = pprintRegABCD "b"  s
pprintRegister (R s RCX) = pprintRegABCD "c"  s
pprintRegister (R s RDX) = pprintRegABCD "d"  s
pprintRegister (R s RSI) = pprintRegSDI  "s"  s
pprintRegister (R s RDI) = pprintRegSDI  "d"  s
pprintRegister (R s RSP) = pprintRegSBP  "s"  s
pprintRegister (R s RBP) = pprintRegSBP  "b"  s
pprintRegister (R s R8)  = pprintReg8_15 "8"  s
pprintRegister (R s R9)  = pprintReg8_15 "9"  s
pprintRegister (R s R10) = pprintReg8_15 "10" s
pprintRegister (R s R11) = pprintReg8_15 "11" s
pprintRegister (R s R12) = pprintReg8_15 "12" s
pprintRegister (R s R13) = pprintReg8_15 "13" s
pprintRegister (R s R14) = pprintReg8_15 "14" s
pprintRegister (R s R15) = pprintReg8_15 "15" s

pprintRegABCD :: String -> Size -> String
pprintRegABCD rs Byte = "%"  ++ rs ++ "l"
pprintRegABCD rs Word = "%"  ++ rs ++ "x"
pprintRegABCD rs Long = "%e" ++ rs ++ "x"
pprintRegABCD rs Quad = "%r" ++ rs ++ "x"

pprintRegSDI :: String -> Size -> String
pprintRegSDI rs Byte = "%"  ++ rs ++ "il"
pprintRegSDI rs Word = "%"  ++ rs ++ "i"
pprintRegSDI rs Long = "%e" ++ rs ++ "i"
pprintRegSDI rs Quad = "%r" ++ rs ++ "i"

pprintRegSBP :: String -> Size -> String
pprintRegSBP rs Byte = "%"  ++ rs ++ "l"
pprintRegSBP rs Long = "%"  ++ rs ++ "p"
pprintRegSBP rs Word = "%e" ++ rs ++ "p"
pprintRegSBP rs Quad = "%r" ++ rs ++ "p"

pprintReg8_15 :: String -> Size -> String
pprintReg8_15 rs Byte = "%"  ++ rs ++ "b"
pprintReg8_15 rs Word = "%r" ++ rs ++ "w"
pprintReg8_15 rs Long = "%r" ++ rs ++ "d"
pprintReg8_15 rs Quad = "%r"  ++ rs

whites10 :: String
whites10 = take 10 $ repeat ' '

whites4 :: String
whites4 = take 4 $ repeat ' '

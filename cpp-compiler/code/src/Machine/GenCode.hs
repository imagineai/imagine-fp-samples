module Machine.GenCode where

import Machine.Code  ( Size(..), Code, Location(..), Instruction(..), Value(..)
                     , Register(..), RegName(..), Label, CmpFlags(..)
                     , locToValue, mkInst
                     , eax, rsp, rdi, mov
                     , MemAddress(..), minMAddr, selfAddr
                     , fMemArg, nextMemArg, fRegArg, nextRegArg, maToLoc
                     , typeToSize, memArr
                     )
import Machine.Monad ( Machine, MemAssign, icRegToLoc, icOpToValue
                     , addMAssign, emptyMAssign, icTypeToMSize
                     , lookupMAss, lookupType, icOpToType, stickMLabel
                     , setStoreG, unionMemAssign
                     )
import Machine.BoolCode  ( boolCodeNot, boolCodeRel, boolCodeEq, boolCodeCond )
import Machine.ArithCode ( arithCode, arithCodeNeg )

import Syntax ( Type(..), UnOp(..), BinOp(..) )
import qualified InterCode as IC ( Label(..), Size, Register, Operand
                                 , InterCode'(..), InterCode
                                 , nextRegister
                                 )

import Control.Monad       ( foldM, forM )
import Control.Applicative ( (<$>) )

icLabelToCode :: IC.Label -> Label
icLabelToCode (IC.L (l,n)) | length l == 0 = ""
                           | otherwise = let strn = if n < 1 then "" else show n
                                         in l ++ strn

lstart :: Label
lstart = "start"

genCode :: IC.InterCode -> Machine Code
genCode ic = concat <$> forM ic icToCode

icUOpToCode :: UnOp -> IC.Operand -> IC.Register -> Machine Code
icUOpToCode Neg = arithCodeNeg
icUOpToCode Not = boolCodeNot

icBOpToCode :: BinOp -> IC.Operand -> IC.Operand -> IC.Register -> Machine Code
icBOpToCode (Arith aop) = arithCode aop
icBOpToCode (Rel rop)   = boolCodeRel rop
icBOpToCode (Eq eop)    = boolCodeEq eop
icBOpToCode (Cond cop)  = boolCodeCond cop

icToCode :: (IC.Label,IC.InterCode') -> Machine Code
icToCode (_,IC.StoreG tss) = 
                     setStoreG tss >>
                     return ( [ (lstart, ENTER (C $ sizeGlobals tss) (C 0)) ]
                             ++ mkLEAQ tss
                             ++ map mkInst [CALL "main", LEAVE, RET]
                             )
icToCode (l,IC.Store reg tss) =
    let (mass,sizevars) = icRegToMem reg tss
        popSelf         = map mkInst $ mov Quad (Loc rdi) (maToLoc selfAddr)
    in unionMemAssign mass >> 
       return ([(icLabelToCode l,ENTER (C sizevars) (C 0))] ++ popSelf)
icToCode (l,IC.UAssign uop v r) =
    icUOpToCode uop v r >>= return . stickMLabel (icLabelToCode l)
icToCode (l,IC.BAssign bop v1 v2 r) =
    icBOpToCode bop v1 v2 r >>= return . stickMLabel (icLabelToCode l)
icToCode (l,IC.ICAssign v r) =
    icOpToValue v >>= \(valic,mval) ->
    lookupType r >>= \ty ->
    icRegToLoc r >>= \(locic,loc) ->
    let size = typeToSize ty
    in return $ stickMLabel (icLabelToCode l) $
                map mkInst $ valic ++ locic ++ mov size mval loc
icToCode (l,IC.CallE icl ps) =
    putFirst6Args ps >>= \code6Args ->
    putRemainArgs ps >>= \codeRemArgs ->
    let puts = stickMLabel (icLabelToCode l) $ map mkInst $
                                               codeRemArgs ++ code6Args
        resetRAX = map mkInst $ mov Quad (C 0) (Reg $ R Quad RAX)
    in return $ puts ++ resetRAX ++ [ mkInst (CALL (icLabelToCode icl)) ]
icToCode (l,IC.Call icl ps) = 
    putFirst5Args ps >>= \code5Args ->
    putRemainArgs ps >>= \codeRemArgs ->
    let putSelf = stickMLabel (icLabelToCode l) $ 
                  map mkInst $ mov Quad (Loc $ maToLoc selfAddr) rdi
                                               
        puts = map mkInst $ codeRemArgs ++ code5Args
    in return $ putSelf ++ puts ++ [ mkInst (CALL (icLabelToCode icl)) ]
    
icToCode (l,IC.PopParams rs) =
    popFirst6Args rs >>= \code6Args ->
    popRemainArgs rs >>= \codeRemArgs ->
    return $ stickMLabel (icLabelToCode l) $ map mkInst $ 
             codeRemArgs ++ code6Args
icToCode (l,IC.Jump l') = return [(icLabelToCode l,JMP $ icLabelToCode l')]
icToCode (l,IC.ICReturn) = return [(icLabelToCode l,LEAVE),mkInst RET]
icToCode (l,IC.ICSkip) = return [(icLabelToCode l,NOP)]
icToCode (l,IC.PutReturn r) =
        lookupMAss r >>= \(maic,ma) ->
        typeToSize <$> lookupType r >>= \size ->
        return $ stickMLabel (icLabelToCode l) $ map mkInst $
                 maic ++
                 mov size (locToValue $ maToLoc ma) (Reg $ R size RAX)
icToCode (l,IC.PopReturn r) = 
        lookupMAss r >>= \(maic,ma) ->
        typeToSize <$> lookupType r >>= \size ->
        return $ stickMLabel (icLabelToCode l) $ map mkInst $
                 maic ++
                 mov size (locToValue $ Reg $ R size RAX) (maToLoc ma)
icToCode (l,IC.JumpCnd op _ lf) =
    icOpToValue op >>= \(opic,mval) ->
    return $ stickMLabel (icLabelToCode l) $ map mkInst $
    opic ++
    [ CMP Byte (C 0) mval
    , J E (icLabelToCode lf)
    ]
-- Arrays
icToCode (l,IC.AssignArray v offset r) =
    lookupMAss r >>= \(maic,ma) ->
    typeToSize <$> lookupType r >>= \size ->
    icOpToValue offset >>= \(offic,moff) ->
    icOpToValue v >>= \(valic,mval) ->
    return $ stickMLabel (icLabelToCode l) $ map mkInst $
      offic ++
      mov Long moff eax ++
      [ CLTQ ] ++
      valic ++
      maic ++
      mov size mval (MA $ memArr ma (R Quad RAX) size)
icToCode (l,IC.ICArrAssign r offset rdest) =
    lookupMAss r >>= \(maric,mar) ->
    lookupMAss rdest >>= \(mdestic,mdest) ->
    typeToSize <$> lookupType r >>= \size ->
    icOpToValue offset >>= \(offic,moff) ->
    return $ stickMLabel (icLabelToCode l) $ map mkInst $
      offic ++
      mov Long moff eax ++
      [ CLTQ ] ++
      maric ++
      mdestic ++
      mov size (locToValue $ MA $ memArr mar (R Quad RAX) size) (maToLoc mdest)

mkLEAQ :: [(Type,IC.Size)] -> Code
mkLEAQ [] = []
mkLEAQ ((ty,s):_) = [ mkInst $ LEAQ maddr regRDI ]
    where
        maddr :: MemAddress
        maddr = MAddr (- (icTypeToMSize ty) * s) (R Quad RBP)
        regRDI :: Register
        regRDI   = R Quad RDI

putFirst5Args :: [IC.Operand] -> Machine [Instruction]
putFirst5Args = putFirstNArgs 5 RSI

putFirst6Args :: [IC.Operand] -> Machine [Instruction]
putFirst6Args = putFirstNArgs 6 fRegArg

putFirstNArgs :: Int -> RegName -> [IC.Operand] -> Machine [Instruction]
putFirstNArgs n rn vs =
    fst <$>
    foldM (\(c,reg) v ->
            (typeToSize <$> icOpToType v) >>= \size ->
            icOpToValue v >>= \(valic,mval) -> return
            (c ++ valic ++ mov size mval (Reg $ R size reg) , nextRegArg reg)) 
          ([],rn) (take n vs)
          
putRemainArgs :: [IC.Operand] -> Machine [Instruction]
putRemainArgs vs | length vs <= 6 = return []
putRemainArgs vs | otherwise =
    let remArgs = drop 6 vs
        lenRemArgs = toInteger $ length remArgs
    in
    fst <$>
    foldM (\(c,ma) v ->
            typeToSize <$> icOpToType v >>= \size ->
            icOpToValue v >>= \(valic,mval) -> return 
            (c ++ valic ++ mov size mval (maToLoc ma) , nextMemArg ma))
          ([SUB Quad (C $ 8 * lenRemArgs) rsp],
           fMemArg) remArgs
           
           
popFirst6Args :: [IC.Register] -> Machine [Instruction]
popFirst6Args rs =
    fst <$>
    foldM (\(c,reg) r ->
            lookupMAss r >>= \(maic,ma) ->
            typeToSize <$> lookupType r >>= \size ->
            return ( c ++ maic ++
                     mov size (locToValue $ Reg $ R size reg) (maToLoc ma)
                   , nextRegArg reg)
            )
          (selfArg,RSI) (take 6 rs)
    where
        selfArg = mov Quad (Loc rdi) $ maToLoc selfAddr
          
popRemainArgs :: [IC.Register] -> Machine [Instruction]
popRemainArgs rs =
    let remArgs = drop 6 rs
    in
    fst <$>
    foldM (\(c,mastack) r ->
            lookupMAss r >>= \(maic,mar) ->
            typeToSize <$> lookupType r >>= \size ->
            return  ( c ++ maic ++ 
                      mov size (locToValue $ maToLoc mastack) (maToLoc mar)
                    , nextMemArg mastack)
                    )
          ([],fMemArg) remArgs

sizeGlobals :: [(Type,IC.Size)] -> Integer
sizeGlobals = foldl (\i (ty,s) -> i + (icTypeToMSize ty) * s) 0
    
icRegToMem :: IC.Register -> [(Type,IC.Size)] -> (MemAssign,Integer)
icRegToMem reg tss = 
    let (mass,i,_,_) = foldl f (emptyMAssign,8,reg,selfAddr) tss
    in (mass,i)
    where f :: (MemAssign,Integer,IC.Register,MemAddress) -> (Type,IC.Size) -> 
               (MemAssign,Integer,IC.Register,MemAddress)
          f (m,i,r,ma) (ty,s) = 
              let sizety = (icTypeToMSize ty) * s
                  maddr = (minMAddr ma sizety)
              in
                ( addMAssign r (maddr,ty) m
                , i + sizety
                , IC.nextRegister r
                , maddr
                )

  

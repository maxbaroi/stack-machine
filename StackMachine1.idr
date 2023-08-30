module StackMachine1

import Data.Nat

import Data.List

import Data.Maybe

data Binop = Plus | Times

data Instr = IConst Nat | IBinop Binop

data Exp = EConst Nat | EBinop Binop Exp Exp

Prog = List Instr
Stack = List Nat

binopDenote : Binop -> Nat -> Nat -> Nat
binopDenote Plus = (+)
binopDenote Times = (*)

expDenote : Exp -> Nat
expDenote (EConst n) = n
expDenote (EBinop b e1 e2) = (binopDenote b) (expDenote e1) (expDenote e2)


instrDenote : Instr -> Stack -> Maybe Stack
instrDenote (IConst n) s = Just (n :: s)
instrDenote (IBinop b) (x :: (y :: zs)) = let h = ((binopDenote b) x y) in 
                                              Just (h :: zs)
instrDenote (IBinop _) _ = Nothing

progDenote : Prog -> Stack -> Maybe Stack
progDenote [] s = Just s
progDenote (i :: p) s = case instrDenote i s of
                             (Just s') => progDenote p s'
                             Nothing => Nothing
                             
compile : Exp -> Prog
compile (EConst n) = [IConst n]                             
compile (EBinop b e1 e2) = compile e2 ++ compile e1 ++ [IBinop b ]                      
compilerHelper1 : (b : Binop) -> (e1 , e2 : Exp) -> (p : Prog) -> (s : Stack)
  -> progDenote (compile (EBinop b e1 e2) ++ p) s 
    = progDenote ((compile e2 ++ (compile e1 ++ [IBinop b])) ++ p) s
compilerHelper1 e1 e2 b p s = Refl
              
compilerCorrect : (e : Exp) -> (p : Prog) -> (s : Stack)
  -> progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)
compilerCorrect (EConst n) p s = Refl
compilerCorrect (EBinop b e1 e2) p s = 
   rewrite sym (appendAssociative (compile e2) (compile e1 ++ [IBinop b]) p) in 
   rewrite compilerCorrect e2 ((compile e1 ++ [IBinop b]) ++ p) s in 
   rewrite sym (appendAssociative (compile e1) [IBinop b] p) in 
   rewrite compilerCorrect e1 ([IBinop b] ++ p) (expDenote e2 :: s) in Refl

  
                                                                                                        

              

module StackMachine2

import Data.Nat

import Data.List

import Data.Maybe

import Data.Vect

data Binop = Plus | Times

data Exp = EConst Nat | EBinop Binop Exp Exp

Stack : Nat -> Type
Stack n = Vect n Nat

binopDenote : Binop -> Nat -> Nat -> Nat
binopDenote Plus = (+)
binopDenote Times = (*)

expDenote : Exp -> Nat
expDenote (EConst n) = n
expDenote (EBinop b e1 e2) = (binopDenote b) (expDenote e1) (expDenote e2)


data Instr : Nat -> Nat -> Type where
  IConst : Nat -> Instr x (S x) 
  IBinop : Binop -> Instr (S (S x)) (S x)
  
  
data Prog : Nat -> Nat -> Type where
  PNil : Prog n n
  PCons : Instr i j -> Prog j k -> Prog i k
  
instrDenote : Instr m n -> Stack m -> Stack n
instrDenote (IConst k) s = k :: s
instrDenote (IBinop b) (x :: (y :: zs)) = (binopDenote b) x y :: zs

{-- changing n to m in Stack produces an immedaite error)-}
progDenote : Prog m n -> Stack m -> Stack n
progDenote PNil s = s
progDenote (PCons i p) s = progDenote p (instrDenote i s)

{- -}
test1 : progDenote (PCons (IConst 1) (PCons (IConst 2) PNil)) [] = [2 , 1]
test1 = Refl

progConcat : Prog i j -> Prog j k -> Prog i k
progConcat PNil p2 = p2
progConcat (PCons inst p1) p2 = PCons inst (progConcat p1 p2)

compile : Exp -> Prog n (S n)
compile (EConst k) = PCons (IConst k) PNil
compile (EBinop b e1 e2) = 
  progConcat (compile e2) (progConcat (compile e1) (PCons (IBinop b) PNil))
  
exp1 : Exp
exp1 = EBinop Times (EConst 2) (EConst 2)

test2 : (progDenote (compile StackMachine2.exp1) []) = [4]
test2 = Refl

progConcatAssoc : (p1 : Prog i j) -> (p2 : Prog j k) -> (p3 : Prog k l)
  -> (progConcat (progConcat p1 p2) p3) = progConcat p1 (progConcat p2 p3)
progConcatAssoc PNil p2 p3 = Refl
progConcatAssoc (PCons ins p1) p2 p3 =
  rewrite progConcatAssoc p1 p2 p3 in Refl

{- (s : Stack ?a) to help me narrow down the correct type -}
compileCorrect : (e : Exp) -> (p : Prog (S m) n) -> (s : Stack m)
  -> progDenote (progConcat (compile e) p) s = progDenote p ((expDenote e) :: s)
compileCorrect (EConst k) p s = Refl
compileCorrect (EBinop b e1 e2) p s = 
  rewrite progConcatAssoc (compile e2) 
                          (progConcat (compile e1) (PCons (IBinop b) PNil)) 
                          p in
  rewrite compileCorrect e2 
                         (progConcat (progConcat (compile e1)
                                                 (PCons (IBinop b) PNil))
                                      p)
                         s in
  rewrite progConcatAssoc (compile e1)
                          (PCons (IBinop b) PNil)
                          p in
  rewrite compileCorrect e1
                         (PCons (IBinop b) p)
                         (expDenote e2 :: s) in Refl

              

module StackMachine3

import Data.Nat

import Data.List

import Data.Maybe

%hide Prelude.Bool

data Bool = True | False

not : Bool -> Bool
not True = False
not False = True

(&&) : Bool -> Bool -> Bool
True && y = y
False && _ = False

(||) : Bool -> Bool -> Bool
True || _ = True 
False || y = y

eqb : Bool -> Bool -> Bool
eqb True True = True
eqb True False = False 
eqb False True = False 
eqb False False = True

eqn : Nat -> Nat -> Bool
eqn 0 0 = True
eqn 0 (S _) = False
eqn (S _) 0 = False 
eqn (S j) (S k) = eqn j k 

lte : Nat -> Nat -> Bool
lte 0 _ = True
lte (S _) 0 = False
lte (S j) (S k) = lte j k 

eif : Bool -> a -> a -> a
eif True a _ = a
eif False _ b = b

data SType = SNat | SBool

data Uniop : SType -> SType -> Type where
  Not : Uniop SBool SBool
  Succ : Uniop SNat SNat
  
data Binop : SType -> SType -> SType -> Type where
  Plus : Binop SNat SNat SNat
  Mult : Binop SNat SNat SNat
  And : Binop SBool SBool SBool
  Or : Binop SBool SBool SBool
  LTE : Binop SNat SNat SBool
  Equals : (t : SType) -> Binop t t SBool

data Triop : SType -> SType -> SType -> SType -> Type where
  If : (t : SType) -> Triop SBool t t t

--Type saefty of the expression language is forced by the ambient type setting
data Exp : SType -> Type where
  ENConst : Nat -> Exp SNat
  EBConst : Bool -> Exp SBool
  EUniop : (t , u  : SType) -> Uniop t u -> Exp t -> Exp u
  EBiop : (s , t , u  : SType) -> Binop s t u -> Exp s -> Exp t -> Exp u
  ETriniop : (r, s, t , u  : SType) -> Triop r s t u 
    -> Exp r -> Exp s -> Exp t -> Exp u

typeDenote : SType -> Type
typeDenote SNat = Nat
typeDenote SBool = Bool

uniDenote : Uniop t u -> typeDenote t -> typeDenote u
uniDenote Not = not
uniDenote Succ = S

binDenote : Binop s t u -> typeDenote s ->  typeDenote t -> typeDenote u
binDenote Plus = (+)
binDenote Mult = (*)
binDenote And = (&&)
binDenote Or = (||)
binDenote LTE = lte
binDenote (Equals SNat) = eqn
binDenote (Equals SBool) = eqb

--The "right" eif will be selected
triDenote : Triop r s t u -> typeDenote r -> typeDenote s ->  typeDenote t 
  -> typeDenote u
triDenote (If _) = eif 

expDenote : Exp a -> typeDenote a
expDenote (ENConst k) = k
expDenote (EBConst b) = b
expDenote (EUniop _ _ f e) = (uniDenote f) (expDenote e)
expDenote (EBiop _ _ _ f e1 e2) = (binDenote f) (expDenote e1) (expDenote e2)
expDenote (ETriniop _ _ _ _ f e1 e2 e3) = 
  (triDenote f) (expDenote e1) (expDenote e2) (expDenote e3)

TypeStack = List SType
data ValueStack : TypeStack -> Type where
  Empty : ValueStack []
  Cons : {t : SType} -> typeDenote t -> ValueStack vs -> ValueStack (t :: vs)

data Instr : TypeStack -> TypeStack -> Type where
  INConst : (n : Nat) -> (s : TypeStack) -> Instr s (SNat :: s)
  IBConst : (b : Bool) -> (s : TypeStack) -> Instr s (SBool :: s)
  


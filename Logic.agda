module Logic (Const Func Var Pred : Set)  where
open import Data.List hiding (all ; and ; or )
open import Data.Bool hiding ( not ; _∧_ ; _∨_ )

data Expr  : Set  where
   var   : Var   → Expr 
   func  : Func  → Expr → Expr 
   const : Const → Expr 
   _,_   : Expr  → Expr → Expr 

data Statement : Set where
   pred       : Pred      → Statement 
   predx      : Pred      → Expr      → Statement 
   _∧_        : Statement → Statement → Statement 
   _∨_        : Statement → Statement → Statement 
   ¬_         : Statement → Statement 
   All_=>_    : Var       → Statement → Statement 
   Exist_=>_  : Var       → Statement → Statement 

--
-- The interpretation
--   all-const is a list of all possible arguments of predicates (possibly infinite)
--   sbst is an Expr depenent variable substituion
--
{-# TERMINATING #-} 
M : (amap :  Pred  → Bool ) (pmap :  Pred → Expr → Bool )
   → (all-const   : List Expr )
   → (sbst : Expr  → Var →  Expr  → Expr  )
   → Statement  → Bool
M amap pmap all0 sbst s = m s where

   --   Expr indepenent variable substituion using Expr substution (sbst)
   _[_/_] :  (e : Statement  ) → Var → Expr → Statement 
   (pred x) [ xv / v ]     = pred x
   (predx x x₁) [ xv / v ] = predx x ( sbst x₁ xv v )
   (e ∧ e₁) [ xv / v ]     = (  e [ xv / v ]) ∧ (  e₁ [ xv / v ])
   (e ∨ e₁) [ xv / v ]     = (  e [ xv / v ]) ∨ (  e₁ [ xv / v ])
   (¬ e) [ xv / v ]        = ¬ (  e [ xv / v ])
   (All x => e) [ xv / v ]   = All x =>   (  e [ xv / v ])   -- we should protect variable x from replacement
   (Exist x => e) [ xv / v ] = Exist x => (  e [ xv / v ])

   m :  Statement  → Bool
   m (pred x)     = amap x
   m (predx x x₁) = pmap x x₁
   m (s ∧ s₁)     = m s  Data.Bool.∧ m s₁ 
   m (s ∨ s₁)     = m s Data.Bool.∨ m s₁ 
   m (¬ s)        = Data.Bool.not (m s )
   -- an esasy emulation of quantifier using a variable free expr list
   m (All x => s) = m-all all0 x s  where
     m-all   : List Expr → Var → Statement → Bool
     m-all   [] vx s = true
     m-all   (x ∷ t) vx s = m ( s [ vx / x ]) Data.Bool.∧ m-all   t vx s
   m (Exist x => s) = m-exist all0 x s  where
     m-exist : List Expr → Var → Statement → Bool
     m-exist [] vx s = false
     m-exist (x ∷ t) vx s = m ( s [ vx / x ] ) Data.Bool.∨ m-exist t vx s



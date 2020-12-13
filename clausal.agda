module clausal (Const Func Var Pred : Set)  where
open import Data.List hiding (all ; and ; or )
open import Data.Bool hiding ( not ; _∧_ ; _∨_ )
open import Function

open import Logic Const Func Var Pred 

-- data Expr  : Set  where
--    var   : Var → Expr 
--    func  : Func → Expr → Expr 
--    const : Const → Expr 
--    _,_ : Expr →Expr → Expr 

-- data Statement : Set where
--    pred       : Pred  → Statement 
--    predx  : Pred  → Expr → Statement 
--    _∧_   : Statement → Statement  → Statement 
--    _∨_         : Statement → Statement  → Statement 
--    ¬_         : Statement  → Statement 
--    All_=>_        : Var → Statement → Statement 
--    Exist_=>_      : Var → Statement → Statement 

-- make negations on predicates only
negin1  : Statement → Statement

negin  : Statement → Statement
negin (pred x) = pred x
negin (predx x x₁) = predx x x₁
negin (s ∧ s₁) = negin s ∧ negin s₁
negin (s ∨ s₁) = negin s ∨ negin s₁
negin (¬ s) = negin1 s
negin (All x => s) = All x => negin s
negin (Exist x => s) = Exist x => negin s

negin1 (pred x) = ¬ (pred x)
negin1 (predx x x₁) = ¬ (predx x x₁)
negin1 (s ∧ s₁) = negin1 s ∨ negin1 s₁
negin1 (s ∨ s₁) = negin1 s ∧ negin1 s₁
negin1 (¬ s) = negin s
negin1 (All x => s) = (Exist x => negin1 s )
negin1 (Exist x => s) = (All x => negin1 s)

-- remove existential quantifiers using sokem functions
--    enough unused functions and constants for skolemization necessary
--    assuming non overrupping quantified variables

{-# TERMINATING #-} 
skolem  : List Const → List Func → (sbst : Expr  → Var →  Expr  → Expr  ) → Statement → Statement
skolem cl fl sbst s = skolemv1 ( λ s cl fl vr → s ) s cl fl []  where
   --   Expr indepenent variable substituion using Expr substution (sbst)
   _[_/_] :  (e : Statement  ) → Var → Expr → Statement
   (pred x) [ xv / v ]     = pred x
   (predx x x₁) [ xv / v ] = predx x ( sbst x₁ xv v )
   (e ∧ e₁) [ xv / v ]     = (  e [ xv / v ]) ∧ (  e₁ [ xv / v ])
   (e ∨ e₁) [ xv / v ]     = (  e [ xv / v ]) ∨ (  e₁ [ xv / v ])
   (¬ e) [ xv / v ]        = ¬ (  e [ xv / v ])
   (All x => e) [ xv / v ]   = All x =>   (  e [ xv / v ])
   (Exist x => e) [ xv / v ] = Exist x => (  e [ xv / v ])

   skolemv1 : (Statement → List Const → List Func → List Var → Statement )
             → Statement → List Const → List Func → List Var → Statement
   skolemv1 next (All x => s )   cl fl vl              = skolemv1 next s cl fl ( x ∷ vl) 
   -- all existential quantifiers are replaced by constants or funcions
   skolemv1 next (Exist x => s ) [] fl []              = skolemv1 next s [] fl [] 
   skolemv1 next (Exist x => s ) (sk ∷ cl ) fl []      = skolemv1 next (s [ x / (Expr.const sk) ] ) cl fl [] 
   skolemv1 next (Exist x => s ) cl [] (v ∷ t)         = skolemv1 next s cl [] (v ∷ t)
   skolemv1 next (Exist x => s ) cl (sk ∷ fl) (v ∷ t)  = skolemv1 next (s [ x / (func sk (mkarg v t) ) ] ) cl fl (v ∷ t)  where
      mkarg : (v : Var) (vl : List Var ) → Expr
      mkarg v []  = var v
      mkarg v (v1 ∷ t )  = var v , mkarg v1 t
   skolemv1 next (s ∧ s₁)                             = skolemv1 ( λ s → skolemv1 (λ s₁ → next (s ∧ s₁) ) s₁ ) s 
   skolemv1 next (s ∨ s₁)                             = skolemv1 ( λ s → skolemv1 (λ s₁ → next (s ∨ s₁) ) s₁ ) s 
   skolemv1 next                                       = next 

-- remove universal quantifiers (assuming all variables are different)
univout  : Statement → Statement
univout (s ∧ s₁) = univout s ∧ univout s₁
univout (s ∨ s₁) = univout s ∨ univout s₁
univout (All x => s ) = s
univout x = x

-- move disjunctions inside
{-# TERMINATING #-} 
conjn1  : Statement → Statement

{-# TERMINATING #-} 
conjn  : Statement → Statement
conjn (s ∧ s₁) = conjn s ∧ conjn s₁
conjn (s ∨ s₁) = conjn1 ( ( conjn s ) ∨ ( conjn s₁) )
conjn x = x

conjn1 ((x ∧ y) ∨ z) = conjn (x ∨ y) ∧ conjn (x ∨ z )
conjn1 (z ∨ (x ∧ y)) = conjn (z ∨ x) ∧ conjn (z ∨ y )
conjn1 x = x

data Clause  : Set where
   _:-_ : ( x y : List Statement ) → Clause

-- turn into [ [  [ positive ] :- [ negative ] ]
--   to remove overraps, we need equality
clausify : Statement → List Clause
clausify s = clausify1 s [] where
   inclause : Statement → Clause → Clause
   inclause (x ∨ y ) a  = inclause x ( inclause y a ) 
   inclause (¬ x) (a :- b )  = a :- ( x ∷ b ) 
   inclause  x (a :- b)   = ( x ∷ a ) :- b  
   clausify1 : Statement → List Clause → List Clause
   clausify1 (x ∧ y) c =  clausify1 y (clausify1 x c )
   clausify1 x c = inclause x ([] :- [] ) ∷ c

translate : Statement → List Const → List Func  →  (sbst : Expr  → Var →  Expr  → Expr  ) →  List Clause
translate s cl fl sbst = clausify $ conjn $ univout $ skolem cl fl sbst $ negin s



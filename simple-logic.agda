module simple-logic where
open import Data.Bool hiding  ( _∨_ ; _∧_ )

data Var : Set where
   X : Var
   Y : Var
   Z : Var

data Expr : Set where
   var : Var → Expr
   a : Expr
   b : Expr
   c : Expr
   f : Expr → Expr
   g : Expr → Expr
   h : Expr → Expr
   _,_ : Expr → Expr → Expr

data Statement : Set where
   p : Expr → Statement
   q : Statement
   r : Statement
   _∧_    :  Statement → Statement → Statement
   _∨_    :  Statement → Statement → Statement
   ¬       :  Statement → Statement 
   all_=>_ :  Var → Statement → Statement
   ∃_=>_   :  Var → Statement → Statement

test2 : Statement
test2 = ¬ ( q ∧ ( all X => p ( f ( var X  ))))

subst-expr : Expr → Var → (value : Expr ) → Expr
subst-expr (var X ) X v = v 
subst-expr (var Y ) Y v = v 
subst-expr (var Z ) Z v = v 
subst-expr (f x ) n v = f (subst-expr x n v) 
subst-expr (x , y ) n v = (subst-expr x n v) , (subst-expr y n v) 
subst-expr x  n v = x 

_[_/_]  : (orig : Statement ) → Var → (value : Expr ) → Statement
(p x ) [ n / v ] = p ( subst-expr x n v )
q [ n / v ] = q
r [ n / v ] = r
(x ∧ y) [ n / v ] = (x [ n / v ] ) ∧  (x [ n / v ])
(x ∨ y) [ n / v ] = (x [ n / v ] ) ∨  (x [ n / v ])
(¬ x) [ n / v ] = ¬ (x [ n / v ] )
(all x => y) [ n / v ] = all x => (y [ n / v ])    -- we should protect variable x from replacement
(∃ x => y) [ n / v ] =  ∃ x =>    (y [ n / v ])

{-# TERMINATING #-} 
M0 : Statement → Bool
M0 q = true
M0 r = false
M0 (p  a ) = true
M0 (x ∧ y) = M0 x Data.Bool.∧ M0 y
M0 (x ∨ y) = M0 x Data.Bool.∨ M0 y
M0 (¬ x) = not (M0 x)
-- we only try simple constant, it may contains arbitrary complex functional value
M0 (all x => y) = M0 ( y [ x / a ] ) Data.Bool.∧ M0 ( y [ x / b ] ) Data.Bool.∧ M0 (  y [ x / c ] ) 
M0 (∃ x => y)   = M0 ( y [ x / a ] ) Data.Bool.∨ M0 ( y [ x / b ] ) Data.Bool.∨ M0 (  y [ x / c ] ) 
M0 _ = false

test3 : Bool 
test3 = M0 ( ∃ X => p ( var X ))


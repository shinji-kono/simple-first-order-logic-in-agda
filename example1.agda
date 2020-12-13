module example1 where
open import Data.List hiding (all ; and ; or )
open import Data.Maybe 
open import Data.Bool hiding ( not ; _∧_ ; _∨_ )

data Const : Set where
      a : Const
      b : Const
      c : Const

data Var : Set where
      X : Var
      Y : Var
      Z : Var

data Func : Set where
      f : Func
      g : Func
      h : Func

data Pred : Set where
      p : Pred
      q : Pred
      r : Pred

open import Logic Const Func Var Pred 

ex1 : Statement
ex1 = ¬ ( pred q  ∧ ( All X =>  predx p ( func f (var X) ) ))

subst-expr :  Expr  → Var → Expr → Expr 
subst-expr  (var X) X v = v
subst-expr  (var Y) Y v = v
subst-expr  (var Z) Z v = v
subst-expr  (func f₁ e) xv v = func f₁ ( subst-expr e xv v ) 
subst-expr  (e , e1) xv v = ( subst-expr e xv v ) , ( subst-expr e1 xv v )
subst-expr  x _ v = x

amap : (px :  Pred ) → Bool 
amap q = true
amap px = false
pmap : (px :  Pred ) → Expr → Bool 
pmap p (const c) = true
pmap p (func d (const a) , const b ) = true
pmap px _ = false

-- we only try simple constant, it may contains arbitrary complex functional value
all0   :  List Expr
all0 =  const a ∷ const b ∷ const c ∷ []

test3 : Bool 
test3 = M amap pmap all0 subst-expr ( Exist X => predx p (var X)  )

open import clausal Const Func Var Pred 

test4 : List Clause
test4 = translate ( Exist X => predx p (var X) ) (c ∷ []) (h ∷ []) subst-expr


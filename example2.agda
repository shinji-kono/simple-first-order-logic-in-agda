module example2 where
open import Data.List hiding (all ; and ; or )
open import Data.Maybe 
open import Data.Bool hiding ( not ; _∧_ ; _∨_ )

data Const : Set where
      anakin : Const
      luke : Const
      leia : Const

data Var : Set where
      X : Var
      Y : Var
      Z : Var

data Func : Set where

data Pred : Set where
      father : Pred
      brother : Pred

open import Logic Const Func Var Pred 

_⇒_ : Statement → Statement → Statement 
x ⇒ y = ( ¬ x ) ∨ y

ex1 : Statement
ex1 = All X => All Y => (( Exist Z => ( ( predx father ( var X , var Z ) ∧  predx father (var Y , var Z ) ))) ⇒ predx brother ( var X , var Y) )

subst-expr :  Expr  → Var → Expr → Expr 
subst-expr  (var X) X v = v
subst-expr  (var Y) Y v = v
subst-expr  (var Z) Z v = v
subst-expr  (func f₁ e) xv v = func f₁ ( subst-expr e xv v ) 
subst-expr  (e , e1) xv v = ( subst-expr e xv v ) , ( subst-expr e1 xv v )
subst-expr  x _ v = x

amap : (px :  Pred ) → Bool 
amap px = false
pmap : (px :  Pred ) → Expr → Bool 
pmap father ( const leia , const anakin ) = true
pmap father ( const luke , const anakin ) = true
pmap brother ( const leia , const luke) = true
pmap brother ( const luke , const leia) = true
pmap brother ( const luke , const luke) = true  -- strange but our definition of brother requires this
pmap brother ( const leia , const leia) = true
pmap px _ = false

-- we only try simple constant, it may contains arbitrary complex functional value
all0   :  List Expr
all0 =  const anakin ∷ const luke ∷ const leia ∷ []

--
-- pmap is a model of axiom ex1
--
test9 : Bool 
test9 = M amap pmap all0 subst-expr ex1 

test3 : Bool 
test3 = M amap pmap all0 subst-expr (
     (  predx father ( const leia , const anakin ) ∧ predx father ( const luke , const anakin ) ) ⇒ predx brother ( const leia , const luke) )

--
-- Valid Proposition is true on any interpretation
--
pmap1 : (px :  Pred ) → Expr → Bool 
pmap1 father ( const leia , const anakin ) = true
pmap1 father ( const luke , const anakin ) = true
pmap1 brother ( const leia , const luke) = false
pmap1 px _ = false

test6 : Bool 
test6 = M amap pmap1 all0 subst-expr (
     ( ex1 ∧ ( predx father ( const leia , const anakin ) ∧ predx father ( const luke , const anakin ) )) ⇒ predx brother ( const leia , const luke) )

--
-- pmap1 is not a model of axiom ex1
--

test4 : Bool 
test4 = M amap pmap1 all0 subst-expr ex1 

test5 : Bool 
test5 = M amap pmap1 all0 subst-expr (   All X => All Y => ( predx father ( var X , const anakin ) ∧  predx father (var Y , const anakin ) ))

open import clausal Const Func Var Pred 

test7 : List Clause
test7 = translate ex1 [] [] subst-expr  

-- brother (X , Y) :- father (X , Z) , father (Y , Z)


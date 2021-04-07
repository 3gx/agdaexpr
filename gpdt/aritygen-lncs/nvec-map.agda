{- Generic Programming with Dependent Types -}
{- Stephanie Weirich and Chris Casinghino   -}
{-# OPTIONS --type-in-type #-}

-- N-ary MAP just for vectors
module nvec-map where

open import Data.List hiding (zip)
open import Data.Nat
open import Data.Bool
open import Data.Vec hiding (_⊛_)

repeat : {n : ℕ} → {A : Set} → A → Vec A n
repeat {zero}   x = []
repeat {suc n}  x = x ∷ repeat {n} x

_⊛_  : {A B : Set} {n : ℕ} → Vec (A → B) n → Vec A n → Vec B n
[]        ⊛ []        = [] 
(a ∷ As)  ⊛ (b ∷ Bs)  = a b ∷ As ⊛ Bs

infixl 40 _⊛_

map0          : {m : ℕ} {A : Set} → A → Vec A m
map0          = repeat


map1          : {m : ℕ} {A B : Set}
              → (A → B) → Vec A m → Vec B m
map1 f x      = repeat f ⊛ x

map2          : {m : ℕ} {A B C : Set} 
              → (A → B → C) → Vec A m → Vec B m → Vec C m
map2 f x1 x2  = repeat f ⊛ x1 ⊛ x2
arrTy : {n : ℕ} → Vec Set (suc n) → Set
arrTy {0}      (A ∷ [])  = A
arrTy {suc n}  (A ∷ As)  = A → arrTy As

arrTyVec  : {n : ℕ} → ℕ → Vec Set (suc n) → Set
arrTyVec m As = arrTy (repeat (\ A → Vec A m) ⊛ As )

nvec-map  : {m : ℕ} (n : ℕ) → {As : Vec Set (suc n)} 
          → arrTy As → arrTyVec m As

nvec-map n f = g n (repeat f) where
  g  : {m : ℕ} → (n : ℕ) → {As : Vec Set (suc n)}
     → Vec (arrTy As) m → arrTyVec m As
  g  0        {A ∷ []}  a  = a
  g  (suc n)  {A ∷ As}  f  = (\ a → g n (f ⊛ a))

∀⇒ : {n : ℕ} → (( _ : Vec Set n) → Set) → Set
∀⇒ {zero}   B = B [] 
∀⇒ {suc n}  B = {a : Set} → ∀⇒ (\  as  → B ( a ∷ as ))

λ⇒  : {n : ℕ} → {B : (_ : Vec Set n) → Set}
    → ({ X : Vec Set n} → B X) → (∀⇒ B)
λ⇒ {zero}    f = f  {[]}
λ⇒ {suc n}   f = \ {a : Set} → λ⇒ {n} (\ {as}  → f { a ∷ as }) 

nmap  :  {m : ℕ} → (n : ℕ)
      → ∀⇒ (\(As : Vec Set (suc n)) → arrTy As → arrTyVec m As )
nmap {m} n =  λ⇒ (\{As} → nvec-map {m} n {As})


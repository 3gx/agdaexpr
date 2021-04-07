{- Generic Programming with Dependent Types -}
{- Stephanie Weirich and Chris Casinghino   -}

{-# OPTIONS --type-in-type #-}
module ngeq where

open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Vec hiding (_⊛_)

open import aritygen

pair-eq3  : {A1 B1 C1 A2 B2 C2 : Set} 
          → (A1 → B1 → C1 → Bool) → (A2 → B2 → C2 → Bool) 
          → (A1 × A2) → (B1 × B2) → (C1 × C2) → Bool
pair-eq3 f g (a1 , a2) (b1 , b2) (c1 , c2) = f a1 b1 c1 ∧ g a2 b2 c2

sum-eq3   : {A1 B1 C1 A2 B2 C2 : Set} 
          → (A1 → B1 → C1 → Bool) → (A2 → B2 → C2 → Bool) 
          → (A1 ⊎ A2) → (B1 ⊎ B2) → (C1 ⊎ C2) → Bool
sum-eq3 f g  (inj₁ a1)  (inj₁ b1)  (inj₁ c1)  = f a1 b1 c1
sum-eq3 f g  (inj₂ a2)  (inj₂ b2)  (inj₂ c2)  = g a2 b2 c2
sum-eq3 f g  _         _          _         = false

NGeq : {n : ℕ} → (v : Vec Set n) → Set
NGeq {zero}   []         = Bool
NGeq {suc n}  (A1 ∷ As)  = A1 → NGeq As

defUnit : (n : ℕ) → NGeq (repeat ⊤)
defUnit zero     = \ x → true
defUnit (suc n)  = \ x → defUnit n

defPair : (n : ℕ) → 
        {as : Vec Set (suc n)} → (NGeq as) →
        {bs : Vec Set (suc n)} → (NGeq bs) → 
        NGeq ((repeat _×_ ⊛ as) ⊛ bs)
defPair zero     {a ∷ []}        at  {b ∷ []}        bt = 
  \ x → at (proj₁ x) ∧ bt (proj₂ x)
defPair (suc n)  {a1 ∷ a2 ∷ as}  af  {b1 ∷ b2 ∷ bs}  bf =
  \ x → (defPair n  {a2 ∷ as} (af (proj₁ x))
                    {b2 ∷ bs} (bf (proj₂ x)))

-- the n-ary constant false function
constFalse : {n : ℕ} → (v : Vec Set n) → NGeq v
constFalse {zero}  []   = false
constFalse {suc m} (A1 ∷ As)  = \ a → constFalse As

defSumFirst : (n : ℕ) → 
        {as : Vec Set (suc n)} → (NGeq as) →
        {bs : Vec Set (suc n)} → 
        NGeq (repeat _⊎_ ⊛ as ⊛ bs)
defSumFirst zero    {a ∷ []} at {b ∷ []}   = f
  where f : a ⊎ b → Bool
        f (inj₁ x1) = at x1
        f (inj₂ x1) = false
defSumFirst (suc n) {a1 ∷ a2 ∷ as} af {b1 ∷ b2 ∷ bs} = f 
  where f : a1 ⊎ b1 → NGeq (repeat _⊎_ ⊛ (a2 ∷ as) ⊛ (b2 ∷ bs))
        f (inj₁ x1) = defSumFirst n (af x1) 
        f (inj₂ x1) = constFalse (repeat _⊎_ ⊛ (a2 ∷ as) ⊛ (b2 ∷ bs))

defSumSecond : (n : ℕ) → 
        {as : Vec Set (suc n)} → 
        {bs : Vec Set (suc n)} → (NGeq bs) →
        NGeq (repeat _⊎_ ⊛ as ⊛ bs)
defSumSecond zero    {a ∷ []} {b ∷ []}  bt  = f
  where f : a ⊎ b → Bool
        f (inj₁ x1) = false
        f (inj₂ x1) = bt x1
defSumSecond (suc n) {a1 ∷ a2 ∷ as}  {b1 ∷ b2 ∷ bs} bf = f 
  where f : a1 ⊎ b1 → NGeq (repeat _⊎_ ⊛ (a2 ∷ as) ⊛ (b2 ∷ bs))
        f (inj₁ x1) = constFalse (repeat _⊎_ ⊛ (a2 ∷ as) ⊛ (b2 ∷ bs))
        f (inj₂ x1) = defSumSecond n (bf x1)

defSum : (n : ℕ) → 
        {as : Vec Set (suc n)} → (NGeq as) →
        {bs : Vec Set (suc n)} → (NGeq bs) → 
        NGeq (repeat _⊎_ ⊛ as ⊛ bs)
defSum zero {a ∷ []} at {b ∷ []} bt = f 
  where f : a ⊎ b → Bool
        f (inj₁ x1) = at x1
        f (inj₂ x1) = bt x1
defSum (suc n)  {a1 ∷ a2 ∷ as} af {b1 ∷ b2 ∷ bs} bf = f
  where f : a1 ⊎ b1 → NGeq (repeat _⊎_ ⊛ (a2 ∷ as) ⊛ (b2 ∷ bs))
        f (inj₁ x1) = defSumFirst n (af x1) 
        f (inj₂ x1) = defSumSecond n (bf x1)

ngeq-const : {n : ℕ} → ConstEnv {n} NGeq
ngeq-const {n} Unit = defUnit n
ngeq-const {n} Prod = defPair n
ngeq-const {n} Sum  = defSum n

ngeq-mu : ∀ {n} → MuGen n NGeq
ngeq-mu   {zero}   {A ∷ []}        =  \ g x -> g (unroll x) 
ngeq-mu   {suc n}  {A1 ∷ A2 ∷ As}  =  \ g x -> ngeq-mu (g (unroll x))
ngeq  : (n : ℕ) → {k : Kind} → (e : Ty k)
      → NGeq ⟨ k ⟩ (repeat ⌊ e ⌋)
ngeq n e = ngen e ngeq-const  (\ {As} -> ngeq-mu {n} {As})

pair-eq1 : {A1 B1 A2 B2 : Set} 
         → (A1 → B1 → Bool) → (A2 → B2 → Bool)
         → (A1 × A2) → (B1 × B2) → Bool
pair-eq1 eq1 eq2 = ngeq 1 (Con Prod) eq1 eq2


{- Generic Programming with Dependent Types -}
{- Stephanie Weirich and Chris Casinghino   -}
{-# OPTIONS --type-in-type #-}

-- Doubly generic version of unzipWith
module ngsplit where

open import Data.Nat 
open import Data.Bool
open import Data.Maybe hiding (maybe)
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Vec hiding (_⊛_)

open import aritygen

Option : Set → Set
Option = \ A → ⊤ ⊎ A

option : Ty (⋆ ⇒ ⋆) 
option = Lam (App (App (Con Sum) (Con Unit)) (Var VZ))

prodTy : {n : ℕ} → (As : Vec Set n) → Set
prodTy {0}            _         = ⊤
prodTy {1}            (A ∷ [])  = A
prodTy {suc (suc _)}  (A ∷ As)  = (A × prodTy As)

NGsplit : {n : ℕ} → (v : Vec Set (suc n)) → Set
NGsplit (A1 ∷ As) = A1 → prodTy As

duplicate  : {t : Set} → (n : ℕ) → t 
           → prodTy {n} (repeat t)
duplicate 0        _ = tt
duplicate 1        x = x 
duplicate (suc (suc n))  x = (x , duplicate (suc n) x) 

defUnit : (n : ℕ) → NGsplit {n} (repeat ⊤)
defUnit n = \ x → duplicate n x

prodn  : {n : ℕ} → (As Bs : Vec Set n)
       → prodTy As → prodTy Bs 
       → prodTy (repeat _×_ ⊛ As ⊛ Bs)
prodn {0}            _         _         a         b         = tt
prodn {1}            (A ∷ [])  (B ∷ [])  a         b         = (a , b)
prodn {suc (suc n)}  (A ∷ As)  (B ∷ Bs)  (a , as)  (b , bs)  =
  ( (a , b) , prodn {suc n} _ _ as bs )     

defPair  : (n : ℕ) 
         → {As : Vec Set (suc n)} → (NGsplit As) 
         → {Bs : Vec Set (suc n)} → (NGsplit Bs) 
         → NGsplit (repeat _×_ ⊛ As ⊛ Bs)
defPair n {A ∷ As} a {B ∷ Bs} b =
  \ p → prodn {n} _ _ (a (proj₁ p)) (b (proj₂ p)) 

injFirst  : {n : ℕ} {As Bs : Vec Set n} 
         → prodTy As
         → prodTy (repeat _⊎_ ⊛ As ⊛ Bs)
injFirst {0}      {[]}      {[]}      tt        = tt
injFirst {1}      {A ∷ []}  {B ∷ []}  a         = inj₁ a
injFirst {suc (suc n)}  {A ∷ As}  {B ∷ Bs}  (a , as)  = 
  ( inj₁ a , injFirst {suc n} as )

injSecond  : {n : ℕ} {As Bs : Vec Set n} 
          → prodTy Bs
          → prodTy (repeat _⊎_ ⊛ As ⊛ Bs)
injSecond {0}      {[]}      {[]}      tt        = tt
injSecond {1}      {A ∷ []}  {B ∷ []}  b         = inj₂ b
injSecond {suc (suc n)}  {A ∷ As}  {B ∷ Bs}  (b , bs)  = 
  ( inj₂ b , injSecond {suc n} bs )

defSum  : (n : ℕ) 
        → {As : Vec Set (suc n)} → (NGsplit As)
        → {Bs : Vec Set (suc n)} → (NGsplit Bs)
        → NGsplit (repeat _⊎_ ⊛ As ⊛ Bs)
defSum n  {A ∷ As}  af  {B ∷ Bs}  bf = f
  where  f : A ⊎ B → prodTy (repeat _⊎_ ⊛ As ⊛ Bs)
         f (inj₁ x1)  = injFirst  {n} (af x1) 
         f (inj₂ x1)  = injSecond {n} (bf x1)

split-const : {n : ℕ} → ConstEnv {n} NGsplit
split-const {n} Unit = defUnit n
split-const Prod = defPair _
split-const Sum  = defSum _

-- roll all of the components of a product
roll-all : ∀ {n : ℕ}{As : Vec (Set -> Set) n} -> 
  prodTy (As ⊛ (repeat μ ⊛ As)) ->
  prodTy (repeat μ ⊛ As) 
roll-all {0}{[]} tt = tt
roll-all {1}{A ∷ []}  x = roll x
roll-all {suc (suc n)}{A1 ∷ A2 ∷ As} (x , xs) = (roll x , roll-all {suc n} xs)

split-mu : { n : ℕ} -> MuGen n NGsplit
split-mu {0}            { A ∷ [] }        = \ g → \ x → g (unroll x)
split-mu {1}            { A1 ∷ A2 ∷ [] }  = \ g → \ x → roll (g (unroll x))
split-mu {suc (suc n)}  { A1 ∷ A2 ∷ As }  =
   \ g → \ x → roll-all {suc (suc n)}{A2 ∷ As} (g (unroll x))

ngsplit  : (n : ℕ) → {k : Kind} → (e : Ty k)
         → NGsplit {n} ⟨ k ⟩ (repeat ⌊ e ⌋)
ngsplit n e = ngen e split-const split-mu

unzipWithOption3 : { A B C : Set } → (A → B × C) → 
  ( Option A → Option B × Option C )
unzipWithOption3 = ngsplit 2 option { _ ∷ _ ∷ _ ∷ [] }

unzipWithOption4 : { A B C D : Set } → (A → B × C × D) → 
  ( Option A → Option B × Option C × Option D)
unzipWithOption4 = ngsplit 3 option { _ ∷ _ ∷ _ ∷ _ ∷ [] }

unzipOption2 : { A B : Set } → Option (A × B) →
   (Option A × Option B)
unzipOption2 = unzipWithOption3 (\ x → x)

unzipOption3 : { A B C : Set } → Option (A × B × C) →
   (Option A × Option B × Option C)
unzipOption3 = unzipWithOption4 (\ x → x)

-- The following code shows how complicated it is to define split
-- directly for vectors.

-- Given a vector of types, create a product 
-- where every element of the product is an empty 
-- vector of the corresponding type in the array.
Array : ℕ → Set → Set
Array n A = Vec A n


prodNil  : {n : ℕ} → (As : Vec Set n) 
         → prodTy (repeat (Array 0) ⊛ As)
prodNil {0}            []        = tt
prodNil {1}            (A ∷ [])  = []
prodNil {suc (suc n)}  (A ∷ As)  = ( [] , prodNil As )

prodPair  : {n m : ℕ} → (As : Vec Set n)
          → prodTy As 
          → prodTy (repeat (Array m) ⊛ As) 
          → prodTy (repeat (Array (suc m)) ⊛ As)
prodPair {0}            []        x1       v        = tt
prodPair {1}            (A ∷ [])  x1       v        = x1 ∷ v
prodPair {suc (suc n)}  (A ∷ As) (x , xs)  (v , vs) =
     x ∷ v , prodPair As xs vs

-- turn an array of products into a product of arrays by 
-- folding prodNil and prodPair on the vector.
transposeP   : {m : ℕ}{n : ℕ} → (As : Vec Set n)
            → Array m (prodTy As) 
            → prodTy (repeat (Array m) ⊛ As)
transposeP {zero}  As []        = prodNil As
transposeP {suc m} As (x ∷ xs)  = prodPair As  x (transposeP As xs)

defArrayAux : {m : ℕ} (n : ℕ) 
  → (As : Vec Set (suc n)) → (NGsplit As) 
  → NGsplit (repeat (Array m) ⊛ As)
defArrayAux n (A ∷ As) fa = \ x → transposeP As (map fa x)
   

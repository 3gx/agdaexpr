{- Generic Programming with Dependent Types -}
{- Stephanie Weirich and Chris Casinghino   -}
{-# OPTIONS --type-in-type --no-termination-check #-}
module nmap where
open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Nat 
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Data.Vec hiding (_⊛_)
open import Data.Bool
open import Data.Maybe

open import aritygen

-- A few definitions that were elided from the text
error : ∀ {A} -> A
error = error

eq-nat : ℕ -> ℕ -> Bool
eq-nat zero     zero     = true
eq-nat (suc n)  (suc m)  = eq-nat n m 
eq-nat _        _        = false

_⟨_⟩₂ : (Set → Set → Set) → (k : Kind) → ⟦ k ⟧ → ⟦ k ⟧ → Set 
b ⟨ ⋆ ⟩₂         = \ t₁ t₂ → b t₁ t₂
b ⟨ k₁ ⇒ k₂ ⟩₂  = \ t₁ t₂ → ∀ { a₁ a₂ } 
                → (b ⟨ k₁ ⟩₂) a₁ a₂ → (b ⟨ k₂ ⟩₂) (t₁ a₁) (t₂ a₂)

Repeat : Vec Set 1 → Set
Repeat ( A ∷ [] ) = A 

grepeat : {k : Kind} → (t : Ty k) → Repeat ⟨ k ⟩ (⌊ t ⌋ ∷ [])
grepeat t = ngen t grepeat-c (\ {As} → grepeat-mu {As}) where
  grepeat-c : ConstEnv Repeat
  grepeat-c Unit = tt
  grepeat-c Sum  = \{A} → grepeat-sum {A} where
    grepeat-sum : Repeat ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ (_⊎_ ∷ [])
    grepeat-sum {A ∷ []} ra {B ∷ []} rb = inj₂ rb
  grepeat-c Prod = \{A} → grepeat-prod {A} where 
    grepeat-prod : Repeat ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ (_×_ ∷ [])
    grepeat-prod {A ∷ []} ra {B ∷ []} rb = (ra , rb)
  
  grepeat-mu : ∀ {As} →  Repeat (As ⊛ ((μ ∷ []) ⊛ As)) → Repeat ((μ ∷ []) ⊛ As)
  grepeat-mu {A ∷ []} = roll

repeat-list : ∀ {A} → A → MyList A
repeat-list = grepeat list {_ ∷ []} 
Map : Vec Set 2 → Set 
Map ( A ∷ B ∷ [] ) = A → B

map-sum : Map ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ (_⊎_ ∷ _⊎_ ∷ [])
map-sum { A1 ∷ B1 ∷ []} ra { A2 ∷ B2 ∷ []} rb = g where
   g : (A1 ⊎ A2) → B1 ⊎ B2
   g (inj₁ x) = inj₁ (ra x)
   g (inj₂ x) = inj₂ (rb x)

map-prod : Map ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ (_×_ ∷ _×_ ∷ [])
map-prod { A1 ∷ B1 ∷ []} ra { A2 ∷ B2 ∷ []} rb = g where
   g : (A1 × A2) → B1 × B2
   g (x , y) = (ra x , rb y)

gmap-mu : ∀ {As} → Map (As ⊛ ((μ ∷ μ ∷ []) ⊛ As)) → Map ((μ ∷ μ ∷ []) ⊛ As)
gmap-mu {_ ∷ _ ∷ []} = \ x y → roll (x (unroll y))

gmap : ∀ {k : Kind} → (t : Ty k) → Map ⟨ k ⟩ (⌊ t ⌋ ∷ ⌊ t ⌋ ∷ [])
gmap t = ngen t gmap-c gmap-mu where
  gmap-c : ConstEnv Map
  gmap-c Unit = \ x → x
  gmap-c Sum  = map-sum
  gmap-c Prod = map-prod
  
ZW : Vec Set 3 → Set 
ZW ( A ∷ B ∷ C ∷ [] ) = A → B → C

zip-sum : ZW ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ (_⊎_ ∷ _⊎_ ∷ _⊎_ ∷ [])
zip-sum {A1 ∷ A2 ∷ A3 ∷ []} ra {B1 ∷ B2 ∷ B3 ∷ []} rb = g where
  g : (A1 ⊎ B1) → (A2 ⊎ B2) → A3 ⊎ B3
  g (inj₁ x)(inj₁ y)  = inj₁ (ra x y)
  g (inj₂ x)(inj₂ y)  = inj₂ (rb x y) 
  g  _ _              = error

zip-prod : ZW ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ (_×_ ∷ _×_ ∷ _×_ ∷ [])
zip-prod { A1 ∷ A2 ∷ A3 ∷ []} ra { B1 ∷ B2 ∷ B3 ∷ []} rb = g where
  g : (A1 × B1) → (A2 × B2) → A3 × B3
  g (x , y) ( w , z ) = (ra x w , rb y z)

gzipWith : ∀ {k} → (t : Ty k) → ZW ⟨ k ⟩ (⌊ t ⌋ ∷ ⌊ t ⌋ ∷ ⌊ t ⌋ ∷ [])
gzipWith t = ngen t gzip-c gzip-mu where
  gzip-c : ConstEnv ZW
  gzip-c Unit = \ x y → x
  gzip-c Sum  = zip-sum
  gzip-c Prod = zip-prod

  gzip-mu : ∀ {As} → ZW (As ⊛ ((μ ∷ μ ∷ μ ∷ [])  ⊛ As)) 
      → ZW ((μ ∷ μ ∷ μ ∷ []) ⊛ As)
  gzip-mu {_ ∷ _ ∷ _ ∷ []} = \ x y z → roll (x (unroll y) (unroll z))

NGmap : {n : ℕ} → Vec Set (suc n) → Set
NGmap (A ∷ [])      = A
NGmap (A ∷ B ∷ As)  = A → NGmap (B ∷ As)

defUnit : (n : ℕ) → NGmap {n} ⟨ ⋆ ⟩ (repeat ⊤)
defUnit zero     = tt
defUnit (suc n)  = \ x → (defUnit n)

defPair  : (n : ℕ) 
         → {As : Vec Set (suc n)} → NGmap As
         → {Bs : Vec Set (suc n)} → NGmap Bs 
         → NGmap (repeat _×_ ⊛ As ⊛ Bs)
defPair  zero     {A ∷ []}        a  {B ∷ []}        b  = (a , b)
defPair  (suc n)  {A1 ∷ A2 ∷ As}  a  {B1 ∷ B2 ∷ Bs}  b  =
         \ p → defPair n  {A2 ∷ As} (a (proj₁ p)) {B2 ∷ Bs} (b (proj₂ p))

defSum : (n : ℕ) 
         → {As : Vec Set (suc n)} → NGmap As
         → {Bs : Vec Set (suc n)} → NGmap Bs
         → NGmap (repeat _⊎_ ⊛ As ⊛ Bs)

defSum zero     {A ∷ []}          a {B ∷ []}          b  = (inj₂ b) 
defSum (suc 0)  {A1 ∷ (A2 ∷ [])}  a {B1 ∷ (B2 ∷ [])}  b  = f
  where
    f : A1 ⊎ B1 → A2 ⊎ B2
    f (inj₁ a1)  = inj₁ (a a1)
    f (inj₂ b1)  = inj₂ (b b1)
defSum (suc n)  {A1 ∷ (A2 ∷ As)}  a {B1 ∷ (B2 ∷ Bs)}       b  = f
  where 
    f : A1 ⊎ B1 → NGmap (repeat _⊎_ ⊛ (A2 ∷ As) ⊛ (B2 ∷ Bs))
    f (inj₁ a1)  = defSum n {A2 ∷ As} (a a1)     {B2 ∷ Bs} (b error)
    f (inj₂ b1)  = defSum n {A2 ∷ As} (a error)  {B2 ∷ Bs} (b b1)
ngmap-const : {n : ℕ} → ConstEnv {n} NGmap
ngmap-const {n} Unit  = defUnit n
ngmap-const {n} Prod  = \{As} → defPair n {As}
ngmap-const {n} Sum   = \{As} → defSum n {As}

ngmap-mu : ∀ {n} → MuGen n NGmap
ngmap-mu {zero}   {A ∷ []}        = roll
ngmap-mu {suc n}  {A1 ∷ A2 ∷ As}  = \ f x → 
  ngmap-mu {n}{A2 ∷ As} (f (unroll x))
ngmap  : (n : ℕ) → {k : Kind} → (e : Ty k) 
       → NGmap {n} ⟨ k ⟩ (repeat ⌊ e ⌋)
ngmap n e = ngen e  ngmap-const (\ {As} → ngmap-mu {n} {As})
 
repeat-ml    : ∀ {B} → B → MyList B
repeat-ml    = ngmap 0 list {_ ∷ []} 

map-ml       : ∀ {A₁ B} → (A₁ → B) → MyList A₁ → MyList B 
map-ml       = ngmap 1 list {_ ∷ _ ∷ []} 

zipWith-ml   : ∀ {A₁ A₂ B} → (A₁ → A₂ → B)
             → MyList A₁ → MyList A₂ → MyList B
zipWith-ml   = ngmap 2 list {_ ∷ _ ∷ _ ∷ []} 


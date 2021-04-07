{- Generic Programming with Dependent Types -}
{- Stephanie Weirich and Chris Casinghino   -}

{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}
module aritygen where

open import Data.Nat
open import Data.Vec hiding (_∈_; _⊛_)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Relation.Binary.PropositionalEquality

infixr 50 _⇒_
infixl 50 _⊛_

-- quantify
∀⇒ : {n : ℕ} {A : Set} → (Vec A n → Set) → Set
∀⇒ {zero}       B = B []
∀⇒ {suc n} {A}  B = {a : A} → ∀⇒ {n} (\ as → B (a ∷ as))
  
--- curry
\⇒  : {n : ℕ} {A : Set} {B : Vec A n → Set} 
    → ((X : Vec A n) → B X) → (∀⇒ B)
\⇒ {zero}       f = f []
\⇒ {suc n} {A}  f = \ {a : A} → \⇒ {n} (\ as → f (a ∷ as)) 

-- uncurry
/⇒ : (n : ℕ) → {K : Set}{B : Vec K n → Set} 
  → (∀⇒ B) → (A : Vec K n) → B A 
/⇒ (zero) f  []       = f
/⇒ (suc n) f (a ∷ as) = /⇒ n (f {a}) as


--- vector repeat and zap

repeat : {n : ℕ} → {A : Set} → A → Vec A n
repeat {zero}    x = []
repeat {(suc n)} x = x ∷ repeat {n} x

_⊛_ : {A B : Set} {n : ℕ} → Vec (A → B) n → Vec A n → Vec B n
[] ⊛ [] = [] 
(a ∷ As) ⊛ (b ∷ Bs) = (a b ∷ As ⊛ Bs)

-- explicit recursion
data μ : (Set → Set) → Set where
   roll : ∀{A} → A (μ A) → μ A

unroll : ∀ {A} → μ A → A (μ A)
unroll (roll x) = x


-- boolean
MyBool    = ⊤ ⊎ ⊤
mytrue    : MyBool
mytrue    = inj₁ tt
myfalse   : MyBool
myfalse   = inj₂ tt



-- structural list example
MyList : Set → Set
MyList A = μ (\ B → ⊤ ⊎ (A × B))

nil : ∀ {A} → MyList A
nil = roll (inj₁ tt)

cons : ∀ {A} → A → MyList A → MyList A
cons x xs = roll (inj₂ (x , xs))

-- structural vector example
MyVec      : Set → ℕ → Set
MyVec A 0        = ⊤
MyVec A (suc n)  = A × MyVec A n

vnil       : ∀ {A} → MyVec A 0
vnil       = tt

vcons      : ∀ {n}{A} → A → MyVec A n → MyVec A (suc n)
vcons x xs = (x , xs)


data Kind : Set where 
  ⋆     : Kind 
  _⇒_  : Kind → Kind → Kind

data Const : Kind → Set where
  Unit  : Const ⋆
  Sum   : Const (⋆ ⇒ ⋆ ⇒ ⋆) 
  Prod  : Const (⋆ ⇒ ⋆ ⇒ ⋆)


data Ctx : Set where
  []    : Ctx
  _∷_   : Kind -> Ctx -> Ctx

data V : Ctx → Kind → Set where
  VZ   : ∀ {Γ k} → V (k ∷ Γ) k
  VS   : ∀ {Γ k' k} → V Γ k → V (k' ∷ Γ) k

data Typ : Ctx → Kind → Set where 
  Var  : ∀ {Γ k} → V Γ k → Typ Γ k 
  Lam  : ∀ {Γ k1 k2} → Typ (k1 ∷ Γ) k2 
       → Typ Γ (k1 ⇒ k2)
  App  : ∀ {Γ k1 k2} → Typ Γ (k1 ⇒ k2) → Typ Γ k1
       → Typ Γ k2
  Con  : ∀ {Γ k} → Const k → Typ Γ k
  Mu   : ∀ {Γ} → Typ Γ (⋆ ⇒ ⋆) → Typ Γ ⋆

Ty : Kind → Set
Ty = Typ []

⟦_⟧        : Kind → Set
⟦ ⋆ ⟧       = Set
⟦ a ⇒ b ⟧  = ⟦ a ⟧ → ⟦ b ⟧

C⟦_⟧ : ∀ {k} → Const k → ⟦ k ⟧
C⟦ Unit ⟧     = ⊤    -- has kind |Set|
C⟦ Sum ⟧      = _⊎_  -- has kind |Set → Set → Set|
C⟦ Prod ⟧     = _×_

data Env : Ctx → Set where
  []   : Env [] 
  _∷_  : ∀ {k Γ} → ⟦ k ⟧ → Env Γ → Env (k ∷ Γ)

sLookup : ∀ {k Γ} → V Γ k → Env Γ → ⟦ k ⟧
sLookup VZ      (v ∷ Γ) = v
sLookup (VS x)  (v ∷ Γ) = sLookup x Γ

interp : ∀ {k Γ} → Typ Γ k → Env Γ → ⟦ k ⟧
interp (Var x)      e  = sLookup x e
interp (Lam t)      e  = \ y → interp t (y ∷ e)
interp (App t1 t2)  e  = (interp t1 e) (interp t2 e)
interp (Mu t)       e  = μ (interp t e)
interp (Con c)      e  = C⟦ c ⟧
⌊_⌋ : ∀ {k} → Ty k → ⟦ k ⟧
⌊ t ⌋ = interp t []

-- Mylist code
list : Ty (⋆ ⇒ ⋆) 
list = 
  Lam (Mu (Lam 
      (App (App (Con Sum) (Con Unit)) 
      (App (App (Con Prod) (Var (VS VZ))) (Var VZ)))))

_⟨_⟩_  : {n : ℕ} → (Vec Set (suc n) → Set) → (k : Kind)
      → Vec ⟦ k ⟧ (suc n) → Set
b ⟨ ⋆ ⟩          v   = b v
b ⟨ k1 ⇒ k2 ⟩   v   = { a : Vec ⟦ k1 ⟧ _} →
    b ⟨ k1 ⟩ a → b ⟨ k2 ⟩ (v ⊛ a)

ConstEnv :  {n : ℕ} → (b : Vec Set (suc n) → Set) → Set 
ConstEnv b = 
  {k : Kind} (c : Const k) → b ⟨ k ⟩ repeat ⌊ Con c ⌋


-- an environment of vectors
data NGEnv  {n : ℕ} (b : Vec Set (suc n) → Set) 
            : Ctx → Set where
   NNil   : NGEnv b []
   NCons  : {k : Kind}  {G : Ctx}
          → (a : Vec ⟦ k ⟧ (suc n))
          → b ⟨ k ⟩ a 
          → NGEnv b G 
          → NGEnv b (k ∷ G)

-- interpret a type with a vector of different environments.
interp∗  : ∀ {G k n} → Typ G k → Vec (Env G) n 
    → Vec ⟦ k ⟧ n
interp∗ t vs = repeat (interp t) ⊛ vs

-- "transpose" an environment of vectors to a vector of environments
transpose  :  {n : ℕ} {b : Vec Set (suc n) → Set} 
              {G : Ctx}
           → NGEnv b G → Vec (Env G) (suc n)
transpose NNil            = repeat []
transpose (NCons a _ nge)  = 
  (repeat _∷_) ⊛ a ⊛ (transpose nge)


-- application is congruent
≡-app : ∀ {A}{b : A → Set} { t1 }{ t2 } → t1 ≡ t2 → b t1 -> b t2 
≡-app refl x = x

-- cons is congruent
≡-tail  : ∀ {A} {n} {t1 t2 : Vec A n} {x : A} 
        → t1 ≡ t2 
        → _≡_ {_}{Vec A (suc n)} (x ∷ t1) (x ∷ t2)
≡-tail {A}{n} refl = refl {_} {Vec A (suc n)}

-- kind-indexed types are congruent
≡-KIT  :  {n : ℕ} {b : Vec Set (suc n) → Set} 
          { k : Kind } {t1 t2 : Vec ⟦ k ⟧ (suc n)} 
        → t1 ≡ t2 
        → b ⟨ k ⟩ t1 
        → b ⟨ k ⟩ t2
≡-KIT refl x = x


c1  : {n : ℕ} { k : Kind } {G : Ctx}
    → (a : Vec ⟦ k ⟧ n)
    → (envs : Vec (Env G) n) 
    → a ≡ interp∗ ( Var VZ ) (repeat _∷_ ⊛ a ⊛ envs)
c1 {zero}  []        []          = refl
c1 {suc n} (t ∷ ts)  ( x ∷ xs )  = ≡-tail (c1 {n} ts xs)

c2  : { n : ℕ } { k k' : Kind } {G : Ctx}
    → (x : V G k')
    → (t1 : Vec ⟦ k ⟧ n) 
    → (envs : Vec (Env G) n) 
    →  interp∗ ( Var x ) envs ≡ 
       interp∗ ( Var (VS x) ) (repeat _∷_ ⊛ t1 ⊛ envs)
c2 {zero}  x []       []        = refl
c2 {suc n} x (t ∷ ts) (y ∷ ys)  = ≡-tail (c2 x ts ys)

c3 : {n : ℕ}{k k' : Kind}{G : Ctx}
    → (t : Typ (k' ∷ G) k)
    → (envs : Vec (Env G) n) 
    → (as : Vec ⟦ k' ⟧ n) 
    → (interp∗ ( t ) (repeat _∷_ ⊛ as ⊛ envs))
    ≡ (interp∗ ( Lam t ) envs) ⊛ as
c3 {zero} t [] [] = refl 
c3 {suc n} t (a ∷ as) (b ∷ bs) = ≡-tail (c3 t as bs)

c4 : {n : ℕ}{k1 k2 : Kind} {G : Ctx}
     → (t1 : Typ G (k1 ⇒ k2))
     → (t2 : Typ G k1)
     → (envs : Vec (Env G) n) 
     →    (interp∗ ( t1 ) envs) ⊛ (interp∗ ( t2 ) envs)
      ≡  interp∗ ( App t1 t2 ) envs
c4 {zero}  _  _  []       = refl
c4 {suc n} t1 t2 (a ∷ as) = ≡-tail (c4 t1 t2 as)

c5 : {n : ℕ}{k : Kind}{G : Ctx}
  → (c : Const k)
  → (envs : Vec (Env G) n) 
  → repeat ⌊ Con c ⌋ ≡ interp∗ ( Con c ) envs
c5 {zero}  _ []       = refl
c5 {suc n} c (a ∷ as) = ≡-tail (c5 c as)


c6 : {n : ℕ} {G : Ctx}
     → (t2 : Typ G (⋆ ⇒ ⋆))
     → (envs : Vec (Env G) n) 
     → (interp∗ t2 envs ⊛ (repeat μ  ⊛ (interp∗ t2 envs)))
      ≡  interp∗ (App t2 ( Mu t2 )) envs
c6 {zero}  _  []       = refl
c6 {suc n} t2 (a ∷ as) = ≡-tail (c6 t2 as)


c6' : {n : ℕ} {G : Ctx}
     → (t2 : Typ G (⋆ ⇒ ⋆))
     → (envs : Vec (Env G) n) 
     → (repeat μ  ⊛ (interp∗ t2 envs))
      ≡  interp∗ ( Mu t2 ) envs
c6' {zero}  _  []       = refl
c6'  {suc n} t2 (a ∷ as) = ≡-tail (c6' t2 as)


c7 : { n : ℕ } { A B : Set } { f : A → B } { x : A } →
  (repeat{n} f) ⊛ repeat x ≡ repeat (f x)
c7 {zero} = refl
c7 {suc n} = ≡-tail c7

nLookup  :  {n : ℕ} {b : Vec Set (suc n) → Set}
            {k : Kind} {G : Ctx} 
         → (v : V G k) 
         → (nge : NGEnv b G) 
         → b ⟨ k ⟩ (interp∗ ( Var v ) (transpose nge))
nLookup {n} {b} {k} VZ  (NCons a e nge) = 
    ≡-KIT (c1 a (transpose nge))     e
nLookup (VS x) (NCons a _ nge) = 
    ≡-KIT (c2 x a (transpose nge))   (nLookup x nge)

MuGen : (n : ℕ) → (Vec Set (suc n) → Set) → Set
MuGen n b = ∀ {A} → b (A ⊛ (repeat μ ⊛ A)) → b (repeat μ ⊛ A)

ngen-open : {n : ℕ}{b : Vec Set (suc n) → Set}{G : Ctx} {k : Kind} → 
             (t : Typ G k) → (ve : NGEnv b G) → 
             (ce : ConstEnv b) → MuGen n b →
             b ⟨ k ⟩ ( interp∗ t (transpose ve))
ngen-open (Var x) ve ce d  = nLookup x ve
ngen-open{n}{b} (Lam {k1 = k1} t) ve ce d = 
 \ {a : Vec ⟦ k1 ⟧ (suc n)} (nwt : b ⟨ k1 ⟩ a) → 
  ≡-KIT (c3 t (transpose ve) a) 
  (ngen-open t (NCons a nwt ve) ce d)
ngen-open{n}{b}{G} (App {k1 = k1}{k2 = k2} t1 t2) ve ce d = 
  ≡-KIT (c4 t1 t2 (transpose ve)) 
      ((ngen-open {n}{b}{G}{k1 ⇒ k2} t1 ve ce d)
      {(interp∗  t2 (transpose ve))} (ngen-open t2 ve ce d))
ngen-open (Con c) ve ce d = ≡-KIT (c5 c (transpose ve)) (ce c) 
ngen-open {n}{b} (Mu t) ve ce d
         with (ngen-open (App t (Mu t)) ve ce d) 
... | ng with d {(interp∗ t (transpose ve))}
... | BS = ≡-app{_}{b} (c6' t (transpose ve)) 
        (BS (≡-app {_} {b} (sym (c6 t (transpose ve))) ng))


ngen : {n : ℕ}{b : Vec Set (suc n) → Set}{k : Kind} → 
       (t : Ty k) → (ConstEnv b) → MuGen n b → b ⟨ k ⟩ (repeat ⌊ t ⌋)
ngen{n}{b}{k} t ce d = ≡-KIT {n}{b}{k} c7 (ngen-open t NNil ce d)


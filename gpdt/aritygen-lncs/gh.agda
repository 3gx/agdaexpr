{- Generic Programming with Dependent Types -}
{- Stephanie Weirich and Chris Casinghino   -}
{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}
module gh where

open import Data.Nat
open import Data.Vec 
-- hiding (_∈_)
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality

infixr 50 _⇒_

Choice : Set → Set → Set
Choice = \ A B → ( A × B ) ⊎ A ⊎ B ⊎ ⊤
eq-list : ∀ {A} → (A → A → Bool)  → List A → List A → Bool
eq-list f  []        []        = true
eq-list f  (a ∷ as)  (b ∷ bs)  = f a b ∧ eq-list f as bs
eq-list f  _          _        = false

eq-choice  : ∀ {A B} → (A → A → Bool) → (B → B → Bool) 
           → Choice A B → Choice A B → Bool
eq-choice fa fb (inj₁ (a1 , b1))         (inj₁ (a2 , b2)) = fa a1 a2 ∧ fb b1 b2
eq-choice fa fb (inj₂ (inj₁ a1))         (inj₂ (inj₁ a2))         = fa a1 a2
eq-choice fa fb (inj₂ (inj₂ (inj₁ b1)))  (inj₂ (inj₂ (inj₁ b2)))  = fb b1 b2 
eq-choice fa fb _ _ = true
MyBool    : Set
MyBool    = ⊤ ⊎ ⊤

mytrue    : MyBool
mytrue    = inj₁ tt

myfalse   : MyBool
myfalse   = inj₂ tt

Option   : Set → Set
Option   = \ A → ⊤ ⊎ A

none     : ∀ { A } → Option A
none     = inj₁ tt

some     : ∀ { A } → A → Option A
some a   = inj₂ a

data μ : (Set → Set) → Set where
   roll : ∀{A} → A (μ A) → μ A

unroll : ∀ {A} → μ A → A (μ A)
unroll (roll x) = x

Nat   : Set
Nat   = μ (\ A → ⊤ ⊎ A)

zilch : Nat
zilch = roll (inj₁ tt)

succ  : Nat → Nat
succ x = roll (inj₂ x)

MyList     : Set → Set
MyList A   = μ (\ B → ⊤ ⊎ (A × B))

nil        : ∀ {A} → MyList A
nil        = roll (inj₁ tt)

cons       : ∀ {A} → A → MyList A → MyList A
cons x xs  = roll (inj₂ (x , xs))

MyVec            : Set → ℕ → Set
MyVec A 0        = ⊤
MyVec A (suc n)  = A × MyVec A n

vnil             : ∀ {A} → MyVec A 0
vnil             = tt
                 
vcons            : ∀ {n}{A} → A → MyVec A n → MyVec A (suc n)
vcons x xs       = (x , xs)

data Kind : Set where 
  ⋆    : Kind 
  _⇒_  : Kind → Kind → Kind

data Const : Kind → Set where
  Unit  : Const ⋆
  Sum   : Const (⋆ ⇒ ⋆ ⇒ ⋆) 
  Prod  : Const (⋆ ⇒ ⋆ ⇒ ⋆)

data Ctx : Set where 
  []    : Ctx
  _∷_   : Kind → Ctx → Ctx

data V : Ctx → Kind → Set where
  VZ   : ∀ {Γ k} → V (k ∷ Γ) k
  VS   : ∀ {Γ k' k} → V Γ k → V (k' ∷ Γ) k

data Typ : Ctx → Kind → Set where 
  Var  : ∀ {Γ k} → V Γ k → Typ Γ k 

  Lam  : ∀ {Γ k₁ k₂} → Typ (k₁ ∷ Γ) k₂ 
       → Typ Γ (k₁ ⇒ k₂)

  App  : ∀ {Γ k₁ k₂} → Typ Γ (k₁ ⇒ k₂) → Typ Γ k₁
       → Typ Γ k₂

  Con  : ∀ {Γ k} → Const k → Typ Γ k

  Mu   : ∀ {Γ} → Typ Γ (⋆ ⇒ ⋆) → Typ Γ ⋆

Ty : Kind → Set
Ty = Typ []

⟦_⟧        : Kind → Set
⟦ ⋆ ⟧      = Set
⟦ a ⇒ b ⟧  = ⟦ a ⟧ → ⟦ b ⟧

C⟦_⟧ : ∀ {k} → Const k → ⟦ k ⟧
C⟦ Unit ⟧     = ⊤    -- has kind |Set|
C⟦ Sum ⟧      = _⊎_  -- has kind |Set → Set → Set|
C⟦ Prod ⟧     = _×_

data Env : Ctx → Set where
  []   : Env [] 
  _∷_  : ∀ {k G} → ⟦ k ⟧ → Env G → Env (k ∷ G)

sLookup : ∀ {k G} → V G k → Env G → ⟦ k ⟧
sLookup VZ      (v ∷ G) = v
sLookup (VS x)  (v ∷ G) = sLookup x G

interp : ∀ {k G} → Typ G k → Env G → ⟦ k ⟧
interp (Var x) e        = sLookup x e
interp (Lam t) e        = \ y → interp t (y ∷ e)
interp (App t1 t2) e    = (interp t1 e) (interp t2 e)
interp (Con c) e        = C⟦ c ⟧
interp (Mu t)  e        = μ (interp t e)

⌊_⌋ : ∀ {k} → Ty k → ⟦ k ⟧
⌊ t ⌋ = interp t []

list : Ty (⋆ ⇒ ⋆) 
list = 
  Lam (Mu (Lam 
      (App  (App (Con Sum) (Con Unit)) 
            (App (App (Con Prod) (Var (VS VZ))) (Var VZ)))))

myvec : ℕ → Ty (⋆ ⇒ ⋆)
myvec n = Lam (f n) where 
      f : ℕ → Typ (⋆ ∷ []) ⋆ 
      f 0        = Con Unit
      f (suc n)  = App (App (Con Prod) (Var VZ)) (f n)

-- code for structural nat type
nat : Ty ⋆ 
nat = Mu (Lam (App (App (Con Sum) (Con Unit)) (Var VZ)))

maybe : Ty (⋆ ⇒ ⋆) 
maybe = 
   Lam (App (App (Con Sum) (Con Unit)) (Var VZ))

_⟨_⟩_ : (Set → Set) → (k : Kind) → ⟦ k ⟧ → Set 
b ⟨ ⋆ ⟩        t  = b t
b ⟨ k1 ⇒ k2 ⟩  t  = ∀ { A } → b ⟨ k1 ⟩ A → b ⟨ k2 ⟩ (t A)

Eq : Set → Set
Eq A = A → A → Bool


geq-prod  : ∀ {A} → (A → A → Bool) → ∀{B} → (B → B → Bool)
          → (A × B) → (A × B) → Bool
geq-prod ra rb ( x₁ , x₂ ) (y₁ , y₂) = ra x₁ y₁ ∧ rb x₂ y₂

geq-sum   : ∀ {A} → (A → A → Bool) → ∀ {B} → (B → B → Bool)
            → (A ⊎ B) → (A ⊎ B) → Bool
geq-sum ra rb (inj₁ x₁) (inj₁ x₂)  = ra x₁ x₂
geq-sum ra rb (inj₂ x₁) (inj₂ x₂)  = rb x₁ x₂
geq-sum _ _ _ _                  = false

geq-c : {k : Kind} → (c : Const k) → Eq ⟨ k ⟩ ⌊ Con c ⌋
geq-c Unit  = \ t1 t2 → true
geq-c Sum   = geq-sum 
geq-c Prod  = geq-prod

data VarEnv  (b : Set → Set) : Ctx → Set where
   []   : VarEnv b []
   _∷_  : {k : Kind} {Γ : Ctx} {a : ⟦ k ⟧}
        → b ⟨ k ⟩ a  → VarEnv b Γ → VarEnv b (k ∷ Γ)

toEnv : {Γ : Ctx}{b : Set → Set} → VarEnv b Γ → Env Γ
toEnv [] = []
toEnv (_∷_ {_}{_}{a} _ r) = a ∷ toEnv r

vLookup : ∀ {Γ k}{b : Set → Set} → (v : V Γ k) → (ve : VarEnv b Γ)
           → b ⟨ k ⟩ (sLookup v (toEnv ve))
vLookup VZ      (v ∷ ve)  = v
vLookup (VS x)  (v ∷ ve)  = vLookup x ve

geq-mu    : ∀ {A} → Eq (A (μ A)) → Eq (μ A)
geq-mu f  = \ x y -> f (unroll x) (unroll y)

geq-open : {Γ : Ctx}{k : Kind} 
    → (ve : VarEnv Eq Γ)
    → (t : Typ Γ k) → Eq ⟨ k ⟩ (interp t (toEnv ve))
geq-open ve (Var v)      = vLookup v ve
geq-open ve (Lam t)      = \ y → geq-open (y ∷ ve) t
geq-open ve (App t1 t2)  = (geq-open ve t1) (geq-open ve t2)
geq-open ve (Mu t)       = geq-mu (geq-open ve (App t (Mu t)))
geq-open ve (Con c)      = geq-c c  

ConstEnv : (Set → Set) → Set
ConstEnv b = ∀ {k} → (c : Const k) → b ⟨ k ⟩ ⌊ Con c ⌋

MuGen : (Set → Set) → Set
MuGen b = ∀ {A} → b (A (μ A)) → b (μ A)

gen-open  : {b : Set → Set}{Γ : Ctx}{k : Kind} 
          → ConstEnv b → (ve : VarEnv b Γ) → MuGen b
          → (t : Typ Γ k) → b ⟨ k ⟩ (interp t (toEnv ve))
gen-open ce ve d (Var v)      = vLookup v ve
gen-open ce ve d (Lam t)      = \ y → gen-open ce (y ∷ ve) d t
gen-open ce ve d (App t1 t2)  = 
   (gen-open ce ve d t1) (gen-open ce ve d t2)
gen-open ce ve d (Con c)      = ce c 
gen-open ce ve d (Mu t)       = 
   d (gen-open ce ve d (App t (Mu t)))

gen  : {b : Set → Set} {k : Kind} → ConstEnv b → MuGen b
     → (t : Ty k) → b ⟨ k ⟩ ⌊ t ⌋
gen c b t = gen-open c [] b t

geq : {k : Kind} → (t : Ty k) → Eq ⟨ k ⟩ ⌊ t ⌋
geq = gen geq-c geq-mu 

Count : Set → Set 
Count A = A → ℕ

gcount : {k : Kind} → (t : Ty k) → Count ⟨ k ⟩ ⌊ t ⌋
gcount = gen gcount-c gcount-mu where
  gcount-c : ConstEnv Count
  gcount-c Unit = \ t → 0
  gcount-c Sum  = gcount-sum where
     -- gcount-sum : ∀ { A } → _ → ∀ { B } → _ → (A ⊎ B) → ℕ
     gcount-sum : ∀ { A } → (A → ℕ) → ∀ { B } → (B → ℕ) → (A ⊎ B) → ℕ
     gcount-sum ra rb (inj₁ x) = ra x 
     gcount-sum ra rb (inj₂ x) = rb x
  gcount-c Prod = gcount-prod where
     gcount-prod : ∀ { A } → (A → ℕ) → ∀ { B } → (B → ℕ) → (A × B) → ℕ
     -- gcount-prod : ∀ { A } → _ → ∀ { B } → _ → (A × B) → ℕ
     gcount-prod ra rb ( x₁ , x₂ ) = ra x₁ + rb  x₂

  gcount-mu : MuGen Count
  gcount-mu f = \ x → f (unroll x)

gsize : (t : Ty (⋆ ⇒ ⋆)) → ∀ {A} → ⌊ t ⌋ A → ℕ
gsize t = gcount t (\ x → 1)

gsum : (t : Ty (⋆ ⇒ ⋆)) → ⌊ t ⌋ ℕ → ℕ
gsum t = gcount t (\ x → x)

exlist2 : MyList ℕ
exlist2 = cons 1 (cons 2 (cons 3 nil))

exvec2 : MyVec ℕ 3 
exvec2 = vcons {2} 1 (vcons {1} 2 (vcons {0} 3 (vnil {ℕ})))


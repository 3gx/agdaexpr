{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}


open import Data.Nat
-- open import Data.Vec
open import Data.Unit -- imports ⊤
open import Data.Product -- imports ×
open import Data.Sum -- imports ⊎
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; cong; sym)

Choice : Set → Set → Set
Choice = λ A B → (A × B) ⊎ (A ⊎ (B ⊎ ⊤))

eq-list : ∀ {A} → (A → A → Bool) → List A → List A → Bool
eq-list f [] [] = true
eq-list f (a ∷ as) (b ∷ bs) = f a b ∧ eq-list f as bs
eq-list f _ _ = false

eq-choice : ∀ {A B} → (A → A → Bool) → (B → B → Bool)
                    → Choice A B → Choice A B → Bool
eq-choice fa fb (inj₁ (a1 , b1)) (inj₁ (a2 , b2)) = fa a1 a2 ∧ fb b1 b2
eq-choice fa fb (inj₂ (inj₁ a1)) (inj₂ (inj₁ a2)) = fa a1 a2
eq-choice fa fb (inj₂ (inj₂ (inj₁ b1))) (inj₂ (inj₂ (inj₁ b2))) = fb b1 b2
eq-choice fa fb _ _ = true

{-
size-nat : ℕ → ℕ
size-bool : Bool → ℕ
size-list : ∀ {A} → (A → ℕ) → List A → ℕ
size-choice : ∀ {A B} → (A → ℕ) → (B → ℕ) → Choice A B → ℕ

arb-nat : ℕ
arb-bool : Bool
arb-list : ∀ {A} → A → List A
arb-choice : ∀ {A B} → A → B → Choice A B
-}

MyBool : Set
MyBool = ⊤ ⊎ ⊤

mytrue : MyBool
mytrue = inj₁ tt

myfalse : MyBool
myfalse = inj₂ tt

Option : Set → Set
Option = λ A → ⊤ ⊎ A

none : ∀ {A} → Option A
none = inj₁ tt

some : ∀ {A} → A → Option A
some a = inj₂ a

data μ : (Set → Set) → Set where
    roll : ∀ {A} → A (μ A) → μ A

unroll : ∀ {A} → μ A → A (μ A)
unroll (roll x) = x

Nat : Set
Nat = μ (λ A → ⊤ ⊎ A)

zilch : Nat
zilch = roll (inj₁ tt)

succ : Nat → Nat
succ x = roll (inj₂ x)

one : Nat
one = succ zilch

two : Nat
two = succ one

MyList : Set → Set
MyList A =  μ (λ B → ⊤ ⊎ (A × B))

nil : ∀ {A} → MyList A
nil = roll (inj₁ tt)

cons : ∀ {A} → A → MyList A → MyList A
cons x xs = roll (inj₂ (x , xs))

MyVec : Set → ℕ → Set
MyVec A 0 = ⊤
MyVec A (suc n) = A × MyVec A n

vnil : ∀ {A} → MyVec A 0
vnil = tt

vcons : ∀ {n} {A} → A → MyVec A n → MyVec A (suc n)
vcons x xs = (x , xs)


infixr 50 _⇒_
data Kind : Set where
    ⋆ : Kind
    _⇒_ : Kind → Kind → Kind

data Const : Kind → Set where
    Unit : Const ⋆
    Sum : Const (⋆ ⇒ ⋆ ⇒ ⋆)
    Prod : Const (⋆ ⇒ ⋆ ⇒ ⋆)

data Ctx : Set where
    [] : Ctx
    _∷_ : Kind → Ctx → Ctx

data V : Ctx → Kind → Set where
    VZ : ∀ {Γ k} → V (k ∷ Γ) k
    VS : ∀ {Γ k' k} → V Γ k → V (k' ∷ Γ) k

data Typ : Ctx → Kind → Set where
    Var : ∀ {Γ k} → V Γ k → Typ Γ k
    Lam : ∀ {Γ k₁ k₂} → Typ (k₁ ∷ Γ) k₂ → Typ Γ (k₁ ⇒ k₂)
    App : ∀ {Γ k₁ k₂} → Typ Γ (k₁ ⇒ k₂) → Typ Γ k₁ → Typ Γ k₂
    Con  : ∀ {Γ k} → Const k → Typ Γ k
    Mu : ∀ {Γ} → Typ Γ (⋆ ⇒ ⋆) → Typ Γ ⋆

Ty : Kind → Set
Ty = Typ []

⟦_⟧ : Kind → Set
⟦ ⋆ ⟧ = Set
⟦ a ⇒ b ⟧ = ⟦ a ⟧ → ⟦ b ⟧

C⟦_⟧ : ∀ {k} → Const k → ⟦ k ⟧
C⟦ Unit ⟧ = ⊤  -- has kind Set
C⟦ Sum ⟧ = _⊎_ -- has kind Set → Set → Set
C⟦ Prod ⟧ = _×_

data Env : Ctx → Set where
    [] : Env []
    _∷_ : ∀ {k G} → ⟦ k ⟧ → Env G → Env (k ∷ G)
sLookup : ∀ {k G} → V G k → Env G → ⟦ k ⟧
sLookup VZ (v ∷ G) = v
sLookup (VS x) (v ∷ G) = sLookup x G

interp : ∀ {G k} → Typ G k → Env G → ⟦ k ⟧
interp (Var x) e = sLookup x e
interp (Lam t) e = λ y → interp t (y ∷ e)
interp (App t1 t2) e = (interp t1 e) (interp t2 e)
interp (Con c) e = C⟦ c ⟧
interp (Mu t) e = μ (interp t e)

⌊_⌋ : ∀ {k} → Ty k → ⟦ k ⟧
⌊ t ⌋ = interp t []

list : Ty (⋆ ⇒ ⋆)
list =
    Lam( Mu (Lam
         (App (App (Con Sum) (Con Unit))
         (App (App (Con Prod) (Var (VS VZ))) (Var VZ)))))

_ : ⌊ list ⌋ ≡ MyList
_ = refl

myvec : ℕ → Ty (⋆ ⇒ ⋆)
myvec n = Lam (f n) where
    f : ℕ → Typ (⋆ ∷ []) ⋆
    f 0 = Con Unit
    f (suc n) = App (App (Con Prod) (Var VZ)) (f n)

_ : ⌊ myvec 4 ⌋ ℕ ≡ MyVec ℕ 4
_ = refl

{- doesn't typecheck
_ : ⌊ myvec 4 ⌋ ≡ ∀ {A} → MyVec A 4
_ = refl
-}

_⟨_⟩_ : (Set → Set) → (k : Kind) → ⟦ k ⟧ → Set
b ⟨ ⋆ ⟩ t = b t
b ⟨ k1 ⇒ k2 ⟩ t = ∀ {A} → b ⟨ k1 ⟩ A → b ⟨ k2 ⟩ (t A)

Eq : Set → Set
Eq A = A → A → Bool

eq-bool' : Eq ⟨ ⋆ ⟩ Bool
    -- Bool → Bool → Bool
eq-bool' true true = true
eq-bool' false false = true
eq-bool' _ _ = false

{- doesn't typecheck
eq-list' : Eq ⟨ ⋆ ⇒ ⋆ ⟩ MyList
    -- ∀ A → (A → A → Bool) → (MyList A → MyList A → Bool)
eq-list' f nil nil = true
eq-list' f (a ∷ as) (b ∷ bs) = f a b ∧ eq-list f as bs
eq-list' f _ _ = false
-}

eq-choice' : Eq ⟨ ⋆ ⇒ ⋆ ⇒ ⋆ ⟩ Choice
    -- ∀ A → (A → A → Bool) → ∀ B → (B → B → Bool)
    --     → (Choice A B → Choice A B → Bool)
eq-choice' fa fb (inj₁ (a1 , b1)) (inj₁ (a2 , b2)) = fa a1 a2 ∧ fb b1 b2
eq-choice' fa fb (inj₂ (inj₁ a1)) (inj₂ (inj₁ a2)) = fa a1 a2
eq-choice' fa fb (inj₂ (inj₂ (inj₁ b1))) (inj₂ (inj₂ (inj₁ b2))) = fb b1 b2
eq-choice' fa fb _ _ = true

geq-prod  : ∀ {A} → (A → A → Bool) → ∀{B} → (B → B → Bool)
                  → (A × B) → (A × B) → Bool
geq-prod ra rb ( x₁ , x₂ ) (y₁ , y₂) = ra x₁ y₁ ∧ rb x₂ y₂

geq-sum   : ∀ {A} → (A → A → Bool) → ∀ {B} → (B → B → Bool)
                  → (A ⊎ B) → (A ⊎ B) → Bool
geq-sum ra rb (inj₁ x₁) (inj₁ x₂) = ra x₁ x₂
geq-sum ra rb (inj₂ x₁) (inj₂ x₂) = rb x₁ x₂
geq-sum _ _ _ _  = false

geq-c : {k : Kind} → (c : Const k) → Eq ⟨ k ⟩ ⌊ Con c ⌋
geq-c Unit  = λ t1 t2 → true
geq-c Sum   = geq-sum 
geq-c Prod  = geq-prod

data VarEnv  (b : Set → Set) : Ctx → Set where
   [] : VarEnv b []
   _∷_ : {k : Kind} {Γ : Ctx} {a : ⟦ k ⟧}
          → b ⟨ k ⟩ a  → VarEnv b Γ → VarEnv b (k ∷ Γ)

toEnv : {Γ : Ctx} { b : Set → Set} → VarEnv b Γ → Env Γ
toEnv [] = []
toEnv (_∷_ {_}{_}{a} _ r) = a ∷ toEnv r

vLookup : ∀ {Γ k} {b : Set → Set} → (v : V Γ k) → (ve : VarEnv b Γ)
                                 → b ⟨ k ⟩ (sLookup v (toEnv ve))
vLookup VZ     (v ∷ ve) = v
vLookup (VS x) (v ∷ ve) = vLookup x ve

geq-mu    : ∀ {A} → Eq (A (μ A)) → Eq (μ A)
geq-mu f  = λ x y -> f (unroll x) (unroll y)

geq-open : {Γ : Ctx} {k : Kind} → (ve : VarEnv Eq Γ)
                                → (t : Typ Γ k)
                                → Eq ⟨ k ⟩ (interp t (toEnv ve))
geq-open ve (Var v)     = vLookup v ve
geq-open ve (Lam t)     = λ y → geq-open (y ∷ ve) t
geq-open ve (App t1 t2) = (geq-open ve t1) (geq-open ve t2)
geq-open ve (Mu t)      = geq-mu (geq-open ve (App t (Mu t)))
geq-open ve (Con c)     = geq-c c  

geq : {k : Kind} → (t : Ty k) → Eq ⟨ k ⟩ ⌊ t ⌋
geq t = geq-open [] t


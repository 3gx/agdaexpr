import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

data Bool : Set where
    true : Bool
    false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _ = false

if_then_else : ∀ {A : Set} → Bool → A → A → A
if true then a1 else a2 = a1
if false then a1 else a2 = a2

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

replicate : ∀ {A : Set} → ℕ → A → List A
replicate zero x = []
replicate (suc n) x = x :: replicate n x

data Vec (A : Set) : ℕ → Set where
    [] : Vec A zero
    _::_ : ∀ {n} → A → (Vec A n) → Vec A (suc n)

repeat : ∀ {n} {A} → A → Vec A n
repeat { zero } x = []
repeat { suc n } x = x :: repeat x

eq-bool : Bool → Bool → Bool
eq-bool true true = true
eq-bool false false = true
eq-bool _ _ = false

eq-nat : ℕ → ℕ → Bool
eq-nat zero zero = true
eq-nat (suc n) (suc m) = eq-nat m n
eq-nat _ _ = false

-- non-dependent pair
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : ∀ {A B} → A × B → A
fst (a , b) = a

snd : ∀ {A B} → A × B → B
snd (a , b) = b

-- Universe
data Type : Set where
    TNat : Type
    TBool : Type
    TProd : Type → Type → Type

⌊_⌋ : Type → Set
⌊ TNat ⌋ = ℕ
⌊ TBool ⌋ = Bool
⌊ TProd t1 t2 ⌋ = ⌊ t1 ⌋ × ⌊ t2 ⌋

geq : (t : Type) → ⌊ t ⌋ → ⌊ t ⌋ → Bool
geq TNat n1  n2 = eq-nat n1 n2
geq TBool b1 b2 = eq-bool b1 b2
geq (TProd a b) (a1 , b1) (a2 , b2) = geq a a1 a2 ∧ geq b b1 b2

_ : Bool 
_ = geq (TProd TNat TBool) ( suc zero , false) ( suc zero , false)

_ : geq (TProd TNat TBool) ( suc zero , false) ( suc zero , false) ≡ true
_ = refl

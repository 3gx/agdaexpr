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
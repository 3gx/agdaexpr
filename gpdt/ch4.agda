{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}


open import Data.Nat
-- open import Data.Vec
open import Data.Unit -- imports ⊤
open import Data.Product -- imports ×
open import Data.Sum -- imports ⊎
open import Data.Bool
open import Data.List
-- open import Relation.Binary.PropositionalEquality

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
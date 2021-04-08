{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}


-- open import Data.Nat
-- open import Data.Vec 

open import Data.Unit -- imports ⊤
open import Data.Product -- imports ×
open import Data.Sum -- imports ⊎

-- open import Data.Bool
-- open import Data.List
-- open import Relation.Binary.PropositionalEquality

Choice : Set → Set → Set
Choice = λ A B → (A × B) ⊎ A ⊎ B ⊎ ⊤

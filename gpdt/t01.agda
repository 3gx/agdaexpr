data Bool : Set where
    true : Bool
    false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _ = false

{-
if_then_else : ∀ {A} → Bool → A → A → A
if true then a1 else a2 = a1
if false then a1 else a2 = a2
-}

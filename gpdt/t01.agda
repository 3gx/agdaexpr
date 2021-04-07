data Bool : Set where
    true : Bool
    false : Bool 

¬ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _ = false

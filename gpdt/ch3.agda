open import ch2

map0 : { m : ℕ } { A : Set } → A → Vec A m
map0 = repeat

_⊛_ : { A B : Set } { n : ℕ } → Vec (A → B) n → Vec A n → Vec B n
[] ⊛ [] = []
(a :: As) ⊛ (b :: Bs) = a b :: As ⊛ Bs
infixl 40 _⊛_

map1 : { m : ℕ } { A B : Set } → (A → B) → Vec A m → Vec B m
map1 f x = repeat f ⊛ x

map2 : {m : ℕ} {A B C : Set} → (A → B → C) → Vec A m → Vec B m → Vec C m
map2 f x y = repeat f ⊛ x ⊛ y

{-# OPTIONS --type-in-type #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
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

arrTy : { n : ℕ } → Vec Set (suc n) → Set
arrTy {zero} (A :: []) = A
arrTy {suc n} (A :: As) = A → arrTy As

-- _ : arrTy (ℕ :: (ℕ :: [])) ≡ ℕ → ℕ
-- _ = refl

arrTyVec : {n : ℕ} → ℕ → Vec Set (suc n) → Set
arrTyVec m As = arrTy (repeat (λ A → Vec A m) ⊛ As)


map0' : { m : ℕ } { A : Set } → arrTy (A :: []) → arrTyVec m ( A :: [])
map0' = repeat

map1' : {m : ℕ} { A B : Set} → arrTy (A :: (B :: [])) 
                             → arrTyVec m (A :: (B :: []))
map1' f x = repeat f ⊛ x

map2' : {m : ℕ} { A B C : Set} → arrTy (A :: (B :: (C :: []))) 
                               → arrTyVec m (A :: (B :: (C :: [])))
map2' f x y = repeat f ⊛ x ⊛ y

nvec-map : {m : ℕ} → (n : ℕ) → {As : Vec Set (suc n)}
                           → arrTy As → arrTyVec m As
nvec-map n f = g n (repeat f) where
    g : {m : ℕ} → (n : ℕ) -> {As : Vec Set (suc n)}
                → Vec (arrTy As) m → arrTyVec m As
    g zero {A :: []} a = a
    g (suc n) {A :: As} f = (λ a → g n (f ⊛ a))

_ : nvec-map (suc zero) {Bool :: (Bool :: [])} (λ x → ¬ x)
                              (true :: (false :: [])) ≡ 
                              (false :: (true :: []))
_ = refl
                          
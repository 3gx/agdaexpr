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

-- 3.1 Typing Arity-Generic Vector Map

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

-- 3.2 - A curried vector map

{-
v∀⇒ : {n : ℕ}  
    -> (Vec Set n -> Set) 
    -> Set
v∀⇒ {ℕ.zero}       B = B []
v∀⇒ {ℕ.suc n} B = ∀ {x} -> v∀⇒ (λ xs -> B (x :: xs))

vλ⇒ : {n : ℕ} {B : (_ : Vec Set n) -> Set} 
    -> ((xs : Vec Set n) -> B xs) 
    -> v∀⇒ B
vλ⇒ {ℕ.zero}       f = f []
vλ⇒ {ℕ.suc n} f = λ {x} -> vλ⇒ (λ xs -> f (x :: xs))
-}

{-
∀⇒ : {n : ℕ} → ((_ : Vec Set n) → Set) → Set
∀⇒ {zero} B = B []
∀⇒ {suc n} B = {a : Set} → ∀⇒ {_} (λ as → B (a :: as))

λ⇒ : {n : ℕ} {B : (_ : Vec Set n) → Set}
             → ({X : Vec Set n} → B X) → (∀⇒ {n} B)
λ⇒ {zero} {_} f = f {[]}

-- the following case doesn't typecheck ;(
λ⇒ {suc n} {_} f = λ {a : Set} → λ⇒ {n} (λ {as} → f {a :: as})
-- λ⇒ {suc n} f = λ {a : Set} → λ⇒ {n} (λ {as} → f {a :: as})
-}

{-
nmap : {m : ℕ} → (n : ℕ)
        → ∀⇒(λ (As : Vec Set (suc n)) → arrTy As → arrTyVec m As)
nmap {m} n = λ⇒ (λ {As} → nvec-map {m} n {As})
-}

{-
_ : nmap (suc zero) (λ x → ¬ x)
                              (true :: (false :: [])) ≡ 
                              (false :: (true :: []))
_ = refl

_ : nmap (suc (suc zero)) (_,_) 
                              (true :: (false :: []))
                              (zero :: (suc zero :: [])) ≡
                              ((true,zero) :: ((false, (suc zero)) :: []))
_ = refl
-}

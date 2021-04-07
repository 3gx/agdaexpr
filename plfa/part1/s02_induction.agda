import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = 
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = 12 ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = 
    begin
      (zero + n) + p
    ≡⟨⟩
      n + p
    ≡⟨⟩
      zero + (n + p)
    ∎
+-assoc (suc m) n p = 
    begin
      (suc m + n) + p
    ≡⟨⟩
      suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
      suc (m + (n + p))
    ≡⟨⟩
      suc m + (n + p)
    ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p = 
    begin
        (2 + n) + p
    ≡⟨⟩
        suc (1 + n) + p
    ≡⟨⟩
        suc ((1 + n) + p)
    -- ≡⟨⟩ -- also works
    ≡⟨ cong suc (+-assoc 1 n p) ⟩
      suc (1 + (n + p))
    ≡⟨⟩
      2 + (n + p)
    ∎

-- first lemma: m + 0 == m
+-id : ∀ (m : ℕ) → m + zero ≡ m
+-id zero = 
    begin
        zero + zero
    ≡⟨⟩
        zero
    ∎
+-id (suc m) =
    begin
        suc m + zero
    ≡⟨⟩
        suc (m + zero)
    ≡⟨ cong suc (+-id m)  ⟩
      suc m
    ∎

-- second lemma: suc m + n == suc (m + n)
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
    begin
        zero + suc n
    ≡⟨⟩
        suc n
    ≡⟨⟩
        suc (zero + n)
    ∎
+-suc (suc m) n =
    begin
        suc m + suc n
    ≡⟨⟩
        suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n))
    ≡⟨⟩
        suc (suc m + n)
    ∎

-- the proposition: m + n == n + m
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = 
    begin
        m + zero
    ≡⟨ (+-id m) ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) =
    begin
        m + (suc n)
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        suc n + m
    ∎


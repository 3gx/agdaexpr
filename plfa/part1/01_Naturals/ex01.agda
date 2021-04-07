data NN : Set where
    zero : NN
    suc : NN → NN

-- zero
-- suc zero

_+_ : NN → NN → NN
zero + n = n
(suc m) + n  = suc (m + n)

_*_ : NN → NN → NN
zero * n = zero
(suc m) * n = n +  (m * n)

_∸_ : NN → NN → NN
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n


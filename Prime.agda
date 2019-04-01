module Prime where

-- IAL
open import bool
open import empty
open import eq
open import list
open import nat
open import product

-- Less than or equal relation -------------------------------------------------

data _<=_ : ℕ → ℕ → Set where
  lteZ : ∀ {n} → 0 <= n
  lteS : ∀ {m n} → m <= n → suc m <= suc n

0lte0 : 0 <= 0
0lte0 = lteZ

_between_and_ : ℕ → ℕ → ℕ → Set
m between l and h = (suc l) <= m × (suc m) <= h

2btwn1and3 : 2 between 1 and 3
2btwn1and3 = lteS (lteS lteZ) , lteS (lteS (lteS lteZ))

-- List membership relation ----------------------------------------------------

data _In_ {ℓ} {a : Set ℓ} (item : a) : 𝕃 a → Set ℓ where
  here : forall {l} → item In (item :: l)
  there : forall {x} {l} → item In l → item In (x :: l)

-- Composite k means there exist m and n such that m times n is k --------------

data Composite (k : ℕ) : Set where
  Cmpst : ∀ {m n} →
    m between 1 and k →
    n between 1 and k →
    m * n ≡ k →
    Composite k

6composite : Composite 6
6composite =
  Cmpst {m = 2} {n = 3}
  ((lteS (lteS lteZ)) , (lteS (lteS (lteS lteZ))))
  ((lteS (lteS lteZ)) , (lteS (lteS (lteS (lteS lteZ)))))
  refl

-- Prime means not composite ---------------------------------------------------

Prime : ℕ → Set
Prime n = Composite n → ⊥

2prime : Prime 2
2prime (Cmpst {zero} {n} (() , b) nBtwn mTimesN)
2prime (Cmpst {suc zero} {n} (lteS () , b) nBtwn mTimesN)
2prime (Cmpst {suc (suc m)} {n} (a , lteS (lteS ())) nBtwn mTimesN)

3prime : Prime 3
3prime (Cmpst {0} {n} (() , _) _ _)
3prime (Cmpst {1} {n} (lteS () , _) _ _)
3prime (Cmpst {2} {0} _ (() , _) _)
3prime (Cmpst {2} {1} _ (lteS () , _) _)
3prime (Cmpst {2} {2} _ _ ())
3prime (Cmpst {2} {suc (suc (suc n))} _ (_ , lteS (lteS (lteS ()))) _)
3prime (Cmpst {suc (suc (suc m))} {n} (_ , lteS (lteS (lteS ()))) _ _)

-- Sieve of Eratosthenes, one step at a time -----------------------------------

checkOnePrime : (ℕ × ℕ) → (𝔹 × 𝕃 (ℕ × ℕ)) → (𝔹 × 𝕃 (ℕ × ℕ))
checkOnePrime (prime , 0) (isPrime , revPrimesAndCounts) =
  (ff , (prime , prime ∸ 1) :: revPrimesAndCounts)
checkOnePrime (prime , suc n) (isPrime , revPrimesAndCounts) =
  (isPrime , (prime , n) :: revPrimesAndCounts)

-- At each step, we are examining a number n. We also have a list of previously
-- found prime numbers, where each prime is accompanied by a counter; when the
-- counter goes to zero, we cross out n (because n is composite). If no counter
-- crosses out n, n is prime, and we add it to the list for the next step.
sieveStep : (ℕ × 𝕃 (ℕ × ℕ)) → (ℕ × 𝕃 (ℕ × ℕ))
sieveStep (n , primesAndCounts)
  with (foldr checkOnePrime (tt , []) primesAndCounts)
... | (isPrime , rpc) =
  suc n , reverse (if isPrime then (n , n ∸ 1) :: rpc else rpc)

sieveLoop : (rem : ℕ) → (ℕ × 𝕃 (ℕ × ℕ)) → 𝕃 ℕ
sieveLoop 0 state = fst (unzip (snd state))
sieveLoop (suc rem') state = sieveLoop rem' (sieveStep state)

-- List of primes up through and including (if prime) n
sieveThrough : ℕ → 𝕃 ℕ
sieveThrough n = reverse (sieveLoop (n ∸ 1) (2 , []))

-- What we'd like to prove -----------------------------------------------------

sievedIsPrime : ∀ {p} → p In sieveThrough p → Prime p
sievedIsPrime {0} ()
sievedIsPrime {suc p} inSieve = {!!}
-- sievedIsPrime {0} ()
-- sievedIsPrime {1} ()
-- sievedIsPrime {2} inSieve = 2prime
-- sievedIsPrime {suc (suc (suc p))} inSieve = {!!}

primeIsSieved : ∀ {p} → Prime p → p In sieveThrough p
primeIsSieved = {!!}

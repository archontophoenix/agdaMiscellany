module EvenOdd where

-- IAL
open import bool
open import empty
open import eq
open import nat

-- Even and Odd as relations (instead of boolean functions) --------------------

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  Even0 : Even 0
  EvenS : ∀ {n} → Odd n → Even (suc n)

data Odd where
  OddS : ∀ {n} → Even n → Odd (suc n)

-- Sanity tests ----------------------------------------------------------------

even2 : Even 2
even2 = EvenS (OddS Even0)

odd3 : Odd 3
odd3 = OddS (EvenS (OddS Even0))

-- Odd and Even are incompatible -----------------------------------------------

oddIsNotEven : ∀ {n} → Odd n → Even n → ⊥
oddIsNotEven {.(suc _)} (OddS evenPrev) (EvenS oddPrev) =
  oddIsNotEven oddPrev evenPrev

-- Odd and Even are equivalent to their IAL counterparts -----------------------

is-even→Even : ∀ {n} → is-even n ≡ tt → Even n
is-odd→Odd : ∀ {n} → is-odd n ≡ tt → Odd n
is-even→Even {0} isEven = Even0
is-even→Even {suc n} isEven = EvenS (is-odd→Odd isEven)
is-odd→Odd {0} ()
is-odd→Odd {suc n} isOdd = OddS (is-even→Even isOdd)

Even→is-even : ∀ {n} → Even n → is-even n ≡ tt
Odd→is-odd : ∀ {n} → Odd n → is-odd n ≡ tt
Even→is-even {zero} Even0 = refl
Even→is-even {suc n} (EvenS nOdd) = Odd→is-odd {n} nOdd
Odd→is-odd {zero} ()
Odd→is-odd {suc n} (OddS nEven) = Even→is-even {n} nEven

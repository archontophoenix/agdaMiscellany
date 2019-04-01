module LteTrans where

-- IAL
open import bool
open import eq
open import nat
open import nat-thms

data _<=_ : ℕ → ℕ → Set where
  lteZ : ∀ {n} → 0 <= n
  lteS : ∀ {m n} → m <= n → suc m <= suc n

<=-trans : ∀ {x y z} → x <= y → y <= z → x <= z
<=-trans lteZ _ = lteZ
<=-trans (lteS xLteY) (lteS yLteZ) = lteS (<=-trans xLteY yLteZ)

<=→≤ : ∀ {x y} → x <= y → x ≤ y ≡ tt
<=→≤ {0} {0} _ = refl
<=→≤ {0} {suc y} _ = refl
<=→≤ {suc x} {zero} ()
<=→≤ {suc x} {suc y} (lteS xLteY) = <=→≤ xLteY

≤→<= : ∀ {x y} → x ≤ y ≡ tt → x <= y
≤→<= {zero} {zero} _ = lteZ
≤→<= {zero} {suc y} _ = lteZ
≤→<= {suc x} {zero} ()
≤→<= {suc x} {suc y} xLteY = lteS (≤→<= (suc≤ {x} {y} xLteY))

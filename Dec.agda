module Dec where

open import empty
open import nat
open import LteTrans

data Dec {ℓ} (prop : Set ℓ) : Set ℓ where
  Yes : (prf : prop) → Dec prop
  No : (contra : prop → ⊥) → Dec prop

<=suc : ∀ {m n} → suc m <= suc n → m <= n
<=suc (lteS sucmn) = sucmn

decLte : ∀ {m n} → Dec (m <= n)
decLte {0} {_} = Yes lteZ
decLte {suc _} {0} = No (λ ())
decLte {suc m'} {suc n'} with decLte {m'} {n'}
decLte {suc m'} {suc n'} | Yes prf = Yes (lteS prf)
decLte {suc m'} {suc n'} | No contra = No (λ x → contra (<=suc x))

module SplitSymmetricNat where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; pred)
open import Data.Fin using (Fin; toℕ; opposite; inject₁) renaming (zero to iz; suc to is)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
import Data.Nat.Properties as NP
open import Data.Fin.Properties using (toℕ-inject₁; opposite-prop)

open import SymmetricNat


before : ∀ {n} → Idx n → ℕ
before 0b₁         = 0
before 0f₁₁        = 0
before (i 1₁₁)     = suc (before i)
before (0r₁₁ {n})  = suc (toN n)

after : ∀ {n} → Idx n → ℕ
after 0b₁         = 0
after (0f₁₁ {n})  = suc (toN n)
after (i 1₁₁)     = suc (after i)
after 0r₁₁        = 0

-- the invariant
split-valid : ∀ {n} (i : Idx n) → before i + suc (after i) ≡ toN n
split-valid 0b₁               = refl
split-valid 0f₁₁              = refl
split-valid (i 1₁₁)           =
  cong suc (trans (NP.+-suc (before i) (suc (after i))) (cong suc (split-valid i)))
split-valid (0r₁₁ {n})        =
  cong suc (trans (NP.+-suc (toN n) 0) (cong suc (NP.+-identityʳ (toN n))))


after-∸ : ∀ {n} (i : Idx n) → toN n ∸ suc (before i) ≡ after i
after-∸ i =
  trans (cong (_∸ suc (before i)) (sym (split-valid i)))
        (trans (cong (_∸ suc (before i)) (NP.+-suc (before i) (after i)))
               (NP.m+n∸m≡n (before i) (after i)))


before-ifirst : ∀ {n} (nz : toN n ≢ 0) → before (ifirst {n} nz) ≡ 0
before-ifirst {N0} nz          = ⊥-elim (nz refl)
before-ifirst {N1} nz          = refl
before-ifirst {D1 ⟨ n ⟩ D1} nz = refl

after-ifirst : ∀ {n} (nz : toN n ≢ 0) → after (ifirst {n} nz) ≡ pred (toN n)
after-ifirst {N0} nz          = ⊥-elim (nz refl)
after-ifirst {N1} nz          = refl
after-ifirst {D1 ⟨ n ⟩ D1} nz = refl

before-ilast : ∀ {n} (nz : n ≢ N0) → before (ilast {n} nz) ≡ pred (toN n)
before-ilast {N0} nz          = ⊥-elim (nz refl)
before-ilast {N1} nz          = refl
before-ilast {D1 ⟨ n ⟩ D1} nz = refl

after-ilast : ∀ {n} (nz : n ≢ N0) → after (ilast {n} nz) ≡ 0
after-ilast {N0} nz          = ⊥-elim (nz refl)
after-ilast {N1} nz          = refl
after-ilast {D1 ⟨ n ⟩ D1} nz = refl

-- consing on the front increases before by one and after unchanged
before-isuccL : ∀ {n} (i : Idx n) → before (isuccL i) ≡ suc (before i)
before-isuccL 0b₁                    = refl
before-isuccL {D1 ⟨ n ⟩ D1} 0f₁₁     = cong suc (before-ifirst {incL n} (incL≢0 n))
before-isuccL {D1 ⟨ n ⟩ D1} (i 1₁₁)  = cong suc (before-isuccL i)
before-isuccL {D1 ⟨ n ⟩ D1} 0r₁₁     = cong suc (incL-correct n)

after-isuccL : ∀ {n} (i : Idx n) → after (isuccL i) ≡ after i
after-isuccL 0b₁                    = refl
after-isuccL {D1 ⟨ n ⟩ D1} 0f₁₁     =
  trans (cong suc (after-ifirst {incL n} (incL≢0 n))) (cong suc (cong pred (incL-correct n)))
after-isuccL {D1 ⟨ n ⟩ D1} (i 1₁₁)  = cong suc (after-isuccL i)
after-isuccL {D1 ⟨ n ⟩ D1} 0r₁₁     = refl

before-isuccR : ∀ {n} (i : Idx n) → before (isuccR i) ≡ before i
before-isuccR 0b₁                    = refl
before-isuccR {D1 ⟨ n ⟩ D1} 0f₁₁     = refl
before-isuccR {df ⟨ n ⟩ D1} (i 1₁₁)  = cong suc (before-isuccR i)
before-isuccR {d ⟨ n ⟩ D1} 0r₁₁      =
  cong suc (trans (before-ilast {incR n} (incR≢0 n)) (cong pred (incR-correct n)))

after-isuccR : ∀ {n} (i : Idx n) → after (isuccR i) ≡ suc (after i)
after-isuccR 0b₁                    = refl
after-isuccR {D1 ⟨ n ⟩ D1} 0f₁₁     = cong suc (incR-correct n)
after-isuccR {df ⟨ n ⟩ D1} (i 1₁₁)  = cong suc (after-isuccR i)
after-isuccR {d ⟨ n ⟩ D1} 0r₁₁      = cong suc (after-ilast {incR n} (incR≢0 n))

-- toF is before
toF-before : ∀ {n} (i : Idx n) → toℕ (toF i) ≡ before i
toF-before 0b₁                   = refl
toF-before 0f₁₁                  = refl
toF-before {D1 ⟨ n ⟩ D1} (i 1₁₁) =
  trans (cong suc (toℕ-inject₁ (toF i))) (cong suc (toF-before i))
toF-before {D1 ⟨ n ⟩ D1} 0r₁₁    = opposite-prop iz

toF-after : ∀ {n} (i : Idx n) → toℕ (opposite (toF i)) ≡ after i
toF-after {n} i =
  trans (opposite-prop (toF i))
        (trans (cong (λ x → toN n ∸ suc x) (toF-before i)) (after-∸ i))

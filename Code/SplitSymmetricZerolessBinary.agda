module SplitSymmetricZerolessBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; pred)
open import Data.Fin using (Fin; toℕ; opposite; inject₁; fromℕ) renaming (zero to iz; suc to is; pred to ip)
open import Relation.Binary.PropositionalEquality
import Data.Nat.Properties as NP
open import Data.Fin.Properties using (toℕ-inject₁; opposite-prop; toℕ-fromℕ)
open import Data.Nat.Tactic.RingSolver using (solve-∀)

open import SymmetricZerolessBinary

-- ℕ helpers

2*≡+ : ∀ x → 2* x ≡ x + x
2*≡+ zero    = refl
2*≡+ (suc x) = trans (cong (λ z → suc (suc z)) (2*≡+ x)) (sym (cong suc (NP.+-suc x x)))

x+1 : ∀ x → x + 1 ≡ suc x
x+1 x = NP.+-comm x 1

x+2 : ∀ x → x + 2 ≡ suc (suc x)
x+2 x = NP.+-comm x 2

-- Fin helpers

toℕ-∙2+0 : ∀ {m} (i : Fin m) → toℕ (i ∙2+0) ≡ 2* (toℕ i)
toℕ-∙2+0 iz     = refl
toℕ-∙2+0 (is i) = cong (λ z → suc (suc z)) (toℕ-∙2+0 i)

toℕ-∙2+1 : ∀ {m} (i : Fin m) → toℕ (i ∙2+1) ≡ suc (2* (toℕ i))
toℕ-∙2+1 iz     = refl
toℕ-∙2+1 (is i) = cong (λ z → suc (suc z)) (toℕ-∙2+1 i)

before : ∀ {n} → Idx n → ℕ
before 0b₁          = 0
before 0f₁₁         = 0
before (0r₁₁ {n})   = suc (2* (toN n))
before ⟪1₁ i 2₁⟫    = suc (2* (before i))
before ⟪2₁ i 1₁⟫    = suc (suc (2* (before i)))
before 0f₁₂         = 0
before (0r₁₂ {n})   = suc (suc (2* (toN n)))
before (1r₁₂ {n})   = suc (2* (toN n))
before ⟪1₁ i 3₂⟫    = suc (2* (before i))
before ⟪2₁ i 2₂⟫    = suc (suc (2* (before i)))
before 0f₂₁         = 0
before 1f₂₁         = 1
before (0r₂₁ {n})   = suc (suc (2* (toN n)))
before ⟪2₂ i 2₁⟫    = suc (suc (2* (before i)))
before ⟪3₂ i 1₁⟫    = suc (suc (suc (2* (before i))))
before 0f₂₂         = 0
before 1f₂₂         = 1
before (0r₂₂ {n})   = suc (suc (suc (2* (toN n))))
before (1r₂₂ {n})   = suc (suc (2* (toN n)))
before ⟪2₂ i 3₂⟫    = suc (suc (2* (before i)))
before ⟪3₂ i 2₂⟫    = suc (suc (suc (2* (before i))))

after : ∀ {n} → Idx n → ℕ
after 0b₁           = 0
after (0f₁₁ {n})    = suc (2* (toN n))
after 0r₁₁          = 0
after ⟪1₁ i 2₁⟫     = suc (suc (2* (after i)))
after ⟪2₁ i 1₁⟫     = suc (2* (after i))
after (0f₁₂ {n})    = suc (suc (2* (toN n)))
after 0r₁₂          = 0
after 1r₁₂          = 1
after ⟪1₁ i 3₂⟫     = suc (suc (suc (2* (after i))))
after ⟪2₁ i 2₂⟫     = suc (suc (2* (after i)))
after (0f₂₁ {n})    = suc (suc (2* (toN n)))
after (1f₂₁ {n})    = suc (2* (toN n))
after 0r₂₁          = 0
after ⟪2₂ i 2₁⟫     = suc (suc (2* (after i)))
after ⟪3₂ i 1₁⟫     = suc (2* (after i))
after (0f₂₂ {n})    = suc (suc (suc (2* (toN n))))
after (1f₂₂ {n})    = suc (suc (2* (toN n)))
after 0r₂₂          = 0
after 1r₂₂          = 1
after ⟪2₂ i 3₂⟫     = suc (suc (suc (2* (after i))))
after ⟪3₂ i 2₂⟫     = suc (suc (2* (after i)))

-- addition helpers

a₁₂₁ : ∀ x y → suc (x + x) + suc (suc (suc (y + y))) ≡ 2 + ((x + suc y) + (x + suc y))
a₁₂₁ = solve-∀
a₂₁₁ : ∀ x y → suc (suc (x + x)) + suc (suc (y + y)) ≡ 2 + ((x + suc y) + (x + suc y))
a₂₁₁ = solve-∀
a₁₃₂ : ∀ x y → suc (x + x) + suc (suc (suc (suc (y + y)))) ≡ 3 + ((x + suc y) + (x + suc y))
a₁₃₂ = solve-∀
a₂₂₂ : ∀ x y → suc (suc (x + x)) + suc (suc (suc (y + y))) ≡ 3 + ((x + suc y) + (x + suc y))
a₂₂₂ = solve-∀
a₂₂₁ : ∀ x y → suc (suc (x + x)) + suc (suc (suc (y + y))) ≡ 3 + ((x + suc y) + (x + suc y))
a₂₂₁ = solve-∀
a₃₁₁ : ∀ x y → suc (suc (suc (x + x))) + suc (suc (y + y)) ≡ 3 + ((x + suc y) + (x + suc y))
a₃₁₁ = solve-∀
a₂₃₂ : ∀ x y → suc (suc (x + x)) + suc (suc (suc (suc (y + y)))) ≡ 4 + ((x + suc y) + (x + suc y))
a₂₃₂ = solve-∀
a₃₂₂ : ∀ x y → suc (suc (suc (x + x))) + suc (suc (suc (y + y))) ≡ 4 + ((x + suc y) + (x + suc y))
a₃₂₂ = solve-∀

split-valid : ∀ {n} (i : Idx n) → before i + suc (after i) ≡ toN n
split-valid 0b₁        = refl
split-valid 0f₁₁       = refl
split-valid (0r₁₁ {n}) = cong suc (x+1 (2* (toN n)))
split-valid ⟪1₁ i 2₁⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₁₂₁ (before i) (after i)
split-valid ⟪2₁ i 1₁⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₂₁₁ (before i) (after i)
split-valid 0f₁₂       = refl
split-valid (0r₁₂ {n}) = cong (λ z → suc (suc z)) (x+1 (2* (toN n)))
split-valid (1r₁₂ {n}) = cong suc (x+2 (2* (toN n)))
split-valid ⟪1₁ i 3₂⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₁₃₂ (before i) (after i)
split-valid ⟪2₁ i 2₂⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₂₂₂ (before i) (after i)
split-valid 0f₂₁       = refl
split-valid 1f₂₁       = refl
split-valid (0r₂₁ {n}) = cong (λ z → suc (suc z)) (x+1 (2* (toN n)))
split-valid ⟪2₂ i 2₁⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₂₂₁ (before i) (after i)
split-valid ⟪3₂ i 1₁⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₃₁₁ (before i) (after i)
split-valid 0f₂₂       = refl
split-valid 1f₂₂       = refl
split-valid (0r₂₂ {n}) = cong (λ z → suc (suc (suc z))) (x+1 (2* (toN n)))
split-valid (1r₂₂ {n}) = cong (λ z → suc (suc z)) (x+2 (2* (toN n)))
split-valid ⟪2₂ i 3₂⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₂₃₂ (before i) (after i)
split-valid ⟪3₂ i 2₂⟫
  rewrite sym (split-valid i) | 2*≡+ (before i) | 2*≡+ (after i) | 2*≡+ (before i + suc (after i))
  = a₃₂₂ (before i) (after i)

after-∸ : ∀ {n} (i : Idx n) → toN n ∸ suc (before i) ≡ after i
after-∸ i =
  trans (cong (_∸ suc (before i)) (sym (split-valid i)))
        (trans (cong (_∸ suc (before i)) (NP.+-suc (before i) (after i)))
               (NP.m+n∸m≡n (before i) (after i)))

-- toF is before
toF-before : ∀ {n} (i : Idx n) → toℕ (toF i) ≡ before i
toF-before 0b₁  = refl
toF-before 0f₁₁ = refl
toF-before 0r₁₁ = opposite-prop iz
toF-before ⟪1₁ i 2₁⟫ =
  trans (cong suc (toℕ-inject₁ ((toF i) ∙2+0)))
        (trans (cong suc (toℕ-∙2+0 (toF i))) (cong (λ z → suc (2* z)) (toF-before i)))
toF-before ⟪2₁ i 1₁⟫ =
  trans (cong suc (toℕ-inject₁ ((toF i) ∙2+1)))
        (trans (cong suc (toℕ-∙2+1 (toF i))) (cong (λ z → suc (suc (2* z))) (toF-before i)))
toF-before 0f₁₂ = refl
toF-before 0r₁₂ = opposite-prop iz
toF-before (1r₁₂ {n}) =
  trans (toℕ-inject₁ (fromℕ (suc (2* (toN n))))) (toℕ-fromℕ (suc (2* (toN n))))
toF-before ⟪1₁ i 3₂⟫ =
  trans (cong suc (toℕ-inject₁ (inject₁ ((toF i) ∙2+0))))
        (trans (cong suc (toℕ-inject₁ ((toF i) ∙2+0)))
               (trans (cong suc (toℕ-∙2+0 (toF i))) (cong (λ z → suc (2* z)) (toF-before i))))
toF-before ⟪2₁ i 2₂⟫ =
  trans (cong suc (toℕ-inject₁ (inject₁ ((toF i) ∙2+1))))
        (trans (cong suc (toℕ-inject₁ ((toF i) ∙2+1)))
               (trans (cong suc (toℕ-∙2+1 (toF i))) (cong (λ z → suc (suc (2* z))) (toF-before i))))
toF-before 0f₂₁ = refl
toF-before 1f₂₁ = refl
toF-before 0r₂₁ = opposite-prop iz
toF-before ⟪2₂ i 2₁⟫ =
  trans (cong (λ z → suc (suc z)) (toℕ-inject₁ ((toF i) ∙2+0)))
        (trans (cong (λ z → suc (suc z)) (toℕ-∙2+0 (toF i)))
               (cong (λ z → suc (suc (2* z))) (toF-before i)))
toF-before ⟪3₂ i 1₁⟫ =
  trans (cong (λ z → suc (suc z)) (toℕ-inject₁ ((toF i) ∙2+1)))
        (trans (cong (λ z → suc (suc z)) (toℕ-∙2+1 (toF i)))
               (cong (λ z → suc (suc (suc (2* z)))) (toF-before i)))
toF-before 0f₂₂ = refl
toF-before 1f₂₂ = refl
toF-before 0r₂₂ = opposite-prop iz
toF-before (1r₂₂ {n}) =
  trans (toℕ-inject₁ (fromℕ (suc (suc (2* (toN n)))))) (toℕ-fromℕ (suc (suc (2* (toN n)))))
toF-before ⟪2₂ i 3₂⟫ =
  trans (cong (λ z → suc (suc z)) (toℕ-inject₁ (inject₁ ((toF i) ∙2+0))))
        (trans (cong (λ z → suc (suc z)) (toℕ-inject₁ ((toF i) ∙2+0)))
               (trans (cong (λ z → suc (suc z)) (toℕ-∙2+0 (toF i)))
                      (cong (λ z → suc (suc (2* z))) (toF-before i))))
toF-before ⟪3₂ i 2₂⟫ =
  trans (cong (λ z → suc (suc z)) (toℕ-inject₁ (inject₁ ((toF i) ∙2+1))))
        (trans (cong (λ z → suc (suc z)) (toℕ-inject₁ ((toF i) ∙2+1)))
               (trans (cong (λ z → suc (suc z)) (toℕ-∙2+1 (toF i)))
                      (cong (λ z → suc (suc (suc (2* z)))) (toF-before i))))

toF-after : ∀ {n} (i : Idx n) → toℕ (opposite (toF i)) ≡ after i
toF-after {n} i =
  trans (opposite-prop (toF i))
        (trans (cong (λ x → toN n ∸ suc x) (toF-before i)) (after-∸ i))

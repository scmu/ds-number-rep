module Binary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Binary.PropositionalEquality

-- ℕ functions and lemmas

2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

2*n≢0⇒n≢0 : ∀ {n} → 2* n ≢ 0 → n ≢ 0
2*n≢0⇒n≢0 {zero } neq = neq
2*n≢0⇒n≢0 {suc n} neq ()

1+n≢0 : ∀ {m} → ∀ n → n ≡ suc m → n ≢ 0
1+n≢0 (suc n) p ()

-- Binary numbers

-- Digits (0 or 1)
data Digit : Set where
    D0 : Digit
    D1 : Digit

-- Binary numbers (least significant digit first)
data Binary : Set where
    B0  : Binary                     -- zero
    _⟨_⟩ : Digit → Binary → Binary    -- add a digit on top

------------------------------------------------------------------------
-- Conversion between Binary and ℕ
------------------------------------------------------------------------

-- Digit to ℕ
Dtoℕ : Digit → ℕ
Dtoℕ D0 = 0
Dtoℕ D1 = 1

-- Binary to ℕ
toℕ : Binary → ℕ
toℕ B0        = 0
toℕ (d ⟨ b ⟩) = Dtoℕ d + 2* (toℕ b)

-- Increment: worst case O(log n), amortized O(1)
inc : Binary → Binary
inc B0         = D1 ⟨ B0 ⟩
inc (D0 ⟨ b ⟩) = D1 ⟨ b ⟩
inc (D1 ⟨ b ⟩) = D0 ⟨ inc b ⟩

-- Decrement: worst case O((log n)²), amortized O(log n)
dec : Binary → Binary
dec B0         = B0
dec (D0 ⟨ b ⟩) with toℕ b
... | zero     = B0
... | suc n    = D1 ⟨ dec b ⟩
dec (D1 ⟨ b ⟩) = D0 ⟨ b ⟩

fromℕ : ℕ → Binary
fromℕ zero    = B0
fromℕ (suc n) = inc (fromℕ n)

------------------------------------------------------------------------
-- Correctness lemmas for conversions
------------------------------------------------------------------------

-- Increment corresponds to suc
inc-correct : ∀ b → toℕ (inc b) ≡ suc (toℕ b)
inc-correct B0         = refl
inc-correct (D0 ⟨ b ⟩) = refl
inc-correct (D1 ⟨ b ⟩) = cong 2* (inc-correct b)

-- Decrement corresponds to pred
dec-correct : ∀ b → toℕ (dec b) ≡ pred (toℕ b)
dec-correct B0         = refl
dec-correct (D0 ⟨ b ⟩) with toℕ b | inspect toℕ b
... | zero  | [ eq ]   = refl
... | suc n | [ eq ]   = cong suc (cong 2* (trans (dec-correct b) (cong pred eq)))
dec-correct (D1 ⟨ b ⟩) = refl

-- toℕ is a left-inverse of fromℕ
toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = trans (inc-correct (fromℕ n)) (cong suc (toℕ-fromℕ n))

------------------------------------------------------------------------
-- Properties of Binary representation
------------------------------------------------------------------------

-- Example: zero is not uniquely represented
zero-ambiguous : ∃ λ x → (B0 ≢ x) × (0 ≡ toℕ x )
zero-ambiguous = (D0 ⟨ B0 ⟩) , (λ ()) , refl

-- redundancy: multiple representations map to same ℕ
redundant : ∃₂ λ x y → (x ≢ y) × (toℕ x ≡ toℕ y)
redundant = B0 , zero-ambiguous

------------------------------------------------------------------------
-- Random Access Lists (RAL) indexed by Binary
------------------------------------------------------------------------

-- Some stores data depending on the digit
data Some (A : Set) : Digit → Set where
    zero :     Some A D0
    one  : A → Some A D1

-- RAL indexed by Binary
data RAL (A : Set) : Binary → Set where
    nil  :                                      RAL A B0
    more : ∀ {d b} → Some A d → RAL (A × A) b → RAL A (d ⟨ b ⟩)

-- cons: worst case O(log n), amortized O(1)
cons : ∀ {A b} → A → RAL A b → RAL A (inc b)
cons x nil               = more (one x) nil
cons x (more zero xs)    = more (one x) xs
cons x (more (one y) xs) = more zero (cons (x , y) xs)

-- head: worst case O(log n)
head : ∀ {A b} → RAL A (inc b) → A
head {_} {B0}      (more (one x) xs) = x
head {_} {D0 ⟨ b ⟩} (more (one x) xs) = x
head {_} {D1 ⟨ b ⟩} (more zero xs)    = proj₁ (head xs)

-- head' (with proof of non-emptiness): worst case O(log n)
head' : ∀ {A b} → RAL A b → (toℕ b ≢ 0) → A
head' nil               p = ⊥-elim (p refl)
head' (more zero xs)    p = proj₁ (head' xs (2*n≢0⇒n≢0 p))
head' (more (one x) xs) p = x

-- tail: worst case O(log n), amortized O(1)
-- can be optimized by storing length
tail : ∀ {A b} → RAL A b → RAL A (dec b)
tail {A} {B0}       nil = nil
tail {A} {D0 ⟨ b ⟩} (more zero xs) with toℕ b | inspect toℕ b
... | zero  | [ eq ] = nil
... | suc n | [ eq ] = more (one (proj₂ (head' xs (1+n≢0 (toℕ b) eq)))) (tail xs)
tail {A} {D1 ⟨ b ⟩} (more (one x) xs) = more zero xs

-- Indices for Binary RAL (like Fin for ℕ)

data Idx : Binary → Set where
    _0₀ : ∀ {b} → Idx b → Idx (D0 ⟨ b ⟩)   -- left child
    _1₀ : ∀ {b} → Idx b → Idx (D0 ⟨ b ⟩)   -- right child
    0b₁ : ∀ {b} →         Idx (D1 ⟨ b ⟩)   -- first element
    _1₁ : ∀ {b} → Idx b → Idx (D1 ⟨ b ⟩)   -- left child
    _2₁ : ∀ {b} → Idx b → Idx (D1 ⟨ b ⟩)   -- right child

-- lookup: O(log n)
lookup : ∀ {A b} → RAL A b → Idx b → A
lookup nil               ()
lookup (more zero xs)    (i 0₀) = proj₁ (lookup xs i)
lookup (more zero xs)    (i 1₀) = proj₂ (lookup xs i)
lookup (more (one x) xs) 0b₁    = x
lookup (more (one x) xs) (i 1₁) = proj₁ (lookup xs i)
lookup (more (one x) xs) (i 2₁) = proj₂ (lookup xs i)

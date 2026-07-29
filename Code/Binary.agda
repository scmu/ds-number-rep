module Binary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Binary.PropositionalEquality

2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

2*n≢0⇒n≢0 : ∀ {n} → 2* n ≢ 0 → n ≢ 0
2*n≢0⇒n≢0 {zero } neq = neq
2*n≢0⇒n≢0 {suc n} neq ()

1+n≢0 : ∀ {m} → ∀ n → n ≡ suc m → n ≢ 0
1+n≢0 (suc n) p ()

data Digit : Set where
    D0 : Digit
    D1 : Digit

data Binary : Set where
    B0  : Binary
    _⟨_⟩ : Digit → Binary → Binary

DtoN : Digit → ℕ
DtoN D0 = 0
DtoN D1 = 1

toN : Binary → ℕ
toN B0        = 0
toN (d ⟨ b ⟩) = DtoN d + 2* (toN b)

-- worst case O(log n), amortized O(1)
inc : Binary → Binary
inc B0         = D1 ⟨ B0 ⟩
inc (D0 ⟨ b ⟩) = D1 ⟨ b ⟩
inc (D1 ⟨ b ⟩) = D0 ⟨ inc b ⟩

-- Decrement: worst case O((log n)²), amortized O(log n)
dec : Binary → Binary
dec B0              = B0
dec (D0 ⟨ b ⟩)      = D1 ⟨ dec b ⟩
dec (D1 ⟨ B0 ⟩)     = B0
dec (D1 ⟨ x ⟨ b ⟩ ⟩) = D0 ⟨ (x ⟨ b ⟩) ⟩

fromN : ℕ → Binary
fromN zero    = B0
fromN (suc n) = inc (fromN n)

-- Correctness lemmas

inc-correct : ∀ b → toN (inc b) ≡ suc (toN b)
inc-correct B0         = refl
inc-correct (D0 ⟨ b ⟩) = refl
inc-correct (D1 ⟨ b ⟩) = cong 2* (inc-correct b)

-- toN is a left-inverse of fromN
toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero    = refl
toN-fromN (suc n) = trans (inc-correct (fromN n)) (cong suc (toN-fromN n))

zero-ambiguous : ∃ λ x → (B0 ≢ x) × (0 ≡ toN x )
zero-ambiguous = (D0 ⟨ B0 ⟩) , (λ ()) , refl

redundant : ∃₂ λ x y → (x ≢ y) × (toN x ≡ toN y)
redundant = B0 , zero-ambiguous

data Some (A : Set) : Digit → Set where
    zero :     Some A D0
    one  : A → Some A D1

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

-- tail: worst case O(log n), amortized O(1)
tail : ∀ {A b} → RAL A (inc b) → RAL A b
tail {A} {B0} xs = nil
tail {A} {D0 ⟨ b ⟩} (more (one x) xs) = more zero xs
tail {A} {D1 ⟨ b ⟩} (more zero xs) = more (one (proj₂ (head xs))) (tail xs)

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

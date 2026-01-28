module RedundantBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Auxiliary ℕ functions and lemmas
------------------------------------------------------------------------

2* : ℕ → ℕ
2* zero    = 0
2* (suc n) = suc (suc (2* n))

n≢0⇒1+n-1≡n : ∀ n → n ≢ 0 → suc (pred n) ≡ n
n≢0⇒1+n-1≡n zero    neq = ⊥-elim (neq refl)
n≢0⇒1+n-1≡n (suc n) neq = refl

------------------------------------------------------------------------
-- Redundant binary numbers
------------------------------------------------------------------------

-- Additional digit of 3
data Digit : Set where
    D1 : Digit
    D2 : Digit
    D3 : Digit

-- Redundant binary numbers (least significant digit first)
data Binary : Set where
    B0  : Binary
    _⟨_⟩ : Digit → Binary → Binary

Dtoℕ : Digit → ℕ
Dtoℕ D1 = 1
Dtoℕ D2 = 2
Dtoℕ D3 = 3

toℕ : Binary → ℕ
toℕ B0        = 0
toℕ (d ⟨ b ⟩) = Dtoℕ d + 2* (toℕ b)

-- Increment (carry if digit = D3)
-- Worst case O(log n), amortized O(1)
inc : Binary → Binary
inc B0         = D1 ⟨ B0 ⟩
inc (D1 ⟨ b ⟩) = D2 ⟨ b ⟩
inc (D2 ⟨ b ⟩) = D3 ⟨ b ⟩
inc (D3 ⟨ b ⟩) = D2 ⟨ inc b ⟩

-- Decrement (borrow if digit = D1)
-- Worst case O(log n), amortized O(1)
dec : Binary → Binary
dec B0              = B0
dec (D1 ⟨ B0 ⟩)      = B0
dec (D1 ⟨ d ⟨ b ⟩ ⟩) = D2 ⟨ dec (d ⟨ b ⟩) ⟩
dec (D2 ⟨ b ⟩)       = D1 ⟨ b ⟩
dec (D3 ⟨ b ⟩)       = D2 ⟨ b ⟩

-- Both operations are amortized O(1) over arbitrary sequences
-- After carry/borrow, the outer digit becomes D2, which won't trigger another carry/borrow

fromℕ : ℕ → Binary
fromℕ zero    = B0
fromℕ (suc n) = inc (fromℕ n)

------------------------------------------------------------------------
-- Correctness lemmas for conversions
------------------------------------------------------------------------

non-zero : ∀ {d b} → toℕ (d ⟨ b ⟩) ≢ 0
non-zero {D1} {b} ()
non-zero {D2} {b} ()
non-zero {D3} {b} ()

inc-correct : ∀ b → toℕ (inc b) ≡ suc (toℕ b)
inc-correct B0         = refl
inc-correct (D1 ⟨ b ⟩) = refl
inc-correct (D2 ⟨ b ⟩) = refl
inc-correct (D3 ⟨ b ⟩) = cong suc (cong suc (cong 2* (inc-correct b)))

dec-correct : ∀ b → toℕ (dec b) ≡ pred (toℕ b)
dec-correct B0              = refl
dec-correct (D1 ⟨ B0 ⟩)      = refl
dec-correct (D1 ⟨ d ⟨ b ⟩ ⟩) = cong 2* (trans (cong suc (dec-correct (d ⟨ b ⟩)))
                                             (n≢0⇒1+n-1≡n (Dtoℕ d + 2* (toℕ b)) (non-zero {d} {b})))
dec-correct (D2 ⟨ b ⟩)       = refl
dec-correct (D3 ⟨ b ⟩)       = refl

-- fromℕ is a left-inverse of toℕ
toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = trans (inc-correct (fromℕ n)) (cong suc (toℕ-fromℕ n))

-- Zero is unique
zero-unique : ∀ x → toℕ x ≡ 0 → x ≡ B0
zero-unique B0 refl = refl
zero-unique (D1 ⟨ b ⟩) ()
zero-unique (D2 ⟨ b ⟩) ()
zero-unique (D3 ⟨ b ⟩) ()

-- Redundancy example
redundant : ∃₂ λ x y → (x ≢ y) × (toℕ x ≡ toℕ y )
redundant = (D3 ⟨ B0 ⟩) , ((D1 ⟨ D1 ⟨ B0 ⟩ ⟩) , (λ ()) , refl)

-- Example: dec (inc b) ≢ b
dec-inc≢id : ∃ λ b → b ≢ dec (inc b)
dec-inc≢id = (D3 ⟨ B0 ⟩) , λ ()

-- There are binaries that is not part of inc's result
inc-gap : ∃ λ x → (toℕ x ≢ 0) × (∀ y → x ≢ inc y)
inc-gap = (D1 ⟨ D1 ⟨ B0 ⟩ ⟩) , ((λ ()) , helper)
  where
  helper : ∀ y → D1 ⟨ D1 ⟨ B0 ⟩ ⟩ ≢ inc y
  helper B0        ()
  helper (D1 ⟨ y ⟩) ()
  helper (D2 ⟨ y ⟩) ()
  helper (D3 ⟨ y ⟩) ()

------------------------------------------------------------------------
-- Random Access Lists (RAL) indexed by Redundant binary
------------------------------------------------------------------------

-- Additional three constructor
data Some (A : Set) : Digit → Set where
    one   : A →         Some A D1
    two   : A → A →     Some A D2
    three : A → A → A → Some A D3

data RAL (A : Set) : Binary → Set where
    nil  :                                      RAL A B0
    more : ∀ {d b} → Some A d → RAL (A × A) b → RAL A (d ⟨ b ⟩)

-- O(1), amortized
cons : ∀ {A b} → A → RAL A b → RAL A (inc b)
cons x nil                        = more (one x) nil
cons x (more (one x₁) xs)         = more (two x x₁) xs
cons x (more (two x₁ x₂) xs)      = more (three x x₁ x₂) xs
cons x (more (three x₁ x₂ x₃) xs) = more (two x x₁) (cons (x₂ , x₃) xs)

-- This version does not accept all shapes of RAL due to inc-gap
head : ∀ {A b} → RAL A (inc b) → A
head {_} {B0}      (more (one x) xs)         = x
head {_} {D1 ⟨ b ⟩} (more (two x x₁) xs)      = x
head {_} {D2 ⟨ b ⟩} (more (three x x₁ x₂) xs) = x
head {_} {D3 ⟨ b ⟩} (more (two x x₁) xs)      = x

-- A non-empty RAL cannot have index 0
more≢empty : ∀ {A d b} → RAL A (d ⟨ b ⟩) → (toℕ (d ⟨ b ⟩) ≢ 0)
more≢empty {_} {d} {b} _ p = contradiction (zero-unique (d ⟨ b ⟩) p) λ ()

-- Safe head with explicit proof of non-emptiness
head' : ∀ {A b} → RAL A b → (toℕ b ≢ 0) → A
head' nil p                       = ⊥-elim (p refl)
head' (more (one x) xs) p         = x
head' (more (two x x₁) xs) p      = x
head' (more (three x x₁ x₂) xs) p = x

-- O(1), amortized
tail : ∀ {A b} → RAL A b → RAL A (dec b)
tail nil                       = nil
tail (more (one x) nil)        = nil
tail (more (one x) xs@(more x₁ xs')) =
    let h = head' xs (more≢empty xs)
    in  more (two (proj₁ h) (proj₂ h)) (tail xs)
tail (more (two x x₁) xs)      = more (one x₁) xs
tail (more (three x x₁ x₂) xs) = more (two x₁ x₂) xs

-- Indices

data Idx : Binary → Set where
    0b₁ : ∀ {b} →         Idx (D1 ⟨ b ⟩)
    _1₁ : ∀ {b} → Idx b → Idx (D1 ⟨ b ⟩)
    _2₁ : ∀ {b} → Idx b → Idx (D1 ⟨ b ⟩)
    0b₂ : ∀ {b} →         Idx (D2 ⟨ b ⟩)
    1b₂ : ∀ {b} →         Idx (D2 ⟨ b ⟩)
    _2₂ : ∀ {b} → Idx b → Idx (D2 ⟨ b ⟩)
    _3₂ : ∀ {b} → Idx b → Idx (D2 ⟨ b ⟩)
    0b₃ : ∀ {b} →         Idx (D3 ⟨ b ⟩)
    1b₃ : ∀ {b} →         Idx (D3 ⟨ b ⟩)
    2b₃ : ∀ {b} →         Idx (D3 ⟨ b ⟩)
    _3₃ : ∀ {b} → Idx b → Idx (D3 ⟨ b ⟩)
    _4₃ : ∀ {b} → Idx b → Idx (D3 ⟨ b ⟩)

-- Lookup by index
-- O(log n) worst case
lookup : ∀ {A b} → RAL A b → Idx b → A
lookup nil                        ()
lookup (more (one x) xs)         0b₁    = x
lookup (more (one x) xs)         (i 1₁) = proj₁ (lookup xs i)
lookup (more (one x) xs)         (i 2₁) = proj₂ (lookup xs i)
lookup (more (two x x₁) xs)      0b₂    = x
lookup (more (two x x₁) xs)      1b₂    = x₁
lookup (more (two x x₁) xs)      (i 2₂) = proj₁ (lookup xs i)
lookup (more (two x x₁) xs)      (i 3₂) = proj₂ (lookup xs i)
lookup (more (three x x₁ x₂) xs) 0b₃    = x
lookup (more (three x x₁ x₂) xs) 1b₃    = x₁
lookup (more (three x x₁ x₂) xs) 2b₃    = x₂
lookup (more (three x x₁ x₂) xs) (i 3₃) = proj₁ (lookup xs i)
lookup (more (three x x₁ x₂) xs) (i 4₃) = proj₂ (lookup xs i)

{-
Alternative index choice

data IdxDigit : Digit → Set where
    0₁ : IdxDigit D1
    0₂ : IdxDigit D2
    1₂ : IdxDigit D2
    0₃ : IdxDigit D3
    1₃ : IdxDigit D3
    2₃ : IdxDigit D3

data Idx : Binary → Set where
    here  : ∀ {d b} → IdxDigit d → Idx (d ⟨ b ⟩)
    left  : ∀ {d b} → Idx b →      Idx (d ⟨ b ⟩)
    right : ∀ {d b} → Idx b →      Idx (d ⟨ b ⟩)
-}
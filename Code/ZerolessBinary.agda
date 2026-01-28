module ZerolessBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (suc-injective)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality

-- ℕ functions and lemmas

2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

n≢0⇒1+n-1≡n : ∀ n → n ≢ 0 → suc (pred n) ≡ n
n≢0⇒1+n-1≡n zero    neq = ⊥-elim (neq refl)
n≢0⇒1+n-1≡n (suc n) neq = refl

2*-injective : ∀ {n m} → 2* n ≡ 2* m → n ≡ m
2*-injective {zero}  {zero}  eq = eq
2*-injective {suc n} {suc m} eq =
  cong suc (2*-injective (suc-injective (suc-injective eq)))

even≢odd : ∀ {m n} → 2* m ≡ suc (2* n) → ⊥
even≢odd {suc m} {suc n} eq = even≢odd (suc-injective (suc-injective eq))

-- Zeroless binary numbers

-- Digits (1 or 2)
data Digit : Set where
    D1 : Digit
    D2 : Digit

-- Zeroless binary numbers (least significant digit first)
data Binary : Set where
    B0  : Binary
    _⟨_⟩ : Digit → Binary → Binary

-- Conversion between Zeroless binary and ℕ

-- Digit to ℕ
Dtoℕ : Digit → ℕ
Dtoℕ D1 = 1
Dtoℕ D2 = 2

-- Zeroless binary to ℕ
toℕ : Binary → ℕ
toℕ B0        = 0
toℕ (d ⟨ n ⟩) = Dtoℕ d + 2* (toℕ n)

-- Increment: worst case O(log n), amortized O(1)
inc : Binary → Binary
inc B0         = D1 ⟨ B0 ⟩
inc (D1 ⟨ b ⟩) = D2 ⟨ b ⟩
inc (D2 ⟨ b ⟩) = D1 ⟨ inc b ⟩

-- Decrement: worst case O(log n), amortized O(1)
dec : Binary → Binary
dec B0              = B0
dec (D1 ⟨ B0 ⟩)     = B0
dec (D1 ⟨ d ⟨ b ⟩ ⟩) = D2 ⟨ dec (d ⟨ b ⟩) ⟩
dec (D2 ⟨ b ⟩)      = D1 ⟨ b ⟩

add : Binary → Binary → Binary
add B0 m = m
add (D1 ⟨ n ⟩) m = inc (add n m)
add (D2 ⟨ n ⟩) m = inc (inc (add n m))

fromℕ : ℕ → Binary
fromℕ zero    = B0
fromℕ (suc n) = inc (fromℕ n)

-- Correctness lemmas for conversions

-- No nonzero number is mapped to 0
non-zero : ∀ {d b} → toℕ (d ⟨ b ⟩) ≢ 0
non-zero {D1} {b} ()
non-zero {D2} {b} ()

-- Increment corresponds to suc
inc-correct : ∀ b → toℕ (inc b) ≡ suc (toℕ b)
inc-correct B0         = refl
inc-correct (D1 ⟨ b ⟩) = refl
inc-correct (D2 ⟨ b ⟩) = cong suc (cong 2* (inc-correct b))

-- Decrement corresponds to pred
dec-correct : ∀ b → toℕ (dec b) ≡ pred (toℕ b)
dec-correct B0              = refl
dec-correct (D1 ⟨ B0 ⟩)     = refl
dec-correct (D1 ⟨ d ⟨ b ⟩ ⟩) =
  cong 2* (trans (cong suc (dec-correct (d ⟨ b ⟩)))
                 (n≢0⇒1+n-1≡n (Dtoℕ d + 2* (toℕ b)) (non-zero {d} {b})))
dec-correct (D2 ⟨ b ⟩)      = refl

-- dec is a left-inverse of inc
dec-inc≡id : ∀ b → dec (inc b) ≡ b
dec-inc≡id B0 = refl
dec-inc≡id (D1 ⟨ b ⟩) = refl
dec-inc≡id (D2 ⟨ B0 ⟩) = refl
dec-inc≡id (D2 ⟨ D1 ⟨ b ⟩ ⟩) = refl
dec-inc≡id (D2 ⟨ D2 ⟨ b ⟩ ⟩) = cong (_⟨_⟩ D2) (dec-inc≡id (D2 ⟨ b ⟩))

-- toℕ is a left-inverse of fromℕ
toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) =
  trans (inc-correct (fromℕ n)) (cong suc (toℕ-fromℕ n))

-- Properties of Zeroless binary representation

-- toℕ is injective (no redundancy)
-- Any binary system that uses the digits 0, . . . , a in the leading position and 
-- a+1 and a+2 for the other positions are non-redundant
nonRedundant : ∀ x y → toℕ x ≡ toℕ y → x ≡ y
nonRedundant B0        B0        refl = refl
nonRedundant B0        (D1 ⟨ y ⟩) ()
nonRedundant B0        (D2 ⟨ y ⟩) ()
nonRedundant (D1 ⟨ x ⟩) B0        ()
nonRedundant (D2 ⟨ x ⟩) B0        ()
nonRedundant (D1 ⟨ x ⟩) (D1 ⟨ y ⟩) eq =
  cong (_⟨_⟩ D1) (nonRedundant x y (2*-injective (suc-injective eq)))
nonRedundant (D1 ⟨ x ⟩) (D2 ⟨ y ⟩) eq =
  ⊥-elim (even≢odd (suc-injective eq))
nonRedundant (D2 ⟨ x ⟩) (D1 ⟨ y ⟩) eq =
  ⊥-elim (even≢odd (suc-injective (sym eq)))
nonRedundant (D2 ⟨ x ⟩) (D2 ⟨ y ⟩) eq =
  cong (_⟨_⟩ D2) (nonRedundant x y (2*-injective (suc-injective (suc-injective eq))))

-- toℕ is a right-inverse of fromℕ
fromℕ-toℕ : ∀ b → fromℕ (toℕ b) ≡ b
fromℕ-toℕ B0        = refl
fromℕ-toℕ (D1 ⟨ b ⟩) =
  nonRedundant _ _ (trans (inc-correct (fromℕ (2* (toℕ b))))
                          (cong suc (toℕ-fromℕ (2* (toℕ b)))))
fromℕ-toℕ (D2 ⟨ b ⟩) =
  nonRedundant _ _ (trans (inc-correct (inc (fromℕ (2* (toℕ b)))))
                          (cong suc (trans (inc-correct (fromℕ (2* (toℕ b))))
                                           (cong suc (toℕ-fromℕ (2* (toℕ b)))))))

-- Random Access Lists (RAL) indexed by Zeroless binary

-- Some stores data depending on the digit
data Some (A : Set) : Digit → Set where
    single : A     → Some A D1
    pair   : A → A → Some A D2

-- RAL indexed by Zeroless binary
data RAL (A : Set) : Binary → Set where
    nil  :                                      RAL A B0
    more : ∀ {d b} → Some A d → RAL (A × A) b → RAL A (d ⟨ b ⟩)

-- cons: worst case O(log n), amortized O(1)
cons : ∀ {A b} → A → RAL A b → RAL A (inc b)
cons x nil                    = more (single x) nil
cons x (more (single y) xs)   = more (pair x y) xs
cons x (more (pair y z) xs)   = more (single x) (cons (y , z) xs)

-- head: worst case O(1), better than plain Binary
head : ∀ {A b} → RAL A (inc b) → A
head {_} {B0}       (more (single x) xs)   = x
head {_} {D1 ⟨ b ⟩} (more (pair x _) xs)   = x
head {_} {D2 ⟨ b ⟩} (more (single x) xs)   = x

-- Generalized head (used in tail)
head' : ∀ {A b} → RAL A b → (toℕ b ≢ 0) → A
head' nil                  p = ⊥-elim (p refl)
head' (more (single x) xs) p = x
head' (more (pair x _) xs) p = x

-- Proof: more constructor never empty
more≢empty : ∀ {A d b} → RAL A (d ⟨ b ⟩) → (toℕ (d ⟨ b ⟩) ≢ 0)
more≢empty {_} {d} {b} _ p =
  contradiction (nonRedundant (d ⟨ b ⟩) B0 p) λ ()

-- tail: worst case O(log n)
tail : ∀ {A b} → RAL A b → RAL A (dec b)
tail nil                    = nil
tail (more (single x) nil)  = nil
tail (more (single x) xs@(more _ _)) =
  let h = head' xs (more≢empty xs)
  in  more (pair (proj₁ h) (proj₂ h)) (tail xs)
tail (more (pair _ y) xs)   = more (single y) xs

-- Indices for Zeroless binary RAL

data Idx : Binary → Set where
    0b₁ : ∀ {b} →         Idx (D1 ⟨ b ⟩)   -- first element
    _1₁ : ∀ {b} → Idx b → Idx (D1 ⟨ b ⟩)   -- left child
    _2₁ : ∀ {b} → Idx b → Idx (D1 ⟨ b ⟩)   -- right child
    0b₂ : ∀ {b} →         Idx (D2 ⟨ b ⟩)   -- first element
    1b₂ : ∀ {b} →         Idx (D2 ⟨ b ⟩)   -- second element
    _2₂ : ∀ {b} → Idx b → Idx (D2 ⟨ b ⟩)   -- left child
    _3₂ : ∀ {b} → Idx b → Idx (D2 ⟨ b ⟩)   -- right child
    
-- lookup: O(log n)
lookup : ∀ {A n} → RAL A n → Idx n → A
lookup nil                   ()
lookup (more (single x) xs)  0b₁    = x
lookup (more (single x) xs)  (i 1₁) = proj₁ (lookup xs i)
lookup (more (single x) xs)  (i 2₁) = proj₂ (lookup xs i)
lookup (more (pair x y) xs)  0b₂    = x
lookup (more (pair x y) xs)  1b₂    = y
lookup (more (pair x y) xs)  (i 2₂) = proj₁ (lookup xs i)
lookup (more (pair x y) xs)  (i 3₂) = proj₂ (lookup xs i)

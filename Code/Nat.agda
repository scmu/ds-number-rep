module Nat where

open import Data.Nat using (ℕ; zero; _+_; suc; pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Digit : Set where
    D1 : Digit

data Nat : Set where
    N0  : Nat
    _⟨_⟩ : Digit → Nat → Nat

DtoN : Digit → ℕ
DtoN D1 = 1

toN : Nat → ℕ
toN N0        = 0
toN (d ⟨ n ⟩) = DtoN d + toN n

-- Increment in O(1)
inc : Nat → Nat
inc n = D1 ⟨ n ⟩

-- Decrement in O(1)
dec : Nat → Nat
dec N0        = N0
dec (D1 ⟨ n ⟩) = n

add : Nat → Nat → Nat
add N0 m = m
add (D1 ⟨ n ⟩) m = D1 ⟨ (add n m) ⟩

fromN : ℕ → Nat
fromN zero    = N0
fromN (suc n) = inc (fromN n)

-- Correctness lemmas

-- Increment corresponds to suc
inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
inc-correct n = refl

-- Decrement corresponds to pred
dec-correct : ∀ n → toN (dec n) ≡ pred (toN n)
dec-correct N0        = refl
dec-correct (D1 ⟨ n ⟩) = refl

dec-inc≡id : ∀ n → dec (inc n) ≡ n
dec-inc≡id n = refl

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero    = refl
toN-fromN (suc n) = cong suc (toN-fromN n)

fromN-toN : ∀ n → fromN (toN n) ≡ n
fromN-toN N0        = refl
fromN-toN (D1 ⟨ n ⟩) = cong inc (fromN-toN n)

-- Random Access List (RAL) indexed by Nat

data Some (A : Set) : Digit → Set where
    one : A → Some A D1

data RAL (A : Set) : Nat → Set where
    nil  :                                RAL A N0
    more : ∀ {d n} → Some A d → RAL A n → RAL A (d ⟨ n ⟩)

-- O(1) cons
cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
cons x nil          = more (one x) nil
cons x (more x₁ xs) = more (one x) (more x₁ xs)

-- O(1) head
head : ∀ {A n} → RAL A (inc n) → A
head (more (one x) xs) = x

-- O(1) tail
tail : ∀ {A n} → RAL A (inc n) → RAL A n
tail (more x xs) = xs

-- O(n) append
append : ∀ {A n m} → RAL A n → RAL A m → RAL A (add n m)
append nil               ys = ys
append (more (one x) xs) ys = more (one x) (append xs ys)

-- Indices for RAL (analogous to Fin for Nat)

data Idx : Nat → Set where
    0n₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩)
    _1₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)

-- Lookup in O(n)
lookup : ∀ {A n} → RAL A n → Idx n → A
lookup nil ()
lookup (more (one x) xs) 0n₁    = x
lookup (more (one x) xs) (i 1₁) = lookup xs i

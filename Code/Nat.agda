module Nat where

open import Data.Nat using (ℕ; zero; _+_; suc; pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Natural numbers in a unary number representation

-- Digit (1 only)
data Digit : Set where
    D1 : Digit

-- Natural numbers built from digits
data Nat : Set where
    N0  : Nat                     -- zero
    _⟨_⟩ : Digit → Nat → Nat       -- add a digit on top

-- Conversion between Nat and ℕ

-- Digit to ℕ
Dtoℕ : Digit → ℕ
Dtoℕ D1 = 1

-- Nat to ℕ
toℕ : Nat → ℕ
toℕ N0        = 0
toℕ (d ⟨ n ⟩) = Dtoℕ d + toℕ n

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

-- Build a Nat from ℕ
fromℕ : ℕ → Nat
fromℕ zero    = N0
fromℕ (suc n) = inc (fromℕ n)

-- Correctness lemmas

-- Increment corresponds to suc
inc-correct : ∀ n → toℕ (inc n) ≡ suc (toℕ n)
inc-correct n = refl

-- Decrement corresponds to pred
dec-correct : ∀ n → toℕ (dec n) ≡ pred (toℕ n)
dec-correct N0        = refl
dec-correct (D1 ⟨ n ⟩) = refl

-- Decrement after increment cancels out
dec-inc≡id : ∀ n → dec (inc n) ≡ n
dec-inc≡id n = refl

-- toℕ is a left-inverse of fromℕ
toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = cong suc (toℕ-fromℕ n)

-- toℕ is a right-inverse of fromℕ
fromℕ-toℕ : ∀ n → fromℕ (toℕ n) ≡ n
fromℕ-toℕ N0        = refl
fromℕ-toℕ (D1 ⟨ n ⟩) = cong inc (fromℕ-toℕ n)

-- Random Access List (RAL) indexed by Nat
-- Behaves like a length-indexed vector

-- A "Some" tuple stores one element per digit
data Some (A : Set) : Digit → Set where
    one : A → Some A D1

-- Random-access list indexed by Nat
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

-- O(1) tail (equivalent to dec on the length index)
tail : ∀ {A n} → RAL A n → RAL A (dec n)
tail nil                  = nil
tail (more (one x) xs) = xs

append : ∀ {A n m} → RAL A n → RAL A m → RAL A (add n m)
append nil ys = ys
append (more (one x) xs) ys = more (one x) (append xs ys)

-- Indices for RAL (analogous to Fin for Nat)

data Idx : Nat → Set where
    0n₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩)   -- zero index
    _1₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)   -- successor index

-- Lookup in O(n)
lookup : ∀ {A n} → RAL A n → Idx n → A
lookup nil ()
lookup (more (one x) xs) 0n₁    = x
lookup (more (one x) xs) (i 1₁) = lookup xs i

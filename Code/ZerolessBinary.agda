module ZerolessBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to iz; suc to is)
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
DtoN : Digit → ℕ
DtoN D1 = 1
DtoN D2 = 2

-- Zeroless binary to ℕ
toN : Binary → ℕ
toN B0        = 0
toN (d ⟨ n ⟩) = DtoN d + 2* (toN n)

-- Increment: worst case O(log n), amortized O(1)
inc : Binary → Binary
inc B0         = D1 ⟨ B0 ⟩
inc (D1 ⟨ n ⟩) = D2 ⟨ n ⟩
inc (D2 ⟨ n ⟩) = D1 ⟨ inc n ⟩

-- Decrement: worst case O(log n), amortized O(1)
dec : Binary → Binary
dec B0              = B0
dec (D1 ⟨ B0 ⟩)     = B0
dec (D1 ⟨ d ⟨ n ⟩ ⟩) = D2 ⟨ dec (d ⟨ n ⟩) ⟩
dec (D2 ⟨ n ⟩)      = D1 ⟨ n ⟩

-- add : Binary → Binary → Binary
-- add B0 m = m
-- add (D1 ⟨ n ⟩) m = inc (add n m)
-- add (D2 ⟨ n ⟩) m = inc (inc (add n m))

fromN : ℕ → Binary
fromN zero    = B0
fromN (suc n) = inc (fromN n)

-- Correctness lemmas for conversions

-- No nonzero number is mapped to 0
non-zero : ∀ d n → toN (d ⟨ n ⟩) ≢ 0
non-zero D1 n ()
non-zero D2 n ()

-- Increment corresponds to suc
inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
inc-correct B0         = refl
inc-correct (D1 ⟨ n ⟩) = refl
inc-correct (D2 ⟨ n ⟩) = cong suc (cong 2* (inc-correct n))

-- Decrement corresponds to pred
dec-correct : ∀ n → toN (dec n) ≡ pred (toN n)
dec-correct B0              = refl
dec-correct (D1 ⟨ B0 ⟩)     = refl
dec-correct (D1 ⟨ d ⟨ n ⟩ ⟩) = 
    cong 2* (trans (cong suc (dec-correct (d ⟨ n ⟩))) 
                   (n≢0⇒1+n-1≡n (DtoN d + 2* (toN n)) (non-zero d n)))
dec-correct (D2 ⟨ n ⟩)      = refl

-- dec is a left-inverse of inc
dec-inc≡id : ∀ n → dec (inc n) ≡ n
dec-inc≡id B0 = refl
dec-inc≡id (D1 ⟨ n ⟩) = refl
dec-inc≡id (D2 ⟨ B0 ⟩) = refl
dec-inc≡id (D2 ⟨ D1 ⟨ n ⟩ ⟩) = refl
dec-inc≡id (D2 ⟨ D2 ⟨ n ⟩ ⟩) = cong (_⟨_⟩ D2) (dec-inc≡id (D2 ⟨ n ⟩))

-- toN is a left-inverse of fromN
toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero    = refl
toN-fromN (suc n) =
    trans (inc-correct (fromN n)) (cong suc (toN-fromN n))

-- Properties of Zeroless binary representation

-- toN is injective (no redundancy)
-- Any binary system that uses the digits 0, . . . , a in the leading position and 
-- a+1 and a+2 for the other positions are non-redundant
nonRedundant : ∀ x y → toN x ≡ toN y → x ≡ y
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

-- toN is a right-inverse of fromN
fromN-toN : ∀ n → fromN (toN n) ≡ n
fromN-toN B0        = refl
fromN-toN (D1 ⟨ n ⟩) =
    nonRedundant _ _ (trans (inc-correct (fromN (2* (toN n))))
                            (cong suc (toN-fromN (2* (toN n)))))
fromN-toN (D2 ⟨ n ⟩) = 
    nonRedundant _ _ (trans (inc-correct (inc (fromN (2* (toN n)))))
                            (cong suc (trans (inc-correct (fromN (2* (toN n))))
                                             (cong suc (toN-fromN (2* (toN n)))))))

data Peano-View : Binary → Set where
    as-zero : Peano-View B0
    as-succ : (i : Binary) → Peano-View (inc i)

view : ∀ n → Peano-View n
view B0 = as-zero
view (D1 ⟨ n ⟩) with view n
... | as-zero = as-succ B0
... | as-succ m = as-succ (D2 ⟨ m ⟩)
view (D2 ⟨ n ⟩) = as-succ (D1 ⟨ n ⟩)

VtoN : ∀ {n} → Peano-View n → ℕ
VtoN as-zero = 0
VtoN (as-succ n) = suc (toN n)

view-correct : ∀ n → VtoN (view n) ≡ toN n
view-correct B0 = refl
view-correct (D1 ⟨ n ⟩) with view n
... | as-zero = refl
... | as-succ m = cong suc (cong 2* (sym (inc-correct m)))
view-correct (D2 ⟨ n ⟩) = refl

-- Random Access Lists (RAL) indexed by Zeroless binary

-- Some stores data depending on the digit
data Some (A : Set) : Digit → Set where
    single : A     → Some A D1
    pair   : A → A → Some A D2

-- RAL indexed by Zeroless binary
data RAL (A : Set) : Binary → Set where
    nil  :                                      RAL A B0
    more : ∀ {d n} → Some A d → RAL (A × A) n → RAL A (d ⟨ n ⟩)

-- cons: worst case O(log n), amortized O(1)
cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
cons x nil                    = more (single x) nil
cons x (more (single y) xs)   = more (pair x y) xs
cons x (more (pair y z) xs)   = more (single x) (cons (y , z) xs)

-- head: worst case O(1), better than plain Binary
head : ∀ {A n} → RAL A (inc n) → A
head {_} {B0}       (more (single x) xs)   = x
head {_} {D1 ⟨ n ⟩} (more (pair x _) xs)   = x
head {_} {D2 ⟨ n ⟩} (more (single x) xs)   = x

-- Generalized head (used in tail)
head' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head' nil                  p = ⊥-elim (p refl)
head' (more (single x) xs) p = x
head' (more (pair x _) xs) p = x

-- Proof: more constructor never empty
more≢empty : ∀ {A d n} → RAL A (d ⟨ n ⟩) → (toN (d ⟨ n ⟩) ≢ 0)
more≢empty {_} {d} {n} _ p =
  contradiction (nonRedundant (d ⟨ n ⟩) B0 p) λ ()

-- tail: worst case O(log n)
tail : ∀ {A n} → RAL A n → RAL A (dec n)
tail nil                    = nil
tail (more (single x) nil)  = nil
tail (more (single x) xs@(more _ _)) =
    let h = head' xs (more≢empty xs)
    in  more (pair (proj₁ h) (proj₂ h)) (tail xs)
tail (more (pair _ y) xs)   = more (single y) xs

-- Indices for Zeroless binary RAL

_∙2+0 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+0 = iz
is i ∙2+0 = is (is (i ∙2+0))

_∙2+1 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+1 = is iz
is i ∙2+1 = is (is (i ∙2+1))

_/2 : ∀ {n} → Fin (2* n) → (Fin n × Fin 2)
_/2 {suc n} iz = iz , iz
_/2 {suc n} (is iz) = iz , is iz
_/2 {suc n} (is (is i)) with i /2
... | q , r = (is q) , r

data Idx : Binary → Set where
    0b₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩)   -- first element
    _1₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)   -- left child
    _2₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)   -- right child
    0b₂ : ∀ {n} →         Idx (D2 ⟨ n ⟩)   -- first element
    1b₂ : ∀ {n} →         Idx (D2 ⟨ n ⟩)   -- second element
    _2₂ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩)   -- left child
    _3₂ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩)   -- right child
    
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

toF : ∀ {n} → Idx n → Fin (toN n)
toF 0b₁ = iz
toF (i 1₁) = is ((toF i) ∙2+0)
toF (i 2₁) = is ((toF i) ∙2+1)
toF 0b₂ = iz
toF 1b₂ = is iz
toF (i 2₂) = is (is ((toF i) ∙2+0))
toF (i 3₂) = is (is ((toF i) ∙2+1))

fromF : ∀ {n} → Fin (toN n) → Idx n
fromF {D1 ⟨ n ⟩} iz = 0b₁
fromF {D1 ⟨ n ⟩} (is i) with i /2
... | j , iz = (fromF j) 1₁
... | j , is iz = (fromF j) 2₁
fromF {D2 ⟨ n ⟩} iz = 0b₂
fromF {D2 ⟨ n ⟩} (is iz) = 1b₂
fromF {D2 ⟨ n ⟩} (is (is i)) with i /2
... | j , iz = (fromF j) 2₂
... | j , is iz = (fromF j) 3₂

izero : ∀ {n} → Idx (inc n)
izero {B0} = 0b₁
izero {D1 ⟨ n ⟩} = 0b₂
izero {D2 ⟨ n ⟩} = 0b₁

isucc : ∀ {n} → Idx n → Idx (inc n)
isucc 0b₁ = 1b₂
isucc (i 1₁) = i 2₂
isucc (i 2₁) = i 3₂
isucc 0b₂ = izero 1₁
isucc 1b₂ = izero 2₁
isucc (i 2₂) = (isucc i) 1₁
isucc (i 3₂) = (isucc i) 2₁

-- izero-correct : ∀ {n} → toF izero  ≡ iz
-- isucc-correct : ∀ {n} → (i : Idx n) → toF (isucc i) ≡ is (toF i)

{-
getIdx : ∀ n → ℕ → Idx (fromN (suc n))
getIdx n zero = izero
getIdx zero (suc i) = 0b₁
getIdx (suc n) (suc i) = isucc (getIdx n i)

Idx (D1 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ ⟩ ⟩)
index 0 : 0b₁
index 1 : 0b₂ 1₁
index 2 : 0b₂ 2₁
index 3 : 1b₂ 1₁
index 4 : 1b₂ 2₁
index 5 : 0b₁ 2₂ 1₁
index 6 : 0b₁ 2₂ 2₁
index 7 : 0b₁ 3₂ 1₁
index 8 : 0b₁ 3₂ 2₁
-}
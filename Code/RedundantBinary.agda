module RedundantBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to iz; suc to is)
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

DtoN : Digit → ℕ
DtoN D1 = 1
DtoN D2 = 2
DtoN D3 = 3

toN : Binary → ℕ
toN B0        = 0
toN (d ⟨ b ⟩) = DtoN d + 2* (toN b)

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

fromN : ℕ → Binary
fromN zero    = B0
fromN (suc n) = inc (fromN n)

------------------------------------------------------------------------
-- Correctness lemmas for conversions
------------------------------------------------------------------------

non-zero : ∀ d b → toN (d ⟨ b ⟩) ≢ 0
non-zero D1 b ()
non-zero D2 b ()
non-zero D3 b ()

inc-correct : ∀ b → toN (inc b) ≡ suc (toN b)
inc-correct B0         = refl
inc-correct (D1 ⟨ b ⟩) = refl
inc-correct (D2 ⟨ b ⟩) = refl
inc-correct (D3 ⟨ b ⟩) = cong suc (cong suc (cong 2* (inc-correct b)))

dec-correct : ∀ b → toN (dec b) ≡ pred (toN b)
dec-correct B0              = refl
dec-correct (D1 ⟨ B0 ⟩)      = refl
dec-correct (D1 ⟨ d ⟨ b ⟩ ⟩) = cong 2* (trans (cong suc (dec-correct (d ⟨ b ⟩)))
                                             (n≢0⇒1+n-1≡n (DtoN d + 2* (toN b)) (non-zero d b)))
dec-correct (D2 ⟨ b ⟩)       = refl
dec-correct (D3 ⟨ b ⟩)       = refl

-- fromN is a left-inverse of toN
toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero    = refl
toN-fromN (suc n) = trans (inc-correct (fromN n)) (cong suc (toN-fromN n))

-- Zero is unique
zero-unique : ∀ x → toN x ≡ 0 → x ≡ B0
zero-unique B0 refl = refl
zero-unique (D1 ⟨ b ⟩) ()
zero-unique (D2 ⟨ b ⟩) ()
zero-unique (D3 ⟨ b ⟩) ()

-- Redundancy example
redundant : ∃₂ λ x y → (x ≢ y) × (toN x ≡ toN y )
redundant = (D3 ⟨ B0 ⟩) , ((D1 ⟨ D1 ⟨ B0 ⟩ ⟩) , (λ ()) , refl)

-- Example: dec (inc b) ≢ b
dec-inc≢id : ∃ λ b → b ≢ dec (inc b)
dec-inc≢id = (D3 ⟨ B0 ⟩) , λ ()

-- There are binaries that is not part of inc's result
inc-gap : ∃ λ x → (toN x ≢ 0) × (∀ y → x ≢ inc y)
inc-gap = (D1 ⟨ D1 ⟨ B0 ⟩ ⟩) , ((λ ()) , helper)
    where
        helper : ∀ y → D1 ⟨ D1 ⟨ B0 ⟩ ⟩ ≢ inc y
        helper B0        ()
        helper (D1 ⟨ y ⟩) ()
        helper (D2 ⟨ y ⟩) ()
        helper (D3 ⟨ y ⟩) ()

inc≢0 : ∀ n → inc n ≢ B0
inc≢0 B0 = λ ()
inc≢0 (D1 ⟨ n ⟩) = λ ()
inc≢0 (D2 ⟨ n ⟩) = λ ()
inc≢0 (D3 ⟨ n ⟩) = λ ()

data Peano-View : Binary → Set where
    as-zero : Peano-View B0
    as-succ : ∀ {n} → (i : Binary) → (p : suc (toN i) ≡ toN n) → Peano-View n

view : ∀ n → Peano-View n
view B0 = as-zero
view (d ⟨ n ⟩) = as-succ (dec (d ⟨ n ⟩)) (trans (cong suc (dec-correct (d ⟨ n ⟩))) (n≢0⇒1+n-1≡n (toN (d ⟨ n ⟩)) (non-zero d n)))

VtoN : ∀ {n} → Peano-View n → ℕ
VtoN as-zero = 0
VtoN (as-succ n p) = suc (toN n)

view-correct : ∀ n → VtoN (view n) ≡ toN n
view-correct B0 = refl
view-correct (d ⟨ n ⟩) = trans (cong suc (dec-correct (d ⟨ n ⟩))) (n≢0⇒1+n-1≡n (toN (d ⟨ n ⟩)) (non-zero d n))

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
more≢empty : ∀ {A d b} → RAL A (d ⟨ b ⟩) → (toN (d ⟨ b ⟩) ≢ 0)
more≢empty {_} {d} {b} _ p = contradiction (zero-unique (d ⟨ b ⟩) p) λ ()

-- Safe head with explicit proof of non-emptiness
head' : ∀ {A b} → RAL A b → (toN b ≢ 0) → A
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

toF : ∀ {n} → Idx n → Fin (toN n)
toF 0b₁ = iz
toF (i 1₁) = is ((toF i) ∙2+0)
toF (i 2₁) = is ((toF i) ∙2+1)
toF 0b₂ = iz
toF 1b₂ = is iz
toF (i 2₂) = is (is ((toF i) ∙2+0))
toF (i 3₂) = is (is ((toF i) ∙2+1))
toF 0b₃ = iz
toF 1b₃ = is iz
toF 2b₃ = is (is iz)
toF (i 3₃) = is (is (is ((toF i) ∙2+0)))
toF (i 4₃) = is (is (is ((toF i) ∙2+1)))

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
fromF {D3 ⟨ n ⟩} iz = 0b₃
fromF {D3 ⟨ n ⟩} (is iz) = 1b₃
fromF {D3 ⟨ n ⟩} (is (is iz)) = 2b₃
fromF {D3 ⟨ n ⟩} (is (is (is i))) with i /2
... | j , iz = (fromF j) 3₃
... | j , is iz = (fromF j) 4₃

izero : ∀ {n} → (n ≢ B0) → Idx n
izero {B0} nz = ⊥-elim (nz refl)
izero {D1 ⟨ n ⟩} nz = 0b₁
izero {D2 ⟨ n ⟩} nz = 0b₂
izero {D3 ⟨ n ⟩} nz = 0b₃

isucc : ∀ {n} → Idx n → Idx (inc n)
isucc 0b₁ = 1b₂
isucc (i 1₁) = i 2₂
isucc (i 2₁) = i 3₂
isucc 0b₂ = 1b₃
isucc 1b₂ = 2b₃
isucc (i 2₂) = i 3₃
isucc (i 3₂) = i 3₃
isucc 0b₃ = 1b₂
isucc {D3 ⟨ b ⟩} 1b₃ = (izero (inc≢0 b)) 2₂
isucc {D3 ⟨ b ⟩} 2b₃ = (izero (inc≢0 b)) 3₂
isucc (i 3₃) = (isucc i) 2₂
isucc (i 4₃) = (isucc i) 3₂

-- izero-correct : ∀ {n} → toF izero  ≡ iz
-- isucc-correct : ∀ {n} → (i : Idx n) → toF (isucc i) ≡ is (toF i)
-- ipred-correct : ∀ {n} → (i : Idx n) → toF (ipred i) ≡ ? (toF i)

{-
Idx (D1 ⟨ D3 ⟨ B0 ⟩ ⟩)
index 0 : 0b₁
index 1 : 0b₃ 1₁
index 2 : 0b₃ 2₁
index 3 : 1b₃ 1₁
index 4 : 1b₃ 2₁
index 5 : 2b₃ 1₁
index 6 : 2b₃ 2₁

fromF {D1 ⟨ D3 ⟨ B0 ⟩ ⟩} (is (is (is (is iz))))
-}
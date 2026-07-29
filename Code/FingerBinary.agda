module FingerBinary where

open import Data.Nat using (ℕ; zero; suc; pred; _∸_; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; n∸n≡0; m+n∸m≡n; m+[n∸m]≡n; ≤-refl; ≤-trans; m≤m+n)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Fin using (Fin; splitAt) renaming (zero to iz; suc to is)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)

-- ℕ functions and lemmas

2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

data Frac : ℕ -> Set where
    one : Frac 0
    [_+_]/2 : ∀ {n} → Frac n → Frac n → Frac (suc n)
    [_+_+_]/2 : ∀ {n} → Frac n → Frac n → Frac n → Frac (suc n)

data Digit : ℕ → Set where
    D1 : ∀ {n} → Frac n                   → Digit n
    D2 : ∀ {n} → Frac n → Frac n          → Digit n
    D3 : ∀ {n} → Frac n → Frac n → Frac n → Digit n

data Binary : ℕ → Set where
    B0 : ∀ {n} → Binary n
    B1 : ∀ {n} → Frac n → Binary n
    _⟨_⟩_ : ∀ {n} → Digit n → Binary (suc n) → Digit n → Binary n

incL' : ∀ {n} → Frac n → Binary n → Binary n
incL' f B0 = B1 f
incL' f (B1 f₁) = (D1 f) ⟨ B0 ⟩ (D1 f₁)
incL' f (D1 f₁ ⟨ b ⟩ d) = (D2 f f₁) ⟨ b ⟩ d
incL' f (D2 f₁ f₂ ⟨ b ⟩ d) = (D3 f f₁ f₂) ⟨ b ⟩ d
incL' f (D3 f₁ f₂ f₃ ⟨ b ⟩ d) = (D2 f f₁) ⟨ (incL' [ f₂ + f₃ ]/2 b) ⟩ d

incL : Binary 0 → Binary 0
incL b = incL' one b

incR' : ∀ {n} → Binary n → Frac n → Binary n
incR' B0 f = B1 f
incR' (B1 f₁) f = (D1 f₁) ⟨ B0 ⟩ (D1 f)
incR' (d ⟨ b ⟩ D1 f₁) f = d ⟨ b ⟩ (D2 f₁ f)
incR' (d ⟨ b ⟩ D2 f₁ f₂) f = d ⟨ b ⟩ (D3 f₁ f₂ f)
incR' (d ⟨ b ⟩ D3 f₁ f₂ f₃) f = d ⟨ (incR' b [ f₁ + f₂ ]/2) ⟩ (D2 f₃ f)

incR : Binary 0 → Binary 0
incR b = incR' b one

decL : ∀ {n} → Binary n → Binary n
decL B0 = B0
decL (B1 f) = B0
decL (D2 f f₁ ⟨ b ⟩ d) = D1 f₁ ⟨ b ⟩ d
decL (D3 f f₁ f₂ ⟨ b ⟩ d) = (D2 f₁ f₂) ⟨ b ⟩ d
decL (D1 f ⟨ B0 ⟩ D1 f₁) = B1 f₁
decL (D1 f ⟨ B0 ⟩ D2 f₁ f₂) = (D1 f₁) ⟨ B0 ⟩ (D1 f₂)
decL (D1 f ⟨ B0 ⟩ D3 f₁ f₂ f₃) = (D1 f₁) ⟨ B0 ⟩ (D2 f₂ f₃)
decL (D1 f ⟨ B1 [ f₁ + f₂ ]/2 ⟩ d) = (D2 f₁ f₂) ⟨ B0 ⟩ d
decL (D1 f ⟨ B1 [ f₁ + f₂ + f₃ ]/2 ⟩ d) = (D3 f₁ f₂ f₃) ⟨ B0 ⟩ d
decL (D1 f ⟨ m@(D1 [ f₁ + f₂ ]/2 ⟨ b ⟩ dr) ⟩ d) = (D2 f₁ f₂) ⟨ (decL m) ⟩ d
decL (D1 f ⟨ m@(D1 [ f₁ + f₂ + f₃ ]/2 ⟨ b ⟩ dr) ⟩ d) = (D3 f₁ f₂ f₃) ⟨ (decL m) ⟩ d
decL (D1 f ⟨ m@(D2 [ f₁ + f₂ ]/2 f₃ ⟨ b ⟩ dr) ⟩ d) = (D2 f₁ f₂) ⟨ decL m ⟩ d
decL (D1 f ⟨ m@(D2 [ f₁ + f₂ + f₃ ]/2 f₄ ⟨ b ⟩ dr) ⟩ d) = (D3 f₁ f₂ f₃) ⟨ decL m ⟩ d
decL (D1 f ⟨ m@(D3 [ f₁ + f₂ ]/2 f₃ f₄ ⟨ b ⟩ dr) ⟩ d) = (D2 f₁ f₂) ⟨ decL m ⟩ d
decL (D1 f ⟨ m@(D3 [ f₁ + f₂ + f₃ ]/2 f₄ f₅ ⟨ b ⟩ dr) ⟩ d) = (D3 f₁ f₂ f₃) ⟨ decL m ⟩ d

data Digit' : ℕ → Set where
    D0 : ∀ {n} → Digit' n
    D1 : ∀ {n} → Frac n → Digit' n
    D2 : ∀ {n} → Frac n → Frac n → Digit' n
    D3 : ∀ {n} → Frac n → Frac n → Frac n → Digit' n

addD'L : ∀ {n} → Digit' n → Binary n → Binary n
addD'L D0 b = b
addD'L (D1 f) b = incL' f b
addD'L (D2 f f₁) b = incL' f (incL' f₁ b)
addD'L (D3 f f₁ f₂) b = incL' f (incL' f₁ (incL' f₂ b))

addD'R : ∀ {n} → Binary n → Digit' n → Binary n
addD'R b D0 = b
addD'R b (D1 f) = incR' b f
addD'R b (D2 f f₁) = incR' (incR' b f) f₁
addD'R b (D3 f f₁ f₂) = incR' (incR' (incR' b f) f₁) f₂

combineDigits : ∀ {n} → Digit n → Digit' n → Digit n → Digit' (suc n)
combineDigits (D1 f)       D0            (D1 f₁)       = D1 [ f + f₁ ]/2
combineDigits (D1 f)       D0            (D2 f₁ f₂)    = D1 [ f + f₁ + f₂ ]/2
combineDigits (D1 f)       D0            (D3 f₁ f₂ f₃) = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D1 f)       (D1 f₁)       (D1 f₂)       = D1 [ f + f₁ + f₂ ]/2
combineDigits (D1 f)       (D1 f₁)       (D2 f₂ f₃)    = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D1 f)       (D1 f₁)       (D3 f₂ f₃ f₄) = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D1 f)       (D2 f₁ f₂)    (D1 f₃)       = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D1 f)       (D2 f₁ f₂)    (D2 f₃ f₄)    = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D1 f)       (D2 f₁ f₂)    (D3 f₃ f₄ f₅) = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D1 f)       (D3 f₁ f₂ f₃) (D1 f₄)       = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D1 f)       (D3 f₁ f₂ f₃) (D2 f₄ f₅)    = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D1 f)       (D3 f₁ f₂ f₃) (D3 f₄ f₅ f₆) = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D2 f f₁)    D0            (D1 f₂)       = D1 [ f + f₁ + f₂ ]/2
combineDigits (D2 f f₁)    D0            (D2 f₂ f₃)    = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D2 f f₁)    D0            (D3 f₂ f₃ f₄) = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D2 f f₁)    (D1 f₂)       (D1 f₃)       = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D2 f f₁)    (D1 f₂)       (D2 f₃ f₄)    = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D2 f f₁)    (D1 f₂)       (D3 f₃ f₄ f₅) = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D2 f f₁)    (D2 f₂ f₃)    (D1 f₄)       = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D2 f f₁)    (D2 f₂ f₃)    (D2 f₄ f₅)    = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D2 f f₁)    (D2 f₂ f₃)    (D3 f₄ f₅ f₆) = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D2 f f₁)    (D3 f₂ f₃ f₄) (D1 f₅)       = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D2 f f₁)    (D3 f₂ f₃ f₄) (D2 f₅ f₆)    = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D2 f f₁)    (D3 f₂ f₃ f₄) (D3 f₅ f₆ f₇) = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2 [ f₆ + f₇ ]/2
combineDigits (D3 f f₁ f₂) D0            (D1 f₃)       = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D3 f f₁ f₂) D0            (D2 f₃ f₄)    = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D3 f f₁ f₂) D0            (D3 f₃ f₄ f₅) = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D3 f f₁ f₂) (D1 f₃)       (D1 f₄)       = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2
combineDigits (D3 f f₁ f₂) (D1 f₃)       (D2 f₄ f₅)    = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D3 f f₁ f₂) (D1 f₃)       (D3 f₄ f₅ f₆) = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D3 f f₁ f₂) (D2 f₃ f₄)    (D1 f₅)       = D2 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2
combineDigits (D3 f f₁ f₂) (D2 f₃ f₄)    (D2 f₅ f₆)    = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D3 f f₁ f₂) (D2 f₃ f₄)    (D3 f₅ f₆ f₇) = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2 [ f₆ + f₇ ]/2
combineDigits (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D1 f₆)       = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D2 f₆ f₇)    = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2 [ f₆ + f₇ ]/2
combineDigits (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D3 f₆ f₇ f₈) = D3 [ f + f₁ + f₂ ]/2 [ f₃ + f₄ + f₅ ]/2 [ f₆ + f₇ + f₈ ]/2

add3 : ∀ {n} → Binary n → Digit' n → Binary n → Binary n
add3 B0           d y            = addD'L d y
add3 (B1 f)       d y            = incL' f (addD'L d y)
add3 (xf ⟨ x ⟩ xr) d B0           = addD'R (xf ⟨ x ⟩ xr) d
add3 (xf ⟨ x ⟩ xr) d (B1 f)       = incR' (addD'R (xf ⟨ x ⟩ xr) d) f
add3 (xf ⟨ x ⟩ xr) d (yf ⟨ y ⟩ yr) = xf ⟨ (add3 x (combineDigits xr d yf) y) ⟩ yr

add : Binary 0 → Binary 0 → Binary 0
add x y = add3 x D0 y

data Tree (A : Set) : (n : ℕ) → Frac n → Set where
    leaf  : A → Tree A 0 one
    node2 : ∀ {n} {f₁ f₂ : Frac n}    → Tree A n f₁ → Tree A n f₂               → Tree A (suc n) [ f₁ + f₂ ]/2
    node3 : ∀ {n} {f₁ f₂ f₃ : Frac n} → Tree A n f₁ → Tree A n f₂ → Tree A n f₃ → Tree A (suc n) [ f₁ + f₂ + f₃ ]/2

data Some (A : Set) (n : ℕ) : Digit n → Set where
    one   : ∀ {f₁ : Frac n}       → Tree A n f₁                             → Some A n (D1 f₁)
    two   : ∀ {f₁ f₂ : Frac n}    → Tree A n f₁ → Tree A n f₂               → Some A n (D2 f₁ f₂)
    three : ∀ {f₁ f₂ f₃ : Frac n} → Tree A n f₁ → Tree A n f₂ → Tree A n f₃ → Some A n (D3 f₁ f₂ f₃)

data FingerTree (A : Set) (n : ℕ) : Binary n → Set where
    nil : FingerTree A n B0
    singleton : ∀ {f : Frac n} → Tree A n f → FingerTree A n (B1 f)
    more : ∀ {df dr : Digit n} {b : Binary (suc n)}→ 
        Some A n df → FingerTree A (suc n) b → Some A n dr → FingerTree A n (df ⟨ b ⟩ dr)

cons' : ∀ {A n b f} → Tree A n f → FingerTree A n b → FingerTree A n (incL' f b)
cons' x nil = singleton x
cons' x (singleton x₁) = more (one x) nil (one x₁)
cons' x (more (one x₁) xs r) = more (two x x₁) xs r
cons' x (more (two x₁ x₃) xs r) = more (three x x₁ x₃) xs r
cons' x (more (three x₁ x₃ x₄) xs r) = more (two x x₁) (cons' (node2 x₃ x₄) xs) r

cons : ∀ {A b} → A → FingerTree A 0 b → FingerTree A 0 (incL b)
cons x xs = cons' (leaf x) xs

snoc' : ∀ {A n b f} → FingerTree A n b → Tree A n f → FingerTree A n (incR' b f)
snoc' nil x = singleton x
snoc' (singleton x₁) x = more (one x₁) nil (one x)
snoc' (more f xs (one x₁)) x = more f xs (two x₁ x)
snoc' (more f xs (two x₁ x₂)) x = more f xs (three x₁ x₂ x)
snoc' (more f xs (three x₁ x₂ x₃)) x = more f (snoc' xs (node2 x₁ x₂)) (two x₃ x)

head : ∀ {A b} → FingerTree A 0 b → (b ≢ B0) → A
head nil p = ⊥-elim (p refl)
head (singleton (leaf x)) p = x
head (more (one (leaf x)) xs x₁) p = x
head (more (two (leaf x) x₂) xs x₁) p = x
head (more (three (leaf x) x₂ x₃) xs x₁) p = x

tail : ∀ {A n b} → FingerTree A n b → FingerTree A n (decL b)
tail nil = nil
tail (singleton x) = nil
tail (more (two x x₁) xs r) = more (one x₁) xs r
tail (more (three x x₁ x₂) xs r) = more (two x₁ x₂) xs r
tail (more (one x) nil (one x₁)) = singleton x₁
tail (more (one x) nil (two x₁ x₂)) = more (one x₁) nil (one x₂)
tail (more (one x) nil (three x₁ x₂ x₃)) = more (one x₁) nil (two x₂ x₃)
tail (more (one x) (singleton (node2 x₁ x₂)) r) = more (two x₁ x₂) nil r
tail (more (one x) (singleton (node3 x₁ x₂ x₃)) r) = more (three x₁ x₂ x₃) nil r
tail (more (one x) m@(more (one (node2 x₁ x₂)) xs r') r) = more (two x₁ x₂) (tail m) r
tail (more (one x) m@(more (one (node3 x₁ x₂ x₃)) xs r') r) = more (three x₁ x₂ x₃) (tail m) r
tail (more (one x) m@(more (two (node2 x₁ x₂) x₃) xs r') r) = more (two x₁ x₂) (tail m) r
tail (more (one x) m@(more (two (node3 x₁ x₂ x₃) x₄) xs r') r) = more (three x₁ x₂ x₃) (tail m) r
tail (more (one x) m@(more (three (node2 x₁ x₂) x₃ x₄) xs r') r) = more (two x₁ x₂) (tail m) r
tail (more (one x) m@(more (three (node3 x₁ x₂ x₃) x₄ x₅) xs r') r) = more (three x₁ x₂ x₃) (tail m) r

data Some' (A : Set) (n : ℕ) : Digit' n → Set where
    zero  : Some' A n D0
    one   : ∀ {f₁ : Frac n} → Tree A n f₁ → Some' A n (D1 f₁)
    two   : ∀ {f₁ f₂ : Frac n} → Tree A n f₁ → Tree A n f₂ → Some' A n (D2 f₁ f₂)
    three : ∀ {f₁ f₂ f₃ : Frac n} → Tree A n f₁ → Tree A n f₂ → Tree A n f₃ → Some' A n (D3 f₁ f₂ f₃)

appendSome'L : ∀ {A n b d} → Some' A n d → FingerTree A n b → FingerTree A n (addD'L d b)
appendSome'L zero xs = xs
appendSome'L (one x) xs = cons' x xs
appendSome'L (two x x₁) xs = cons' x (cons' x₁ xs)
appendSome'L (three x x₁ x₂) xs = cons' x (cons' x₁ (cons' x₂ xs))

appendSome'R : ∀ {A n b d} → FingerTree A n b → Some' A n d → FingerTree A n (addD'R b d)
appendSome'R xs zero = xs
appendSome'R xs (one x) = snoc' xs x
appendSome'R xs (two x x₁) = snoc' (snoc' xs x) x₁
appendSome'R xs (three x x₁ x₂) = snoc' (snoc' (snoc' xs x) x₁) x₂

combineSome : ∀ {A n d₁ d₂ d₃} → Some A n d₁ → Some' A n d₂ → Some A n d₃ → Some' A (suc n) (combineDigits d₁ d₂ d₃)
combineSome (one x) zero (one x₁) = one (node2 x x₁)
combineSome (one x) zero (two x₁ x₂) = one (node3 x x₁ x₂)
combineSome (one x) zero (three x₁ x₂ x₃) = two (node2 x x₁) (node2 x₂ x₃)
combineSome (one x) (one x₁) (one x₂) = one (node3 x x₁ x₂)
combineSome (one x) (one x₁) (two x₂ x₃) = two (node2 x x₁) (node2 x₂ x₃)
combineSome (one x) (one x₁) (three x₂ x₃ x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (one x) (two x₁ x₂) (one x₃) = two (node2 x x₁) (node2 x₂ x₃)
combineSome (one x) (two x₁ x₂) (two x₃ x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (one x) (two x₁ x₂) (three x₃ x₄ x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (one x) (three x₁ x₂ x₃) (one x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (one x) (three x₁ x₂ x₃) (two x₄ x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (one x) (three x₁ x₂ x₃) (three x₄ x₅ x₆) = three (node3 x x₁ x₂) (node2 x₃ x₄) (node2 x₅ x₆)
combineSome (two x x₁) zero (one x₂) = one (node3 x x₁ x₂)
combineSome (two x x₁) zero (two x₂ x₃) = two (node2 x x₁) (node2 x₂ x₃)
combineSome (two x x₁) zero (three x₂ x₃ x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (two x x₁) (one x₂) (one x₃) = two (node2 x x₁) (node2 x₂ x₃)
combineSome (two x x₁) (one x₂) (two x₃ x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (two x x₁) (one x₂) (three x₃ x₄ x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (two x x₁) (two x₂ x₃) (one x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (two x x₁) (two x₂ x₃) (two x₄ x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (two x x₁) (two x₂ x₃) (three x₄ x₅ x₆) = three (node3 x x₁ x₂) (node2 x₃ x₄) (node2 x₅ x₆)
combineSome (two x x₁) (three x₂ x₃ x₄) (one x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (two x x₁) (three x₂ x₃ x₄) (two x₅ x₆) = three (node3 x x₁ x₂) (node2 x₃ x₄) (node2 x₅ x₆)
combineSome (two x x₁) (three x₂ x₃ x₄) (three x₅ x₆ x₇) = three (node3 x x₁ x₂) (node3 x₃ x₄ x₅) (node2 x₆ x₇)
combineSome (three x x₁ x₂) zero (one x₃) = two (node2 x x₁) (node2 x₂ x₃)
combineSome (three x x₁ x₂) zero (two x₃ x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (three x x₁ x₂) zero (three x₃ x₄ x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (three x x₁ x₂) (one x₃) (one x₄) = two (node3 x x₁ x₂) (node2 x₃ x₄)
combineSome (three x x₁ x₂) (one x₃) (two x₄ x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (three x x₁ x₂) (one x₃) (three x₄ x₅ x₆) = three (node3 x x₁ x₂) (node2 x₃ x₄) (node2 x₅ x₆)
combineSome (three x x₁ x₂) (two x₃ x₄) (one x₅) = two (node3 x x₁ x₂) (node3 x₃ x₄ x₅)
combineSome (three x x₁ x₂) (two x₃ x₄) (two x₅ x₆) = three (node3 x x₁ x₂) (node2 x₃ x₄) (node2 x₅ x₆)
combineSome (three x x₁ x₂) (two x₃ x₄) (three x₅ x₆ x₇) = three (node3 x x₁ x₂) (node3 x₃ x₄ x₅) (node2 x₆ x₇)
combineSome (three x x₁ x₂) (three x₃ x₄ x₅) (one x₆) = three (node3 x x₁ x₂) (node2 x₃ x₄) (node2 x₅ x₆)
combineSome (three x x₁ x₂) (three x₃ x₄ x₅) (two x₆ x₇) = three (node3 x x₁ x₂) (node3 x₃ x₄ x₅) (node2 x₆ x₇)
combineSome (three x x₁ x₂) (three x₃ x₄ x₅) (three x₆ x₇ x₈) = three (node3 x x₁ x₂) (node3 x₃ x₄ x₅) (node3 x₆ x₇ x₈)

glue : ∀ {A n b₁ d b₂} → FingerTree A n b₁ → Some' A n d → FingerTree A n b₂ → FingerTree A n (add3 b₁ d b₂)
glue nil             s ys              = appendSome'L s ys
glue (singleton x)   s ys              = cons' x (appendSome'L s ys)
glue (more xf xs xr) s nil             = appendSome'R (more xf xs xr) s
glue (more xf xs xr) s (singleton y)   = snoc' (appendSome'R (more xf xs xr) s) y
glue (more xf xs xr) s (more yf ys yr) = more xf (glue xs (combineSome xr s yf) ys) yr

append : ∀ {A b₁ b₂} → FingerTree A 0 b₁ → FingerTree A 0 b₂ → FingerTree A 0 (add b₁ b₂)
append xs ys = glue xs zero ys

data IdxTree : (n : ℕ) → Frac n → Set where
    here   : IdxTree 0 one
    left2  : ∀ {n f₁ f₂} → IdxTree n f₁ → IdxTree (suc n) [ f₁ + f₂ ]/2
    right2 : ∀ {n f₁ f₂} → IdxTree n f₂ → IdxTree (suc n) [ f₁ + f₂ ]/2
    left3  : ∀ {n f₁ f₂ f₃} → IdxTree n f₁ → IdxTree (suc n) [ f₁ + f₂ + f₃ ]/2
    mid3   : ∀ {n f₁ f₂ f₃} → IdxTree n f₂ → IdxTree (suc n) [ f₁ + f₂ + f₃ ]/2
    right3 : ∀ {n f₁ f₂ f₃} → IdxTree n f₃ → IdxTree (suc n) [ f₁ + f₂ + f₃ ]/2

lookupTree : ∀ {A n f} → Tree A n f → IdxTree n f → A
lookupTree (leaf x) here = x
lookupTree (node2 l r) (left2 i) = lookupTree l i
lookupTree (node2 l r) (right2 i) = lookupTree r i
lookupTree (node3 l m r) (left3 i) = lookupTree l i
lookupTree (node3 l m r) (mid3 i) = lookupTree m i
lookupTree (node3 l m r) (right3 i) = lookupTree r i

data IdxSome (n : ℕ) : Digit n → Set where
    use₁  : ∀ {f₁} → IdxTree n f₁ → IdxSome n (D1 f₁)
    use₂L : ∀ {f₁ f₂} → IdxTree n f₁ → IdxSome n (D2 f₁ f₂)
    use₂R : ∀ {f₁ f₂} → IdxTree n f₂ → IdxSome n (D2 f₁ f₂)
    use₃L : ∀ {f₁ f₂ f₃} → IdxTree n f₁ → IdxSome n (D3 f₁ f₂ f₃)
    use₃M : ∀ {f₁ f₂ f₃} → IdxTree n f₂ → IdxSome n (D3 f₁ f₂ f₃)
    use₃R : ∀ {f₁ f₂ f₃} → IdxTree n f₃ → IdxSome n (D3 f₁ f₂ f₃)

lookupSome : ∀ {A n d} → Some A n d → IdxSome n d → A
lookupSome (one x) (use₁ i) = lookupTree x i
lookupSome (two x x₁) (use₂L i) = lookupTree x i
lookupSome (two x x₁) (use₂R i) = lookupTree x₁ i
lookupSome (three x x₁ x₂) (use₃L i) = lookupTree x i
lookupSome (three x x₁ x₂) (use₃M i) = lookupTree x₁ i
lookupSome (three x x₁ x₂) (use₃R i) = lookupTree x₂ i

data Idx (n : ℕ) : Binary n → Set where
    atSingle : ∀ {f} → IdxTree n f → Idx n (B1 f)
    front    : ∀ {df dr b} → IdxSome n df → Idx n (df ⟨ b ⟩ dr)
    middle   : ∀ {df dr b} → Idx (suc n) b → Idx n (df ⟨ b ⟩ dr)
    rear     : ∀ {df dr b} → IdxSome n dr → Idx n (df ⟨ b ⟩ dr)

lookup : ∀ {A n b} → FingerTree A n b → Idx n b → A
lookup nil ()
lookup (singleton x) (atSingle i) = lookupTree x i
lookup (more f xs r) (front i) = lookupSome f i
lookup (more f xs r) (middle i) = lookup xs i
lookup (more f xs r) (rear i) = lookupSome r i

sizeF : ∀ {n} → Frac n → ℕ
sizeF one = 1
sizeF [ f₁ + f₂ ]/2 = sizeF f₁ +ℕ sizeF f₂
sizeF [ f₁ + f₂ + f₃ ]/2 = sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)

sizeD : ∀ {n} → Digit n → ℕ
sizeD (D1 f) = sizeF f
sizeD (D2 f₁ f₂) = sizeF f₁ +ℕ sizeF f₂
sizeD (D3 f₁ f₂ f₃) = sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)

sizeB : ∀ {n} → Binary n → ℕ
sizeB B0 = 0
sizeB (B1 f) = sizeF f
sizeB (df ⟨ b ⟩ dr) = sizeD df +ℕ (sizeB b +ℕ sizeD dr)

fromFTree : ∀ {n f} → Fin (sizeF f) → IdxTree n f
fromFTree {f = one} iz = here
fromFTree {f = [ f₁ + f₂ ]/2} i with splitAt (sizeF f₁) i
... | inj₁ il = left2 (fromFTree il)
... | inj₂ ir = right2 (fromFTree ir)
fromFTree {f = [ f₁ + f₂ + f₃ ]/2} i with splitAt (sizeF f₁) i
... | inj₁ il = left3 (fromFTree il)
... | inj₂ i' with splitAt (sizeF f₂) i'
...   | inj₁ im = mid3 (fromFTree im)
...   | inj₂ ir = right3 (fromFTree ir)

fromFSome : ∀ {n d} → Fin (sizeD d) → IdxSome n d
fromFSome {d = D1 f₁} i = use₁ (fromFTree i)
fromFSome {d = D2 f₁ f₂} i with splitAt (sizeF f₁) i
... | inj₁ il = use₂L (fromFTree il)
... | inj₂ ir = use₂R (fromFTree ir)
fromFSome {d = D3 f₁ f₂ f₃} i with splitAt (sizeF f₁) i
... | inj₁ il = use₃L (fromFTree il)
... | inj₂ i' with splitAt (sizeF f₂) i'
...   | inj₁ im = use₃M (fromFTree im)
...   | inj₂ ir = use₃R (fromFTree ir)

fromF : ∀ {n b} → Fin (sizeB b) → Idx n b
fromF {b = B0} ()
fromF {b = B1 f} i = atSingle (fromFTree i)
fromF {b = df ⟨ b ⟩ dr} i with splitAt (sizeD df) i
... | inj₁ il = front (fromFSome il)
... | inj₂ i' with splitAt (sizeB b) i'
...   | inj₁ im = middle (fromF im)
...   | inj₂ ir = rear (fromFSome ir)

toN : ∀ {n} → Binary n → ℕ
toN = sizeB

sizeD' : ∀ {n} → Digit' n → ℕ
sizeD' D0           = 0
sizeD' (D1 f)       = sizeF f
sizeD' (D2 f f₁)    = sizeF f +ℕ sizeF f₁
sizeD' (D3 f f₁ f₂) = sizeF f +ℕ (sizeF f₁ +ℕ sizeF f₂)


il5 : ∀ a b c d e g → (a +ℕ b) +ℕ (((c +ℕ d) +ℕ e) +ℕ g) ≡ a +ℕ ((b +ℕ (c +ℕ d)) +ℕ (e +ℕ g))
il5 = solve-∀

ir1 : ∀ p q r s → p +ℕ (q +ℕ (r +ℕ s)) ≡ (p +ℕ (q +ℕ r)) +ℕ s
ir1 = solve-∀

ir2 : ∀ p q r s t → p +ℕ (q +ℕ (r +ℕ (s +ℕ t))) ≡ (p +ℕ (q +ℕ (r +ℕ s))) +ℕ t
ir2 = solve-∀

ir3 : ∀ p q r s t u → p +ℕ ((q +ℕ (r +ℕ s)) +ℕ (t +ℕ u)) ≡ (p +ℕ (q +ℕ (r +ℕ (s +ℕ t)))) +ℕ u
ir3 = solve-∀

-- incL' adds (sizeF f) leaves.
incL'-correct : ∀ {n} (f : Frac n) (b : Binary n)
              → sizeB (incL' f b) ≡ sizeF f +ℕ sizeB b
incL'-correct f B0                = sym (+-identityʳ (sizeF f))
incL'-correct f (B1 f₁)           = refl
incL'-correct f (D1 f₁ ⟨ b ⟩ d)   = +-assoc (sizeF f) (sizeF f₁) (sizeB b +ℕ sizeD d)
incL'-correct f (D2 f₁ f₂ ⟨ b ⟩ d) = +-assoc (sizeF f) (sizeF f₁ +ℕ sizeF f₂) (sizeB b +ℕ sizeD d)
incL'-correct f (D3 f₁ f₂ f₃ ⟨ b ⟩ d) =
  trans (cong (λ z → (sizeF f +ℕ sizeF f₁) +ℕ (z +ℕ sizeD d)) (incL'-correct [ f₂ + f₃ ]/2 b))
        (il5 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeB b) (sizeD d))

incR'-correct : ∀ {n} (b : Binary n) (f : Frac n)
              → sizeB (incR' b f) ≡ sizeB b +ℕ sizeF f
incR'-correct B0 f                = refl
incR'-correct (B1 f₁) f           = refl
incR'-correct (d ⟨ b ⟩ D1 f₁) f   = ir1 (sizeD d) (sizeB b) (sizeF f₁) (sizeF f)
incR'-correct (d ⟨ b ⟩ D2 f₁ f₂) f = ir2 (sizeD d) (sizeB b) (sizeF f₁) (sizeF f₂) (sizeF f)
incR'-correct (d ⟨ b ⟩ D3 f₁ f₂ f₃) f =
  trans (cong (λ z → sizeD d +ℕ (z +ℕ (sizeF f₃ +ℕ sizeF f))) (incR'-correct b [ f₁ + f₂ ]/2))
        (ir3 (sizeD d) (sizeB b) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f))

incL-correct : ∀ (b : Binary 0) → toN (incL b) ≡ suc (toN b)
incL-correct b = incL'-correct one b

incR-correct : ∀ (b : Binary 0) → toN (incR b) ≡ suc (toN b)
incR-correct b = trans (incR'-correct b one) (+-comm (sizeB b) 1)

-- decL removes the leftmost tree, its size is leadSize
leadSize : ∀ {n} → Binary n → ℕ
leadSize B0                = 0
leadSize (B1 f)            = sizeF f
leadSize (D1 f ⟨ b ⟩ d)    = sizeF f
leadSize (D2 f f₁ ⟨ b ⟩ d) = sizeF f
leadSize (D3 f f₁ f₂ ⟨ b ⟩ d) = sizeF f

leadSize≤sizeB : ∀ {n} (b : Binary n) → leadSize b ≤ sizeB b
leadSize≤sizeB B0             = z≤n
leadSize≤sizeB (B1 f)         = ≤-refl
leadSize≤sizeB (D1 f ⟨ b ⟩ d) = m≤m+n (sizeF f) (sizeB b +ℕ sizeD d)
leadSize≤sizeB (D2 f f₁ ⟨ b ⟩ d) =
  ≤-trans (m≤m+n (sizeF f) (sizeF f₁)) (m≤m+n (sizeF f +ℕ sizeF f₁) (sizeB b +ℕ sizeD d))
leadSize≤sizeB (D3 f f₁ f₂ ⟨ b ⟩ d) =
  ≤-trans (m≤m+n (sizeF f) (sizeF f₁ +ℕ sizeF f₂)) (m≤m+n (sizeF f +ℕ (sizeF f₁ +ℕ sizeF f₂)) (sizeB b +ℕ sizeD d))

-- shared arithmetic for the six borrow cases of decL
borrowArith : ∀ a s c lf → a ≤ s → a +ℕ ((s ∸ a) +ℕ c) ≡ (lf +ℕ (s +ℕ c)) ∸ lf
borrowArith a s c lf a≤s =
  trans (sym (+-assoc a (s ∸ a) c))
        (trans (cong (_+ℕ c) (m+[n∸m]≡n a≤s))
               (sym (m+n∸m≡n lf (s +ℕ c))))

decL-general : ∀ {n} (b : Binary n) → sizeB (decL b) ≡ sizeB b ∸ leadSize b
decL-general B0                = refl
decL-general (B1 f)            = sym (n∸n≡0 (sizeF f))
decL-general (D2 f f₁ ⟨ b ⟩ d) =
  sym (trans (cong (_∸ sizeF f) (+-assoc (sizeF f) (sizeF f₁) (sizeB b +ℕ sizeD d)))
             (m+n∸m≡n (sizeF f) (sizeF f₁ +ℕ (sizeB b +ℕ sizeD d))))
decL-general (D3 f f₁ f₂ ⟨ b ⟩ d) =
  sym (trans (cong (_∸ sizeF f) (+-assoc (sizeF f) (sizeF f₁ +ℕ sizeF f₂) (sizeB b +ℕ sizeD d)))
             (m+n∸m≡n (sizeF f) ((sizeF f₁ +ℕ sizeF f₂) +ℕ (sizeB b +ℕ sizeD d))))
decL-general (D1 f ⟨ B0 ⟩ D1 f₁)       = sym (m+n∸m≡n (sizeF f) (sizeF f₁))
decL-general (D1 f ⟨ B0 ⟩ D2 f₁ f₂)    = sym (m+n∸m≡n (sizeF f) (sizeF f₁ +ℕ sizeF f₂))
decL-general (D1 f ⟨ B0 ⟩ D3 f₁ f₂ f₃) = sym (m+n∸m≡n (sizeF f) (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)))
decL-general (D1 f ⟨ B1 [ f₁ + f₂ ]/2 ⟩ d) =
  sym (m+n∸m≡n (sizeF f) ((sizeF f₁ +ℕ sizeF f₂) +ℕ sizeD d))
decL-general (D1 f ⟨ B1 [ f₁ + f₂ + f₃ ]/2 ⟩ d) =
  sym (m+n∸m≡n (sizeF f) ((sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) +ℕ sizeD d))
decL-general (D1 f ⟨ m@(D1 [ f₁ + f₂ ]/2 ⟨ b ⟩ dr) ⟩ d) =
  trans (cong (λ z → (sizeF f₁ +ℕ sizeF f₂) +ℕ (z +ℕ sizeD d)) (decL-general m))
        (borrowArith (sizeF f₁ +ℕ sizeF f₂) (sizeB m) (sizeD d) (sizeF f) (leadSize≤sizeB m))
decL-general (D1 f ⟨ m@(D1 [ f₁ + f₂ + f₃ ]/2 ⟨ b ⟩ dr) ⟩ d) =
  trans (cong (λ z → (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) +ℕ (z +ℕ sizeD d)) (decL-general m))
        (borrowArith (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) (sizeB m) (sizeD d) (sizeF f) (leadSize≤sizeB m))
decL-general (D1 f ⟨ m@(D2 [ f₁ + f₂ ]/2 f₃ ⟨ b ⟩ dr) ⟩ d) =
  trans (cong (λ z → (sizeF f₁ +ℕ sizeF f₂) +ℕ (z +ℕ sizeD d)) (decL-general m))
        (borrowArith (sizeF f₁ +ℕ sizeF f₂) (sizeB m) (sizeD d) (sizeF f) (leadSize≤sizeB m))
decL-general (D1 f ⟨ m@(D2 [ f₁ + f₂ + f₃ ]/2 f₄ ⟨ b ⟩ dr) ⟩ d) =
  trans (cong (λ z → (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) +ℕ (z +ℕ sizeD d)) (decL-general m))
        (borrowArith (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) (sizeB m) (sizeD d) (sizeF f) (leadSize≤sizeB m))
decL-general (D1 f ⟨ m@(D3 [ f₁ + f₂ ]/2 f₃ f₄ ⟨ b ⟩ dr) ⟩ d) =
  trans (cong (λ z → (sizeF f₁ +ℕ sizeF f₂) +ℕ (z +ℕ sizeD d)) (decL-general m))
        (borrowArith (sizeF f₁ +ℕ sizeF f₂) (sizeB m) (sizeD d) (sizeF f) (leadSize≤sizeB m))
decL-general (D1 f ⟨ m@(D3 [ f₁ + f₂ + f₃ ]/2 f₄ f₅ ⟨ b ⟩ dr) ⟩ d) =
  trans (cong (λ z → (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) +ℕ (z +ℕ sizeD d)) (decL-general m))
        (borrowArith (sizeF f₁ +ℕ (sizeF f₂ +ℕ sizeF f₃)) (sizeB m) (sizeD d) (sizeF f) (leadSize≤sizeB m))

-- At depth 0 the leftmost tree is always a single leaf
sizeF-Frac0 : (f : Frac 0) → sizeF f ≡ 1
sizeF-Frac0 one = refl

∸1≡pred : ∀ n → n ∸ 1 ≡ pred n
∸1≡pred zero    = refl
∸1≡pred (suc n) = refl

decL-correct : ∀ (b : Binary 0) → toN (decL b) ≡ pred (toN b)
decL-correct B0 = refl
decL-correct (B1 f) =
  trans (decL-general (B1 f)) (trans (cong (sizeB (B1 f) ∸_) (sizeF-Frac0 f)) (∸1≡pred (sizeB (B1 f))))
decL-correct (D1 f ⟨ b ⟩ d) =
  trans (decL-general (D1 f ⟨ b ⟩ d)) (trans (cong (sizeB (D1 f ⟨ b ⟩ d) ∸_) (sizeF-Frac0 f)) (∸1≡pred (sizeB (D1 f ⟨ b ⟩ d))))
decL-correct (D2 f f₁ ⟨ b ⟩ d) =
  trans (decL-general (D2 f f₁ ⟨ b ⟩ d)) (trans (cong (sizeB (D2 f f₁ ⟨ b ⟩ d) ∸_) (sizeF-Frac0 f)) (∸1≡pred (sizeB (D2 f f₁ ⟨ b ⟩ d))))
decL-correct (D3 f f₁ f₂ ⟨ b ⟩ d) =
  trans (decL-general (D3 f f₁ f₂ ⟨ b ⟩ d)) (trans (cong (sizeB (D3 f f₁ f₂ ⟨ b ⟩ d) ∸_) (sizeF-Frac0 f)) (∸1≡pred (sizeB (D3 f f₁ f₂ ⟨ b ⟩ d))))

-- helpers for addD'L/R and add3
al3 : ∀ a b c d → a +ℕ (b +ℕ (c +ℕ d)) ≡ (a +ℕ (b +ℕ c)) +ℕ d
al3 = solve-∀
ar3 : ∀ a b c d → ((a +ℕ b) +ℕ c) +ℕ d ≡ a +ℕ (b +ℕ (c +ℕ d))
ar3 = solve-∀
a3final : ∀ p q r s t u v
        → p +ℕ ((q +ℕ ((r +ℕ (s +ℕ t)) +ℕ u)) +ℕ v) ≡ (p +ℕ (q +ℕ r)) +ℕ (s +ℕ (t +ℕ (u +ℕ v)))
a3final = solve-∀

-- helpers for the combineDigits cases
S1 : ∀ a b c d → (a +ℕ b) +ℕ (c +ℕ d) ≡ a +ℕ (b +ℕ (c +ℕ d))
S1 = solve-∀
S2 : ∀ a b c d e → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ e) ≡ a +ℕ (b +ℕ (c +ℕ (d +ℕ e)))
S2 = solve-∀
S3 : ∀ a b c d → (a +ℕ b) +ℕ (c +ℕ d) ≡ a +ℕ ((b +ℕ c) +ℕ d)
S3 = solve-∀
S4 : ∀ a b c d e → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ e) ≡ a +ℕ ((b +ℕ c) +ℕ (d +ℕ e))
S4 = solve-∀
S5 : ∀ a b c d e g → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ g)) ≡ a +ℕ ((b +ℕ c) +ℕ (d +ℕ (e +ℕ g)))
S5 = solve-∀
S6 : ∀ a b c d e → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ e) ≡ a +ℕ ((b +ℕ (c +ℕ d)) +ℕ e)
S6 = solve-∀
S7 : ∀ a b c d e g → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ g)) ≡ a +ℕ ((b +ℕ (c +ℕ d)) +ℕ (e +ℕ g))
S7 = solve-∀
S8 : ∀ a b c d e g h → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ (g +ℕ h)) ≡ a +ℕ ((b +ℕ (c +ℕ d)) +ℕ (e +ℕ (g +ℕ h)))
S8 = solve-∀
S9 : ∀ a b c → a +ℕ (b +ℕ c) ≡ (a +ℕ b) +ℕ c
S9 = solve-∀
S10 : ∀ a b c d e → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ e) ≡ (a +ℕ b) +ℕ (c +ℕ (d +ℕ e))
S10 = solve-∀
S11 : ∀ a b c d e g → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ g)) ≡ (a +ℕ b) +ℕ (c +ℕ (d +ℕ (e +ℕ g)))
S11 = solve-∀
S12 : ∀ a b c d e → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ e) ≡ (a +ℕ b) +ℕ ((c +ℕ d) +ℕ e)
S12 = solve-∀
S13 : ∀ a b c d e g → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ g)) ≡ (a +ℕ b) +ℕ ((c +ℕ d) +ℕ (e +ℕ g))
S13 = solve-∀
S14 : ∀ a b c d e g h → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ (g +ℕ h)) ≡ (a +ℕ b) +ℕ ((c +ℕ d) +ℕ (e +ℕ (g +ℕ h)))
S14 = solve-∀
S15 : ∀ a b c d e g → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ g)) ≡ (a +ℕ b) +ℕ ((c +ℕ (d +ℕ e)) +ℕ g)
S15 = solve-∀
S16 : ∀ a b c d e g h → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ (g +ℕ h)) ≡ (a +ℕ b) +ℕ ((c +ℕ (d +ℕ e)) +ℕ (g +ℕ h))
S16 = solve-∀
S17 : ∀ a b c d e g h i → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ (e +ℕ g)) +ℕ (h +ℕ i)) ≡ (a +ℕ b) +ℕ ((c +ℕ (d +ℕ e)) +ℕ (g +ℕ (h +ℕ i)))
S17 = solve-∀
S18 : ∀ a b c d → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ (b +ℕ c)) +ℕ d
S18 = solve-∀
S19 : ∀ a b c d e g h → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ (g +ℕ h)) ≡ (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ (g +ℕ h)))
S19 = solve-∀
S20 : ∀ a b c d e g → (a +ℕ (b +ℕ c)) +ℕ (d +ℕ (e +ℕ g)) ≡ (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ g)
S20 = solve-∀
S21 : ∀ a b c d e g h i → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ (e +ℕ g)) +ℕ (h +ℕ i)) ≡ (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ (g +ℕ (h +ℕ i)))
S21 = solve-∀
S22 : ∀ a b c d e g h → (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ e) +ℕ (g +ℕ h)) ≡ (a +ℕ (b +ℕ c)) +ℕ ((d +ℕ (e +ℕ g)) +ℕ h)
S22 = solve-∀

addD'L-correct : ∀ {n} (d : Digit' n) (b : Binary n) → sizeB (addD'L d b) ≡ sizeD' d +ℕ sizeB b
addD'L-correct D0 b           = refl
addD'L-correct (D1 f) b       = incL'-correct f b
addD'L-correct (D2 f f₁) b    =
  trans (incL'-correct f (incL' f₁ b))
        (trans (cong (sizeF f +ℕ_) (incL'-correct f₁ b))
               (sym (+-assoc (sizeF f) (sizeF f₁) (sizeB b))))
addD'L-correct (D3 f f₁ f₂) b =
  trans (incL'-correct f (incL' f₁ (incL' f₂ b)))
        (trans (cong (sizeF f +ℕ_) (incL'-correct f₁ (incL' f₂ b)))
               (trans (cong (λ z → sizeF f +ℕ (sizeF f₁ +ℕ z)) (incL'-correct f₂ b))
                      (al3 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeB b))))

addD'R-correct : ∀ {n} (b : Binary n) (d : Digit' n) → sizeB (addD'R b d) ≡ sizeB b +ℕ sizeD' d
addD'R-correct b D0           = sym (+-identityʳ (sizeB b))
addD'R-correct b (D1 f)       = incR'-correct b f
addD'R-correct b (D2 f f₁)    =
  trans (incR'-correct (incR' b f) f₁)
        (trans (cong (_+ℕ sizeF f₁) (incR'-correct b f))
               (+-assoc (sizeB b) (sizeF f) (sizeF f₁)))
addD'R-correct b (D3 f f₁ f₂) =
  trans (incR'-correct (incR' (incR' b f) f₁) f₂)
        (trans (cong (_+ℕ sizeF f₂) (incR'-correct (incR' b f) f₁))
               (trans (cong (λ z → (z +ℕ sizeF f₁) +ℕ sizeF f₂) (incR'-correct b f))
                      (ar3 (sizeB b) (sizeF f) (sizeF f₁) (sizeF f₂))))

combineDigits-correct : ∀ {n} (d₁ : Digit n) (d₂ : Digit' n) (d₃ : Digit n)
                      → sizeD' (combineDigits d₁ d₂ d₃) ≡ sizeD d₁ +ℕ (sizeD' d₂ +ℕ sizeD d₃)
combineDigits-correct (D1 f)       D0            (D1 f₁)       = refl
combineDigits-correct (D1 f)       D0            (D2 f₁ f₂)    = refl
combineDigits-correct (D1 f)       D0            (D3 f₁ f₂ f₃) = S1 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃)
combineDigits-correct (D1 f)       (D1 f₁)       (D1 f₂)       = refl
combineDigits-correct (D1 f)       (D1 f₁)       (D2 f₂ f₃)    = S1 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃)
combineDigits-correct (D1 f)       (D1 f₁)       (D3 f₂ f₃ f₄) = S2 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄)
combineDigits-correct (D1 f)       (D2 f₁ f₂)    (D1 f₃)       = S3 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃)
combineDigits-correct (D1 f)       (D2 f₁ f₂)    (D2 f₃ f₄)    = S4 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄)
combineDigits-correct (D1 f)       (D2 f₁ f₂)    (D3 f₃ f₄ f₅) = S5 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅)
combineDigits-correct (D1 f)       (D3 f₁ f₂ f₃) (D1 f₄)       = S6 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄)
combineDigits-correct (D1 f)       (D3 f₁ f₂ f₃) (D2 f₄ f₅)    = S7 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅)
combineDigits-correct (D1 f)       (D3 f₁ f₂ f₃) (D3 f₄ f₅ f₆) = S8 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆)
combineDigits-correct (D2 f f₁)    D0            (D1 f₂)       = S9 (sizeF f) (sizeF f₁) (sizeF f₂)
combineDigits-correct (D2 f f₁)    D0            (D2 f₂ f₃)    = refl
combineDigits-correct (D2 f f₁)    D0            (D3 f₂ f₃ f₄) = S10 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄)
combineDigits-correct (D2 f f₁)    (D1 f₂)       (D1 f₃)       = refl
combineDigits-correct (D2 f f₁)    (D1 f₂)       (D2 f₃ f₄)    = S10 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄)
combineDigits-correct (D2 f f₁)    (D1 f₂)       (D3 f₃ f₄ f₅) = S11 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅)
combineDigits-correct (D2 f f₁)    (D2 f₂ f₃)    (D1 f₄)       = S12 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄)
combineDigits-correct (D2 f f₁)    (D2 f₂ f₃)    (D2 f₄ f₅)    = S13 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅)
combineDigits-correct (D2 f f₁)    (D2 f₂ f₃)    (D3 f₄ f₅ f₆) = S14 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆)
combineDigits-correct (D2 f f₁)    (D3 f₂ f₃ f₄) (D1 f₅)       = S15 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅)
combineDigits-correct (D2 f f₁)    (D3 f₂ f₃ f₄) (D2 f₅ f₆)    = S16 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆)
combineDigits-correct (D2 f f₁)    (D3 f₂ f₃ f₄) (D3 f₅ f₆ f₇) = S17 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆) (sizeF f₇)
combineDigits-correct (D3 f f₁ f₂) D0            (D1 f₃)       = S18 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃)
combineDigits-correct (D3 f f₁ f₂) D0            (D2 f₃ f₄)    = refl
combineDigits-correct (D3 f f₁ f₂) D0            (D3 f₃ f₄ f₅) = refl
combineDigits-correct (D3 f f₁ f₂) (D1 f₃)       (D1 f₄)       = refl
combineDigits-correct (D3 f f₁ f₂) (D1 f₃)       (D2 f₄ f₅)    = refl
combineDigits-correct (D3 f f₁ f₂) (D1 f₃)       (D3 f₄ f₅ f₆) = S19 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆)
combineDigits-correct (D3 f f₁ f₂) (D2 f₃ f₄)    (D1 f₅)       = S20 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅)
combineDigits-correct (D3 f f₁ f₂) (D2 f₃ f₄)    (D2 f₅ f₆)    = refl
combineDigits-correct (D3 f f₁ f₂) (D2 f₃ f₄)    (D3 f₅ f₆ f₇) = S21 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆) (sizeF f₇)
combineDigits-correct (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D1 f₆)       = S22 (sizeF f) (sizeF f₁) (sizeF f₂) (sizeF f₃) (sizeF f₄) (sizeF f₅) (sizeF f₆)
combineDigits-correct (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D2 f₆ f₇)    = refl
combineDigits-correct (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D3 f₆ f₇ f₈) = refl

add3-correct : ∀ {n} (x : Binary n) (d : Digit' n) (y : Binary n)
             → sizeB (add3 x d y) ≡ sizeB x +ℕ (sizeD' d +ℕ sizeB y)
add3-correct B0 d y = addD'L-correct d y
add3-correct (B1 f) d y =
  trans (incL'-correct f (addD'L d y)) (cong (sizeF f +ℕ_) (addD'L-correct d y))
add3-correct (xf ⟨ x ⟩ xr) d B0 =
  trans (addD'R-correct (xf ⟨ x ⟩ xr) d) (cong (sizeB (xf ⟨ x ⟩ xr) +ℕ_) (sym (+-identityʳ (sizeD' d))))
add3-correct (xf ⟨ x ⟩ xr) d (B1 f) =
  trans (incR'-correct (addD'R (xf ⟨ x ⟩ xr) d) f)
        (trans (cong (_+ℕ sizeF f) (addD'R-correct (xf ⟨ x ⟩ xr) d))
               (+-assoc (sizeB (xf ⟨ x ⟩ xr)) (sizeD' d) (sizeF f)))
add3-correct (xf ⟨ x ⟩ xr) d (yf ⟨ y ⟩ yr) =
  trans (cong (λ z → sizeD xf +ℕ (z +ℕ sizeD yr))
              (trans (add3-correct x (combineDigits xr d yf) y)
                     (cong (λ w → sizeB x +ℕ (w +ℕ sizeB y)) (combineDigits-correct xr d yf))))
        (a3final (sizeD xf) (sizeB x) (sizeD xr) (sizeD' d) (sizeD yf) (sizeB y) (sizeD yr))

add-correct : ∀ (x y : Binary 0) → toN (add x y) ≡ toN x +ℕ toN y
add-correct x y = add3-correct x D0 y

data Dyadic : ℕ → Set where
    _/2^_ : (a : ℕ) → (k : ℕ) → Dyadic k

_⊹_ : ∀ {k} → Dyadic k → Dyadic k → Dyadic k
(a /2^ k) ⊹ (b /2^ k) = (a +ℕ b) /2^ k

double : ∀ {k} → Dyadic (suc k) → Dyadic k
double (a /2^ (suc k)) = a /2^ k

_/2 : ∀ {k} → Dyadic k → Dyadic (suc k)
(a /2^ k) /2 = a /2^ suc k

FtoQ : ∀ {n} → Frac n → Dyadic n
FtoQ one             = 1 /2^ 0
FtoQ [ f + g ]/2     = (FtoQ f ⊹ FtoQ g) /2
FtoQ [ f + g + h ]/2 = (FtoQ f ⊹ (FtoQ g ⊹ FtoQ h)) /2

DtoQ : ∀ {n} → Digit n → Dyadic n
DtoQ (D1 f)     = FtoQ f
DtoQ (D2 f g)   = FtoQ f ⊹ FtoQ g
DtoQ (D3 f g h) = FtoQ f ⊹ (FtoQ g ⊹ FtoQ h)

toQ : ∀ {n} → Binary n → Dyadic n
toQ {n} B0        = 0 /2^ n
toQ (B1 f)        = FtoQ f
toQ (df ⟨ b ⟩ dr) = (DtoQ df ⊹ double (toQ b)) ⊹ DtoQ dr

FtoQ-size : ∀ {n} (f : Frac n) → FtoQ f ≡ sizeF f /2^ n
FtoQ-size one             = refl
FtoQ-size [ f + g ]/2     = cong (_/2) (cong₂ _⊹_ (FtoQ-size f) (FtoQ-size g))
FtoQ-size [ f + g + h ]/2 = cong (_/2) (cong₂ _⊹_ (FtoQ-size f) (cong₂ _⊹_ (FtoQ-size g) (FtoQ-size h)))

DtoQ-size : ∀ {n} (d : Digit n) → DtoQ d ≡ sizeD d /2^ n
DtoQ-size (D1 f)     = FtoQ-size f
DtoQ-size (D2 f g)   = cong₂ _⊹_ (FtoQ-size f) (FtoQ-size g)
DtoQ-size (D3 f g h) = cong₂ _⊹_ (FtoQ-size f) (cong₂ _⊹_ (FtoQ-size g) (FtoQ-size h))

toQ-size : ∀ {n} (b : Binary n) → toQ b ≡ sizeB b /2^ n
toQ-size B0          = refl
toQ-size (B1 f)      = FtoQ-size f
toQ-size (df ⟨ b ⟩ dr) =
  trans (cong₂ _⊹_ (cong₂ _⊹_ (DtoQ-size df) (cong double (toQ-size b))) (DtoQ-size dr))
        (cong (_/2^ _) (+-assoc (sizeD df) (sizeB b) (sizeD dr)))

module FracBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)

-- ℕ functions and lemmas

2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

data Frac : ℕ -> Set where
    zero : Frac 0
    [_+_]/2 : ∀ {n} → Frac n → Frac n → Frac (suc n)
    [_+_+_+1]/2 : ∀ {n} → Frac n → Frac n → Frac n → Frac (suc n)

data Digit : ℕ → Set where
    D1 : ∀ {n} → Frac n → Digit n
    D2 : ∀ {n} → Frac n → Frac n → Digit n
    D3 : ∀ {n} → Frac n → Frac n → Frac n → Digit n

data Binary : ℕ → Set where
    B0 : ∀ {n} → Binary n
    B1 : ∀ {n} → Frac n → Binary n
    _⟨_⟩_ : ∀ {n} → Digit n → Binary (suc n) → Digit n → Binary n

-- TODO: toN

incL' : ∀ {n} → Frac n → Binary n → Binary n
incL' f B0 = B1 f
incL' f (B1 f₁) = (D1 f) ⟨ B0 ⟩ (D1 f₁)
incL' f (D1 f₁ ⟨ b ⟩ d) = (D2 f f₁) ⟨ b ⟩ d
incL' f (D2 f₁ f₂ ⟨ b ⟩ d) = (D3 f f₁ f₂) ⟨ b ⟩ d
incL' f (D3 f₁ f₂ f₃ ⟨ b ⟩ d) = (D2 f f₁) ⟨ (incL' [ f₂ + f₃ ]/2 b) ⟩ d

incL : Binary 0 → Binary 0
incL b = incL' zero b

incR' : ∀ {n} → Binary n → Frac n → Binary n
incR' B0 f = B1 f
incR' (B1 f₁) f = (D1 f₁) ⟨ B0 ⟩ (D1 f)
incR' (d ⟨ b ⟩ D1 f₁) f = d ⟨ b ⟩ (D2 f₁ f)
incR' (d ⟨ b ⟩ D2 f₁ f₂) f = d ⟨ b ⟩ (D3 f₁ f₂ f)
incR' (d ⟨ b ⟩ D3 f₁ f₂ f₃) f = d ⟨ (incR' b [ f₁ + f₂ ]/2) ⟩ (D2 f₃ f)

incR : Binary 0 → Binary 0
incR b = incR' b zero

decL : ∀ {n} → Binary n → Binary n
decL B0 = B0
decL (B1 f) = B0
decL (D2 f f₁ ⟨ b ⟩ d) = D1 f₁ ⟨ b ⟩ d
decL (D3 f f₁ f₂ ⟨ b ⟩ d) = (D2 f₁ f₂) ⟨ b ⟩ d
decL (D1 f ⟨ B0 ⟩ D1 f₁) = B1 f₁
decL (D1 f ⟨ B0 ⟩ D2 f₁ f₂) = (D1 f₁) ⟨ B0 ⟩ (D1 f₂)
decL (D1 f ⟨ B0 ⟩ D3 f₁ f₂ f₃) = (D1 f₁) ⟨ B0 ⟩ (D2 f₂ f₃)
decL (D1 f ⟨ B1 [ f₁ + f₂ ]/2 ⟩ d) = (D2 f₁ f₂) ⟨ B0 ⟩ d
decL (D1 f ⟨ B1 [ f₁ + f₂ + f₃ +1]/2 ⟩ d) = (D3 f₁ f₂ f₃) ⟨ B0 ⟩ d
decL (D1 f ⟨ m@(D1 [ f₁ + f₂ ]/2 ⟨ b ⟩ dr) ⟩ d) = (D2 f₁ f₂) ⟨ (decL m) ⟩ d
decL (D1 f ⟨ m@(D1 [ f₁ + f₂ + f₃ +1]/2 ⟨ b ⟩ dr) ⟩ d) = (D3 f₁ f₂ f₃) ⟨ (decL m) ⟩ d
decL (D1 f ⟨ m@(D2 [ f₁ + f₂ ]/2 f₃ ⟨ b ⟩ dr) ⟩ d) = (D2 f₁ f₂) ⟨ decL m ⟩ d
decL (D1 f ⟨ m@(D2 [ f₁ + f₂ + f₃ +1]/2 f₄ ⟨ b ⟩ dr) ⟩ d) = (D3 f₁ f₂ f₃) ⟨ decL m ⟩ d
decL (D1 f ⟨ m@(D3 [ f₁ + f₂ ]/2 f₃ f₄ ⟨ b ⟩ dr) ⟩ d) = (D2 f₁ f₂) ⟨ decL m ⟩ d
decL (D1 f ⟨ m@(D3 [ f₁ + f₂ + f₃ +1]/2 f₄ f₅ ⟨ b ⟩ dr) ⟩ d) = (D3 f₁ f₂ f₃) ⟨ decL m ⟩ d

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
combineDigits (D1 f)       D0            (D2 f₁ f₂)    = D1 [ f + f₁ + f₂ +1]/2
combineDigits (D1 f)       D0            (D3 f₁ f₂ f₃) = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D1 f)       (D1 f₁)       (D1 f₂)       = D1 [ f + f₁ + f₂ +1]/2
combineDigits (D1 f)       (D1 f₁)       (D2 f₂ f₃)    = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D1 f)       (D1 f₁)       (D3 f₂ f₃ f₄) = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D1 f)       (D2 f₁ f₂)    (D1 f₃)       = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D1 f)       (D2 f₁ f₂)    (D2 f₃ f₄)    = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D1 f)       (D2 f₁ f₂)    (D3 f₃ f₄ f₅) = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D1 f)       (D3 f₁ f₂ f₃) (D1 f₄)       = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D1 f)       (D3 f₁ f₂ f₃) (D2 f₄ f₅)    = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D1 f)       (D3 f₁ f₂ f₃) (D3 f₄ f₅ f₆) = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D2 f f₁)    D0            (D1 f₂)       = D1 [ f + f₁ + f₂ +1]/2
combineDigits (D2 f f₁)    D0            (D2 f₂ f₃)    = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D2 f f₁)    D0            (D3 f₂ f₃ f₄) = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D2 f f₁)    (D1 f₂)       (D1 f₃)       = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D2 f f₁)    (D1 f₂)       (D2 f₃ f₄)    = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D2 f f₁)    (D1 f₂)       (D3 f₃ f₄ f₅) = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D2 f f₁)    (D2 f₂ f₃)    (D1 f₄)       = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D2 f f₁)    (D2 f₂ f₃)    (D2 f₄ f₅)    = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D2 f f₁)    (D2 f₂ f₃)    (D3 f₄ f₅ f₆) = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D2 f f₁)    (D3 f₂ f₃ f₄) (D1 f₅)       = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D2 f f₁)    (D3 f₂ f₃ f₄) (D2 f₅ f₆)    = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D2 f f₁)    (D3 f₂ f₃ f₄) (D3 f₅ f₆ f₇) = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2 [ f₆ + f₇ ]/2
combineDigits (D3 f f₁ f₂) D0            (D1 f₃)       = D2 [ f + f₁ ]/2 [ f₂ + f₃ ]/2
combineDigits (D3 f f₁ f₂) D0            (D2 f₃ f₄)    = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D3 f f₁ f₂) D0            (D3 f₃ f₄ f₅) = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D3 f f₁ f₂) (D1 f₃)       (D1 f₄)       = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2
combineDigits (D3 f f₁ f₂) (D1 f₃)       (D2 f₄ f₅)    = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D3 f f₁ f₂) (D1 f₃)       (D3 f₄ f₅ f₆) = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D3 f f₁ f₂) (D2 f₃ f₄)    (D1 f₅)       = D2 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2
combineDigits (D3 f f₁ f₂) (D2 f₃ f₄)    (D2 f₅ f₆)    = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D3 f f₁ f₂) (D2 f₃ f₄)    (D3 f₅ f₆ f₇) = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2 [ f₆ + f₇ ]/2
combineDigits (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D1 f₆)       = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ ]/2 [ f₅ + f₆ ]/2
combineDigits (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D2 f₆ f₇)    = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2 [ f₆ + f₇ ]/2
combineDigits (D3 f f₁ f₂) (D3 f₃ f₄ f₅) (D3 f₆ f₇ f₈) = D3 [ f + f₁ + f₂ +1]/2 [ f₃ + f₄ + f₅ +1]/2 [ f₆ + f₇ + f₈ +1]/2

add3 : ∀ {n} → Binary n → Digit' n → Binary n → Binary n
add3 B0 d y = addD'L d y
add3 (B1 f) d y = incL' f (addD'L d y)
add3 (xf ⟨ x ⟩ xr) d B0 = addD'R (xf ⟨ x ⟩ xr) d
add3 (xf ⟨ x ⟩ xr) d (B1 f) = incR' (addD'R (xf ⟨ x ⟩ xr) d) f
add3 (xf ⟨ x ⟩ xr) d (yf ⟨ y ⟩ yr) = xf ⟨ (add3 x (combineDigits xr d yf) y) ⟩ yr

add : Binary 0 → Binary 0 → Binary 0
add x y = add3 x D0 y

data Tree (A : Set) : (n : ℕ) → Frac n → Set where
    leaf  : A → Tree A 0 zero
    node2 : ∀ {n} {f₁ f₂ : Frac n} → Tree A n f₁ → Tree A n f₂ → Tree A (suc n) [ f₁ + f₂ ]/2
    node3 : ∀ {n} {f₁ f₂ f₃ : Frac n} → Tree A n f₁ → Tree A n f₂ → Tree A n f₃ → Tree A (suc n) [ f₁ + f₂ + f₃ +1]/2

data Some (A : Set) (n : ℕ) : Digit n → Set where
    one   : ∀ {f₁ : Frac n} → Tree A n f₁ → Some A n (D1 f₁)
    two   : ∀ {f₁ f₂ : Frac n} → Tree A n f₁ → Tree A n f₂ → Some A n (D2 f₁ f₂)
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
glue nil s ys = appendSome'L s ys
glue (singleton x) s ys = cons' x (appendSome'L s ys)
glue (more xf xs xr) s nil = appendSome'R (more xf xs xr) s
glue (more xf xs xr) s (singleton y) = snoc' (appendSome'R (more xf xs xr) s) y
glue (more xf xs xr) s (more yf ys yr) = more xf (glue xs (combineSome xr s yf) ys) yr

append : ∀ {A b₁ b₂} → FingerTree A 0 b₁ → FingerTree A 0 b₂ → FingerTree A 0 (add b₁ b₂)
append xs ys = glue xs zero ys
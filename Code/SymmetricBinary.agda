module SymmetricBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Nullary.Negation using (contradiction)

-- ℕ function and lemmas

2* : ℕ → ℕ
2* zero    = 0
2* (suc n) = suc (suc (2* n))

pred-suc-2n+ : ∀ n k → n ≢ 0 → suc (suc (2* (pred n) + k)) ≡ pred (suc (2* n + k))
pred-suc-2n+ zero    k neq = ⊥-elim (neq refl)
pred-suc-2n+ (suc n) k neq = refl

-- Symmetric binary numbers

-- Digits allowed
data Digit : Set where
    D1 : Digit
    D2 : Digit
    D3 : Digit

-- Modified redundant binary to allow operations from both ends
data Binary : Set where
    B0   : Binary
    B1   : Binary
    _⟨_⟩_ : Digit → Binary → Digit → Binary

Dtoℕ : Digit → ℕ
Dtoℕ D1 = 1
Dtoℕ D2 = 2
Dtoℕ D3 = 3

toℕ : Binary → ℕ
toℕ B0           = 0
toℕ B1           = 1
toℕ (df ⟨ b ⟩ dr) = Dtoℕ df + 2* (toℕ b) + Dtoℕ dr

-- Increment from left
incL : Binary → Binary
incL B0           = B1
incL B1           = D1 ⟨ B0 ⟩ D1
incL (D1 ⟨ b ⟩ d) = D2 ⟨ b ⟩ d
incL (D2 ⟨ b ⟩ d) = D3 ⟨ b ⟩ d
incL (D3 ⟨ b ⟩ d) = D2 ⟨ incL b ⟩ d

-- Increment from right
incR : Binary → Binary
incR B0           = B1
incR B1           = D1 ⟨ B0 ⟩ D1
incR (d ⟨ b ⟩ D1) = d ⟨ b ⟩ D2
incR (d ⟨ b ⟩ D2) = d ⟨ b ⟩ D3
incR (d ⟨ b ⟩ D3) = d ⟨ incR b ⟩ D2

-- Decrement from left
decL : Binary → Binary
decL B0                   = B0
decL B1                   = B0
decL (D1 ⟨ B0 ⟩ D1)        = B1
decL (D1 ⟨ B0 ⟩ D2)        = D1 ⟨ B0 ⟩ D1
decL (D1 ⟨ B0 ⟩ D3)        = D1 ⟨ B0 ⟩ D2
decL (D1 ⟨ B1 ⟩ d)         = D2 ⟨ B0 ⟩ d
decL (D1 ⟨ df ⟨ b ⟩ dr ⟩ d) = D2 ⟨ decL (df ⟨ b ⟩ dr) ⟩ d
decL (D2 ⟨ b ⟩ d)          = D1 ⟨ b ⟩ d
decL (D3 ⟨ b ⟩ d)          = D2 ⟨ b ⟩ d

-- Decrement from right
decR : Binary → Binary
decR B0                     = B0
decR B1                     = B0
decR (d ⟨ b ⟩ D2)           = d ⟨ b ⟩ D1
decR (d ⟨ b ⟩ D3)           = d ⟨ b ⟩ D2
decR (d ⟨ B1 ⟩ D1)          = d ⟨ B0 ⟩ D2
decR (d ⟨ df ⟨ b ⟩ dr ⟩ D1) = d ⟨ decR (df ⟨ b ⟩ dr) ⟩ D2
decR (D1 ⟨ B0 ⟩ D1)         = B1
decR (D2 ⟨ B0 ⟩ D1)         = D1 ⟨ B0 ⟩ D1
decR (D3 ⟨ B0 ⟩ D1)         = D2 ⟨ B0 ⟩ D1

add : Binary → Binary → Binary
add B0 m = m
add B1 m = incL m
add (D1 ⟨ n ⟩ nr) B0 = {!   !}
add (D1 ⟨ n ⟩ nr) B1 = {!   !}
add (D1 ⟨ n ⟩ nr) (x ⟨ m ⟩ x₁) = {!   !}
add (D2 ⟨ n ⟩ nr) m = {!   !}
add (D3 ⟨ n ⟩ nr) m = {!   !}

fromℕ : ℕ → Binary
fromℕ zero    = B0
fromℕ (suc n) = incL (fromℕ n)

-- Binary lemmas

non-zero : ∀ {df b dr} → toℕ (df ⟨ b ⟩ dr) ≢ 0
non-zero {D1} {b} {dr} ()
non-zero {D2} {b} {dr} ()
non-zero {D3} {b} {dr} ()

incL-correct : ∀ b → toℕ (incL b) ≡ suc (toℕ b)
incL-correct B0          = refl
incL-correct B1          = refl
incL-correct (D1 ⟨ b ⟩ d) = refl
incL-correct (D2 ⟨ b ⟩ d) = refl
incL-correct (D3 ⟨ b ⟩ d) = cong suc (cong suc (cong (λ x → x + (Dtoℕ d)) (cong 2* (incL-correct b))))

decL-correct : ∀ b → toℕ (decL b) ≡ pred (toℕ b)
decL-correct B0                    = refl
decL-correct B1                    = refl
decL-correct (D1 ⟨ B0 ⟩ D1)        = refl
decL-correct (D1 ⟨ B0 ⟩ D2)        = refl
decL-correct (D1 ⟨ B0 ⟩ D3)        = refl
decL-correct (D1 ⟨ B1 ⟩ d)         = refl
decL-correct (D1 ⟨ df ⟨ b ⟩ dr ⟩ d) = trans (cong suc (cong suc (cong (λ x → x + (Dtoℕ d)) 
                                           (cong 2* (decL-correct (df ⟨ b ⟩ dr)))))) 
                                           (pred-suc-2n+ (toℕ (df ⟨ b ⟩ dr)) (Dtoℕ d) (non-zero {df} {b} {dr}))
decL-correct (D2 ⟨ b ⟩ d)          = refl
decL-correct (D3 ⟨ b ⟩ d)          = refl

toℕ-fromℕ : ∀ n → toℕ (fromℕ n) ≡ n
toℕ-fromℕ zero    = refl
toℕ-fromℕ (suc n) = trans (incL-correct (fromℕ n)) (cong suc (toℕ-fromℕ n))

zero-unique : ∀ x → toℕ x ≡ 0 → x ≡ B0
zero-unique B0           eq = refl
zero-unique B1           ()
zero-unique (D1 ⟨ b ⟩ dr) ()
zero-unique (D2 ⟨ b ⟩ dr) ()
zero-unique (D3 ⟨ b ⟩ dr) ()

redundant : ∃₂ λ x y → (x ≢ y) × (toℕ x ≡ toℕ y)
redundant = (D2 ⟨ B0 ⟩ D1) , ((D1 ⟨ B0 ⟩ D2) , (λ ()) , refl)

decL-incL≢id : ∃ λ b → b ≢ decL (incL b)
decL-incL≢id = (D3 ⟨ B0 ⟩ D1) , (λ ())

incL-gap : ∃ λ x → (toℕ x ≢ 0) × (∀ y → x ≢ incL y)
incL-gap = (D1 ⟨ B0 ⟩ D2) , ((λ ()) , helper)
  where
    helper : ∀ y → D1 ⟨ B0 ⟩ D2 ≢ incL y
    helper B0          ()
    helper B1          ()
    helper (D1 ⟨ b ⟩ d) ()
    helper (D2 ⟨ b ⟩ d) ()
    helper (D3 ⟨ b ⟩ d) ()

-- Random Access List

data Some (A : Set) : Digit → Set where
    one   : A →         Some A D1
    two   : A → A →     Some A D2
    three : A → A → A → Some A D3

-- Symmetric random access list
data RAL (A : Set) : Binary → Set where
    nil       :                                                       RAL A B0
    singleton : A →                                                   RAL A B1
    more      : ∀ {df b dr} → Some A df → RAL (A × A) b → Some A dr → RAL A (df ⟨ b ⟩ dr)

snoc : ∀ {A b} → RAL A b → A → RAL A (incR b)
snoc nil                           x = singleton x
snoc (singleton x₁)                x = more (one x₁) nil (one x)
snoc (more x₁ xs (one x₂))         x = more x₁ xs (two x₂ x)
snoc (more x₁ xs (two x₂ x₃))      x = more x₁ xs (three x₂ x₃ x)
snoc (more x₁ xs (three x₂ x₃ x₄)) x = more x₁ (snoc xs (x₂ , x₃)) (two x₄ x)

last : ∀ {A b} → RAL A b → (toℕ b ≢ 0) → A
last nil                          p = ⊥-elim (p refl)
last (singleton x)                p = x
last (more x xs (one x₁))         p = x₁
last (more x xs (two x₁ x₂))      p = x₂
last (more x xs (three x₁ x₂ x₃)) p = x₃

more≢empty : ∀ {A df b dr} → RAL A (df ⟨ b ⟩ dr) → (toℕ (df ⟨ b ⟩ dr) ≢ 0)
more≢empty {_} {df} {b} {dr} _ p = contradiction (zero-unique (df ⟨ b ⟩ dr) p) λ ()

init : ∀ {A b} → RAL A b → RAL A (decR b)
init nil                                   = nil
init (singleton x)                         = nil
init (more x xs (two x₁ x₂))               = more x xs (one x₁)
init (more x xs (three x₁ x₂ x₃))          = more x xs (two x₂ x₃)
init (more x (singleton x₁) (one x₂))      = more x nil (two (proj₁ x₁) (proj₂ x₁))
init (more x xs@(more x₁ xs' x₂) (one x₃)) =
    let l = last xs (more≢empty xs)
    in  more x (init xs) (two (proj₁ l) (proj₂ l))
init (more (one x) nil (one x₁))           = singleton x
init (more (two x x₁) nil (one x₂))        = more (one x) nil (one x₁)
init (more (three x x₁ x₂) nil (one x₃))   = more (two x x₁) nil (one x₂)

-- Indices

data IdxDigit : Digit → Set where
    0₁ : IdxDigit D1
    0₂ : IdxDigit D2
    1₂ : IdxDigit D2
    0₃ : IdxDigit D3
    1₃ : IdxDigit D3
    2₃ : IdxDigit D3

lookupSome : ∀ {A b} → Some A b → IdxDigit b → A
lookupSome (one x)       0₁   = x
lookupSome (two x x₁)      0₂ = x
lookupSome (two x x₁)      1₂ = x₁
lookupSome (three x x₁ x₂) 0₃ = x
lookupSome (three x x₁ x₂) 1₃ = x₁
lookupSome (three x x₁ x₂) 2₃ = x₂

data Idx : Binary → Set where
    here  :                             Idx B1
    front : ∀ {df b dr} → IdxDigit df → Idx (df ⟨ b ⟩ dr)
    left  : ∀ {df b dr} → Idx b →       Idx (df ⟨ b ⟩ dr)
    right : ∀ {df b dr} → Idx b →       Idx (df ⟨ b ⟩ dr)
    rear  : ∀ {df b dr} → IdxDigit dr → Idx (df ⟨ b ⟩ dr)

lookup : ∀ {A b} → RAL A b → Idx b → A
lookup nil           ()
lookup (singleton x) here      = x
lookup (more f xs r) (front i) = lookupSome f i
lookup (more f xs r) (left i)  = proj₁ (lookup xs i)
lookup (more f xs r) (right i) = proj₂ (lookup xs i)
lookup (more f xs r) (rear i)  = lookupSome r i

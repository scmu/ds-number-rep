module SymmetricNat where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; opposite; inject₁) renaming (zero to iz; suc to is)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties using (suc-injective)
open import Data.Fin.Properties using (opposite-involutive)

2* : ℕ → ℕ
2* zero = 0
2* (suc n) = suc (suc (2* n))

+-suc : ∀ n → suc n ≡ n + 1
+-suc zero = refl
+-suc (suc n) = cong suc (+-suc n)

data Digit : Set where
    D1 : Digit

data Nat : Set where
    N0 : Nat
    N1 : Nat
    _⟨_⟩_ : Digit → Nat → Digit → Nat

incL : Nat → Nat
incL N0 = N1
incL N1 = D1 ⟨ N0 ⟩ D1
incL (D1 ⟨ n ⟩ d) = D1 ⟨ (incL n) ⟩ d

incR : Nat → Nat
incR N0 = N1
incR N1 = D1 ⟨ N0 ⟩ D1
incR (d ⟨ n ⟩ D1) = d ⟨ (incR n) ⟩ D1

decL : Nat → Nat
decL N0 = N0
decL N1 = N0
decL (D1 ⟨ N0 ⟩ D1) = N1
decL (D1 ⟨ N1 ⟩ d) = D1 ⟨ N0 ⟩ d
decL (D1 ⟨ df ⟨ n ⟩ dr ⟩ d) = D1 ⟨ (decL (df ⟨ n ⟩ dr)) ⟩ d

decR : Nat → Nat
decR N0 = N0
decR N1 = N0
decR (d ⟨ N1 ⟩ D1) = d ⟨ N0 ⟩ D1
decR (d ⟨ df ⟨ n ⟩ dr ⟩ D1) = d ⟨ (decR (df ⟨ n ⟩ dr)) ⟩ D1
decR (D1 ⟨ N0 ⟩ D1) = N1

DtoN : Digit → ℕ
DtoN D1 = 1

toN : Nat → ℕ
toN N0 = 0
toN N1 = 1
toN (df ⟨ n ⟩ dr) = DtoN df + DtoN dr + toN n

toNL : Nat → ℕ
toNL N0 = 0
toNL N1 = 1
toNL (df ⟨ n ⟩ dr) = DtoN df + toNL n

toNR : Nat → ℕ
toNR N0 = 0
toNR N1 = 1
toNR (df ⟨ n ⟩ dr) = DtoN dr + toNR n

fromN : ℕ → Nat
fromN zero = N0
fromN (suc n) = incL (fromN n)

incL-correct : ∀ n → toN (incL n) ≡ suc (toN n)
incL-correct N0 = refl
incL-correct N1 = refl
incL-correct (D1 ⟨ n ⟩ D1) = cong (λ n → suc (suc n)) (incL-correct n)

incR-correct : ∀ n → toN (incR n) ≡ suc (toN n)
incR-correct N0 = refl
incR-correct N1 = refl
incR-correct (D1 ⟨ n ⟩ D1) = cong (λ n → suc (suc n)) (incR-correct n)

decL-correct : ∀ n → toN (decL n) ≡ pred (toN n)
decL-correct N0 = refl
decL-correct N1 = refl
decL-correct (D1 ⟨ N0 ⟩ D1) = refl
decL-correct (D1 ⟨ N1 ⟩ D1) = refl
decL-correct (D1 ⟨ D1 ⟨ n ⟩ D1 ⟩ D1) = cong (λ n → suc (suc n)) (decL-correct (D1 ⟨ n ⟩ D1))

decR-correct : ∀ n → toN (decR n) ≡ pred (toN n)
decR-correct N0 = refl
decR-correct N1 = refl
decR-correct (D1 ⟨ N0 ⟩ D1) = refl
decR-correct (D1 ⟨ N1 ⟩ D1) = refl
decR-correct (D1 ⟨ D1 ⟨ n ⟩ D1 ⟩ D1) = cong (λ n → suc (suc n)) (decR-correct (D1 ⟨ n ⟩ D1))

-- todo
-- decL-incL≡id : ∀ n → decL (incL n) ≡ n
-- decR-incR≡id : ∀ n → decR (incR n) ≡ n

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero = refl
toN-fromN (suc n) = trans (incL-correct (fromN n)) (cong suc (toN-fromN n))

1≢1+1+n : ∀ {n} → 1 ≢ (1 + 1 + n)
1≢1+1+n {n} = λ ()

1+n≢0 : ∀ {n} → suc n ≢ 0
1+n≢0 ()

nonRedundant : ∀ x y → toN x ≡ toN y → x ≡ y
nonRedundant N0 N0 refl = refl
nonRedundant N0 (D1 ⟨ y ⟩ D1) ()
nonRedundant N1 N1 refl = refl
nonRedundant N1 (D1 ⟨ y ⟩ D1) eq = ⊥-elim (1≢1+1+n eq)
nonRedundant (D1 ⟨ x ⟩ D1) N0 eq = ⊥-elim (1+n≢0 eq)
nonRedundant (D1 ⟨ x ⟩ D1) N1 eq = ⊥-elim (1≢1+1+n (sym eq))
nonRedundant (D1 ⟨ x ⟩ D1) (D1 ⟨ y ⟩ D1) eq = cong (λ n → D1 ⟨ n ⟩ D1) (nonRedundant x y (suc-injective (suc-injective eq)))

fromN-toN : ∀ n → fromN (toN n) ≡ n
fromN-toN N0 = refl
fromN-toN N1 = refl
fromN-toN (D1 ⟨ n ⟩ D1) = nonRedundant _ _ (trans (incL-correct (fromN (suc (toN n)))) (cong suc (toN-fromN (suc (toN n)))))

incL≢0 : ∀ n → incL n ≢ N0
incL≢0 N0 = λ ()
incL≢0 N1 = λ ()
incL≢0 (D1 ⟨ n ⟩ d) = λ ()

incR≢0 : ∀ n → incR n ≢ N0
incR≢0 N0 = λ ()
incR≢0 N1 = λ ()
incR≢0 (d ⟨ n ⟩ D1) = λ ()

data Left-View : Nat → Set where
    as-zero : Left-View N0
    as-succ : (i : Nat) → Left-View (incL i)

lview : ∀ n → Left-View n
lview N0 = as-zero
lview N1 = as-succ N0
lview (D1 ⟨ n ⟩ d) with lview n
... | as-succ i = as-succ (D1 ⟨ i ⟩ d)
lview (D1 ⟨ n ⟩ D1) | as-zero = as-succ N1

LVtoN : ∀ {n} → Left-View n → ℕ
LVtoN as-zero = zero
LVtoN (as-succ n) = suc (toN n)

lview-correct : ∀ n → LVtoN (lview n) ≡ toN n
lview-correct N0 = refl
lview-correct N1 = refl
lview-correct (D1 ⟨ n ⟩ D1) with lview n
... | as-zero = refl
... | as-succ m = cong (λ n → suc (suc n)) (sym (incL-correct m))

data Some (A : Set) : Digit → Set where
    one : A → Some A D1

data RAL (A : Set) : Nat → Set where
    nil : RAL A N0
    singleton : A → RAL A N1
    more : ∀ {df n dr} → Some A df → RAL A n → Some A dr → RAL A (df ⟨ n ⟩ dr)

cons : ∀ {A n} → A → RAL A n → RAL A (incL n)
cons x nil                   = singleton x
cons x (singleton x₁)        = more (one x) nil (one x₁)
cons x (more (one x₁) xs x₂) = more (one x) (cons x₁ xs) x₂

snoc : ∀ {A n} → A → RAL A n → RAL A (incR n)
snoc x nil                   = singleton x
snoc x (singleton x₁)        = more (one x₁) nil (one x)
snoc x (more x₁ xs (one x₂)) = more x₁ (snoc x₂ xs) (one x)

head : ∀ {A n} → RAL A (incL n) → A
head {_} {N0}         (singleton x)        = x
head {_} {N1}         (more (one x) xs x₁) = x
head {_} {D1 ⟨ n ⟩ x₁} (more (one x) xs x₂) = x

head' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head' nil                  p = ⊥-elim (p refl)
head' (singleton x)        p = x
head' (more (one x) xs x₁) p = x

more≢nil : ∀ {A df n dr} → RAL A (df ⟨ n ⟩ dr) → (toN (df ⟨ n ⟩ dr) ≢ 0)
more≢nil {_} {D1} xs ()

tail : ∀ {A n} → RAL A n → RAL A (decL n)
tail nil                              = nil
tail (singleton x)                    = nil
tail (more (one x) nil (one x₁))      = singleton x₁
tail (more (one x) (singleton x₁) x₂) = more (one x₁) nil x₂
tail (more (one x) xs@(more x₁ xs' x₂) x₃) =
    let h = head' xs (more≢nil xs)
    in  more (one h) (tail xs) x₃

data Idx : Nat → Set where
    0b₁ :                  Idx N1
    0f₁₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩ D1)
    _1₁₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D1)
    0r₁₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩ D1)

lookup : ∀ {A n} → RAL A n → Idx n → A
lookup nil ()
lookup (singleton x) 0b₁ = x
lookup (more (one x) xs (one x₁)) 0f₁₁ = x
lookup (more (one x) xs (one x₁)) (i 1₁₁) = lookup xs i
lookup (more (one x) xs (one x₁)) 0r₁₁ = x₁

-- last index
il : ∀ {n} → Fin (suc n)
il = opposite iz

split : ∀ {n} → (i : Fin (toN n)) → (j : Fin (toN n)) → (opposite i ≡ j) → (Fin (toNL n) × Fin (toNR n))
split {N1} iz iz p = iz , iz
split {D1 ⟨ n ⟩ D1} iz (is j) p = iz , il
split {D1 ⟨ n ⟩ D1} (is i) iz p = il , iz
split {D1 ⟨ n ⟩ D1} (is i) (is j) p with opposite i
... | is j' = is (proj₁ rec), is (proj₂ rec)
    where rec = split {n} (opposite j') j' (opposite-involutive j')

toF : ∀ {n} → Idx n → Fin (toN n)
toF 0b₁ = iz
toF 0f₁₁ = iz
toF {D1 ⟨ n ⟩ D1} (i 1₁₁) = is (inject₁ (toF i))
toF {D1 ⟨ n ⟩ D1} 0r₁₁ = il

fromF' : ∀ {n} → Fin (toNL n) → Fin (toNR n) → Idx n
fromF' {N1} iz iz = 0b₁
fromF' {D1 ⟨ n ⟩ D1} iz iz = 0f₁₁ -- should not happen when called from fromF
fromF' {D1 ⟨ n ⟩ D1} iz (is j) = 0f₁₁
fromF' {D1 ⟨ n ⟩ D1} (is i) iz = 0r₁₁
fromF' {D1 ⟨ n ⟩ D1} (is i) (is j) = (fromF' i j) 1₁₁

fromF : ∀ {n} → Fin (toN n) → Idx n
fromF {n} i with split {n} i (opposite i) refl
... | l , r = fromF' l r

ifirst : ∀ {n} → (n ≢ N0) → Idx n
ifirst {N0} nz = ⊥-elim (nz refl)
ifirst {N1} nz = 0b₁
ifirst {D1 ⟨ n ⟩ D1} nz = 0f₁₁

ilsucc : ∀ {n} → Idx n → Idx (incL n)
ilsucc 0b₁ = 0r₁₁
ilsucc {D1 ⟨ n ⟩ d} 0f₁₁ = (ifirst (incL≢0 n)) 1₁₁
ilsucc {D1 ⟨ n ⟩ d} (i 1₁₁) = (ilsucc i) 1₁₁
ilsucc {D1 ⟨ n ⟩ D1} 0r₁₁ = 0r₁₁

ilast : ∀ {n} → (n ≢ N0) → Idx n
ilast {N0} nz = ⊥-elim (nz refl)
ilast {N1} nz = 0b₁
ilast {D1 ⟨ n ⟩ D1} nz = 0r₁₁

irsucc : ∀ {n} → Idx n → Idx (incR n)
irsucc 0b₁ = 0f₁₁
irsucc {D1 ⟨ n ⟩ D1} 0f₁₁ = 0f₁₁
irsucc {df ⟨ n ⟩ D1} (i 1₁₁) = (irsucc i) 1₁₁
irsucc {d ⟨ n ⟩ D1} 0r₁₁ = ilast (incR≢0 n) 1₁₁

-- fromF-correct : ∀ {n} (i : Fin (toN n)) → toF (fromF i) ≡ i

-- ifirst-correct : ∀ {n} toF ifirst ≡ iz
-- ilsucc-correct : ∀ {n} → (i : Idx n) → toF (ilsucc i) ≡ is (toF i)
-- ilast-correct : ∀ {n} → toF ilast ≡ il
-- irsucc-correct : ∀ {n} → (i : Idx n) → toF (irsucc i) ≡ inject₁ (toF i)

{-
getIdx : ∀ n → ℕ → Idx (fromN (suc n))
getIdx n zero = ifirst (incL≢0 (fromN n))
getIdx zero (suc i) = 0b₁
getIdx (suc n) (suc i) = ilsucc (getLIdx n i)

Idx (D1 ⟨ D1 ⟨ N1 ⟩ D1 ⟩ D1)
index 0 : 0f₁₁
index 1 : 0f₁₁ 1₁₁
index 2 : 0b₁ 1₁₁ 1₁₁
index 3 : 0r₁₁ 1₁₁ (index 1 counted backward)
index 4 : 0r₁₁ (index 0 counted backward)
-}
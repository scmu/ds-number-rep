module SymmetricNat where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Data.Nat.Properties using (suc-injective)

2* : ℕ → ℕ
2* zero = 0
2* (suc n) = suc (suc (2* n))

data Digit : Set where
    d₁ : Digit

data Nat : Set where
    d₀ : Nat
    d₁ : Nat
    _⟨_⟩_ : Digit → Nat → Digit → Nat

incL : Nat → Nat
incL d₀ = d₁
incL d₁ = d₁ ⟨ d₀ ⟩ d₁
incL (d₁ ⟨ n ⟩ d) = d₁ ⟨ (incL n) ⟩ d

incR : Nat → Nat
incR d₀ = d₁
incR d₁ = d₁ ⟨ d₀ ⟩ d₁
incR (d ⟨ n ⟩ d₁) = d ⟨ (incR n) ⟩ d₁

decL : Nat → Nat
decL d₀ = d₀
decL d₁ = d₀
decL (d₁ ⟨ d₀ ⟩ d₁) = d₁
decL (d₁ ⟨ d₁ ⟩ d) = d₁ ⟨ d₀ ⟩ d
decL (d₁ ⟨ df ⟨ n ⟩ dr ⟩ d) = d₁ ⟨ (decL (df ⟨ n ⟩ dr)) ⟩ d

decR : Nat → Nat
decR d₀ = d₀
decR d₁ = d₀
decR (d ⟨ d₁ ⟩ d₁) = d ⟨ d₀ ⟩ d₁
decR (d ⟨ df ⟨ n ⟩ dr ⟩ d₁) = d ⟨ (decR (df ⟨ n ⟩ dr)) ⟩ d₁
decR (d₁ ⟨ d₀ ⟩ d₁) = d₁

D⟦_⇓⟧ : Digit → ℕ
D⟦ d₁ ⇓⟧ = 1

⟦_⇓⟧ : Nat → ℕ
⟦ d₀ ⇓⟧ = 0
⟦ d₁ ⇓⟧ = 1
⟦ df ⟨ n ⟩ dr ⇓⟧ = D⟦ df ⇓⟧ + ⟦ n ⇓⟧ + D⟦ dr ⇓⟧

⟦_⇑⟧ : ℕ → Nat
⟦ zero ⇑⟧ = d₀
⟦ suc n ⇑⟧ = incL ⟦ n ⇑⟧

incL-correct : ∀ n → ⟦ incL n ⇓⟧ ≡ suc ⟦ n ⇓⟧
incL-correct d₀ = refl
incL-correct d₁ = refl
incL-correct (d₁ ⟨ n ⟩ d₁) = cong suc (cong (λ x → x + 1) (incL-correct n))

sound⇑ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
sound⇑ zero = refl
sound⇑ (suc n) = trans (incL-correct ⟦ n ⇑⟧) (cong suc (sound⇑ n))

1≢1+n+1 : ∀ {n} → 1 ≢ 1 + (n + 1)
1≢1+n+1 {zero} ()
1≢1+n+1 {suc n} ()

1+n≢0 : ∀ {n} → suc n ≢ 0
1+n≢0 ()

+1-injective : ∀ {n m} → n + 1 ≡ m + 1 → n ≡ m
+1-injective {zero} {zero} eq = refl
+1-injective {zero} {suc m} eq = ⊥-elim (1≢1+n+1 eq)
+1-injective {suc n} {zero} eq = ⊥-elim (1≢1+n+1 (sym eq))
+1-injective {suc n} {suc m} eq = cong suc (+1-injective (suc-injective eq))

nonRedundant : ∀ x y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
nonRedundant d₀ d₀ refl = refl
nonRedundant d₀ (d₁ ⟨ y ⟩ d₁) ()
nonRedundant d₁ d₁ refl = refl
nonRedundant d₁ (d₁ ⟨ y ⟩ d₁) eq = ⊥-elim (1≢1+n+1 eq)
nonRedundant (d₁ ⟨ x ⟩ d₁) d₀ eq = ⊥-elim (1+n≢0 eq)
nonRedundant (d₁ ⟨ x ⟩ d₁) d₁ eq = ⊥-elim (1≢1+n+1 (sym eq))
nonRedundant (d₁ ⟨ x ⟩ d₁) (d₁ ⟨ y ⟩ d₁) eq = cong (λ n → d₁ ⟨ n ⟩ d₁) (nonRedundant x y (suc-injective (+1-injective eq)))

complete⇓ : ∀ n → ⟦ ⟦ n ⇓⟧ ⇑⟧ ≡ n
complete⇓ d₀ = refl
complete⇓ d₁ = refl
complete⇓ (d₁ ⟨ n ⟩ d₁) = nonRedundant _ _ (trans (incL-correct ⟦ ⟦ n ⇓⟧ + 1 ⇑⟧) (cong suc (sound⇑ (⟦ n ⇓⟧ + D⟦ d₁ ⇓⟧))))

data Some (A : Set) : Digit → Set where
    one : A → Some A d₁

data RAL (A : Set) : Nat → Set where
    nil : RAL A d₀
    singleton : A → RAL A d₁
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
head {_} {d₀}         (singleton x)        = x
head {_} {d₁}         (more (one x) xs x₁) = x
head {_} {d₁ ⟨ n ⟩ x₁} (more (one x) xs x₂) = x

head' : ∀ {A n} → RAL A n → (⟦ n ⇓⟧ ≢ 0) → A
head' nil                  p = ⊥-elim (p refl)
head' (singleton x)        p = x
head' (more (one x) xs x₁) p = x

more≢nil : ∀ {A df n dr} → RAL A (df ⟨ n ⟩ dr) → (⟦ df ⟨ n ⟩ dr ⇓⟧ ≢ 0)
more≢nil {_} {d₁} xs ()

tail : ∀ {A n} → RAL A n → RAL A (decL n)
tail nil                              = nil
tail (singleton x)                    = nil
tail (more (one x) nil (one x₁))      = singleton x₁
tail (more (one x) (singleton x₁) x₂) = more (one x₁) nil x₂
tail (more (one x) xs@(more x₁ xs' x₂) x₃) =
    let h = head' xs (more≢nil xs)
    in  more (one h) (tail xs) x₃

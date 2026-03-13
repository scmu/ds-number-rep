module FracZeroless where

open import Data.Nat using (ℕ; zero; suc; _+_; pred; _∸_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Fin using (Fin) renaming (zero to iz; suc to is)
open import Data.Nat.Properties using (+-assoc)
open import Relation.Binary.PropositionalEquality

data Dyadic  : ℕ → Set where
    _/2^_ : (n : ℕ) → (k : ℕ) → Dyadic k 

_⊹_ : ∀ {k} → Dyadic k → Dyadic k → Dyadic k
(n /2^ k) ⊹ (m /2^ k) = (n + m) /2^ k

2* : ∀ {k} → Dyadic (suc k) → Dyadic k
2* (n /2^ (suc k)) = n /2^ k

_/2 : ∀ {k} → Dyadic k → Dyadic (suc k)
(n /2^ k) /2 = n /2^ suc k

inj-num : ∀ {k} {a b : ℕ} → (a /2^ k) ≡ (b /2^ k) → a ≡ b
inj-num refl = refl

*2-/2 : ∀ {k} → (n : Dyadic k) → (2* (n /2)) ≡ n
*2-/2 (n /2^ k) = refl

2*-distrib : ∀ {k} → (n : Dyadic (suc k)) → (m : Dyadic (suc k)) → 2* (n ⊹ m) ≡ (2* n) ⊹ (2* m)
2*-distrib (n /2^ k) (m /2^ k) = refl

⊹-assoc : ∀ {k} → (x : Dyadic k) → (y : Dyadic k) → (z : Dyadic k) → ((x ⊹ y) ⊹ z) ≡ (x ⊹ (y ⊹ z))
⊹-assoc (x /2^ k) (y /2^ k) (z /2^ k) = cong (_/2^ k) (+-assoc x y z)

data Frac : ℕ -> Set where
    one : Frac 0
    [_+_]/2 : ∀ {n} → Frac n → Frac n → Frac (suc n)

data Digit : ℕ → Set where
    D1 : ∀ {n} → Frac n → Digit n
    D2 : ∀ {n} → Frac n → Frac n → Digit n

data Binary : ℕ → Set where
    B0 : ∀ {n} → Binary n
    _⟨_⟩ : ∀ {n} → Digit n → Binary (suc n) → Binary n

FtoQ : ∀ {n} → Frac n → Dyadic n
FtoQ one = 1 /2^ 0
FtoQ [ f + f₁ ]/2 = ((FtoQ f) ⊹ (FtoQ f₁)) /2

DtoQ : ∀ {n} → Digit n → Dyadic n
DtoQ (D1 f) = FtoQ f
DtoQ (D2 f f₁) = FtoQ f ⊹ FtoQ f₁

toQ : ∀ {n} → Binary n → Dyadic n
toQ {n} B0 = 0 /2^ n
toQ (d ⟨ n ⟩) = DtoQ d ⊹ 2* (toQ n)

toN : Binary 0 → ℕ
toN n with toQ n
... | n' /2^ 0 = n'

inc' : ∀ {n} → Frac n → Binary n → Binary n
inc' f B0 = D1 f ⟨ B0 ⟩
inc' f (D1 f₁ ⟨ n ⟩) = (D2 f f₁) ⟨ n ⟩
inc' f (D2 f₁ f₂ ⟨ n ⟩) = (D1 f) ⟨ inc' [ f₁ + f₂ ]/2 n ⟩

inc : Binary 0 → Binary 0
inc n = inc' one n

fromN : ℕ → Binary 0
fromN zero = B0
fromN (suc n) = inc (fromN n)

inc'-correct : ∀ {k} (f : Frac k) (n : Binary k) → toQ (inc' f n) ≡ FtoQ f ⊹ (toQ n)
inc'-correct f B0 = refl
inc'-correct f (D1 f₁ ⟨ n ⟩) = ⊹-assoc (FtoQ f) (FtoQ f₁) (2* (toQ n))
inc'-correct f (D2 f₁ f₂ ⟨ n ⟩) = 
    cong (λ x → FtoQ f ⊹ x) (trans (cong 2* (inc'-correct [ f₁ + f₂ ]/2 n)) 
                                   (trans (2*-distrib ((FtoQ f₁ ⊹ FtoQ f₂) /2) (toQ n)) 
                                          (cong (λ x → x ⊹ 2* (toQ n)) (*2-/2 (FtoQ f₁ ⊹ FtoQ f₂)))))

inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
inc-correct n with toQ n in eq | toQ (inc n) in eq'
... | n' /2^ 0 | n'' /2^ 0 = inj-num {0} (trans (sym eq') 
                                                (trans (inc'-correct one n) 
                                                       (cong (λ x → FtoQ one ⊹ x) eq)))

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero = refl
toN-fromN (suc n) = trans (inc-correct (fromN n)) (cong suc (toN-fromN n))
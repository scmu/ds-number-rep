module FracZeroless where

open import Data.Nat using (ℕ; zero; suc; _+_; pred; _∸_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Fin using (Fin; splitAt) renaming (zero to iz; suc to is)
open import Data.Sum using (inj₁; inj₂)
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
    one       : Frac 0
    [_+_]/2   : ∀ {n} → Frac n → Frac n → Frac (suc n)

data Digit : ℕ → Set where
    D1 : ∀ {n} → Frac n → Digit n
    D2 : ∀ {n} → Frac n → Frac n → Digit n

data Binary : ℕ → Set where
    B0  : ∀ {n} → Binary n
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

dec : ∀ {n} → Binary n → Binary n
dec B0 = B0
dec (D1 f ⟨ B0 ⟩) = B0
dec (D1 f ⟨ n@(D1 [ f₁ + f₂ ]/2 ⟨ _ ⟩) ⟩) = (D2 f₁ f₂) ⟨ dec n ⟩
dec (D1 f ⟨ n@(D2 [ f₁ + f₂ ]/2 _ ⟨ _ ⟩) ⟩) = (D2 f₁ f₂) ⟨ dec n ⟩
dec (D2 f f₁ ⟨ n ⟩) = (D1 f₁) ⟨ n ⟩

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

dec-inc' : ∀ {k} (f : Frac k) (n : Binary k) → dec (inc' f n) ≡ n
dec-inc' f B0 = refl
dec-inc' f (D1 f₁ ⟨ n ⟩) = refl
dec-inc' f (D2 f₁ f₂ ⟨ B0 ⟩) = refl
dec-inc' f (D2 f₁ f₂ ⟨ D1 [ g₁ + g₂ ]/2 ⟨ n ⟩ ⟩) = refl
dec-inc' f (D2 f₁ f₂ ⟨ D2 [ g₁ + g₂ ]/2 g₃ ⟨ n ⟩ ⟩) =
    cong (λ x → D2 f₁ f₂ ⟨ x ⟩) (dec-inc' [ f₁ + f₂ ]/2 (D2 [ g₁ + g₂ ]/2 g₃ ⟨ n ⟩))

restoreD2 : ∀ {k} (f₁ f₂ : Frac k) (f₃ : Frac (suc k)) (n : Binary (suc (suc k))) →
            inc' [ f₁ + f₂ ]/2 (dec (D2 [ f₁ + f₂ ]/2 f₃ ⟨ n ⟩)) ≡ D2 [ f₁ + f₂ ]/2 f₃ ⟨ n ⟩
restoreD2 f₁ f₂ f₃ n = refl

restoreD1 : ∀ {k} (f₁ f₂ : Frac k) (n : Binary (suc (suc k))) →
            inc' [ f₁ + f₂ ]/2 (dec (D1 [ f₁ + f₂ ]/2 ⟨ n ⟩)) ≡ D1 [ f₁ + f₂ ]/2 ⟨ n ⟩
restoreD1 f₁ f₂ B0 = refl
restoreD1 f₁ f₂ (D1 [ g₁ + g₂ ]/2 ⟨ n ⟩) =
    cong (λ x → D1 [ f₁ + f₂ ]/2 ⟨ x ⟩) (restoreD1 g₁ g₂ n)
restoreD1 f₁ f₂ (D2 [ g₁ + g₂ ]/2 g₃ ⟨ n ⟩) =
    cong (λ x → D1 [ f₁ + f₂ ]/2 ⟨ x ⟩) (restoreD2 g₁ g₂ g₃ n)

inc-dec-nz : ∀ (n : Binary 0) → n ≢ B0 → inc (dec n) ≡ n
inc-dec-nz B0 nz = ⊥-elim (nz refl)
inc-dec-nz (D1 one ⟨ B0 ⟩) nz = refl
inc-dec-nz (D1 one ⟨ D1 [ f₁ + f₂ ]/2 ⟨ n ⟩ ⟩) nz =
    cong (λ x → D1 one ⟨ x ⟩) (restoreD1 f₁ f₂ n)
inc-dec-nz (D1 one ⟨ D2 [ f₁ + f₂ ]/2 f₃ ⟨ n ⟩ ⟩) nz =
    cong (λ x → D1 one ⟨ x ⟩) (restoreD2 f₁ f₂ f₃ n)
inc-dec-nz (D2 one one ⟨ n ⟩) nz = refl

dec-correct' : ∀ (n : Binary 0) → n ≢ B0 → toN (dec n) ≡ pred (toN n)
dec-correct' n nz =
    cong pred (trans (sym (inc-correct (dec n))) (cong toN (inc-dec-nz n nz)))

dec-correct : ∀ (n : Binary 0) → toN (dec n) ≡ pred (toN n)
dec-correct B0 = refl
dec-correct (D1 one ⟨ B0 ⟩) = refl
dec-correct n@(D1 one ⟨ D1 [ f₁ + f₂ ]/2 ⟨ _ ⟩ ⟩) = dec-correct' n (λ ())
dec-correct n@(D1 one ⟨ D2 [ f₁ + f₂ ]/2 _ ⟨ _ ⟩ ⟩) = dec-correct' n (λ ())
dec-correct n@(D2 one one ⟨ _ ⟩) = dec-correct' n (λ ())

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero = refl
toN-fromN (suc n) = trans (inc-correct (fromN n)) (cong suc (toN-fromN n))

data Tree (A : Set) : (n : ℕ) → Frac n → Set where
    leaf  : A → Tree A 0 one
    node2 : ∀ {n} {f₁ f₂ : Frac n} → Tree A n f₁ → Tree A n f₂ → Tree A (suc n) [ f₁ + f₂ ]/2

data Some (A : Set) (n : ℕ) : Digit n → Set where
    one   : ∀ {f₁ : Frac n} → Tree A n f₁ → Some A n (D1 f₁)
    two   : ∀ {f₁ f₂ : Frac n} → Tree A n f₁ → Tree A n f₂ → Some A n (D2 f₁ f₂)

data RAL (A : Set) (n : ℕ) : Binary n → Set where
    nil  : RAL A n B0
    more : ∀ {df : Digit n} {b : Binary (suc n)} → 
        Some A n df → RAL A (suc n) b → RAL A n (df ⟨ b ⟩)

cons' : ∀ {A n b f} → Tree A n f → RAL A n b → RAL A n (inc' f b)
cons' x nil = more (one x) nil
cons' x (more (one x₁) xs) = more (two x x₁) xs
cons' x (more (two x₁ x₂) xs) = more (one x) (cons' (node2 x₁ x₂) xs)


cons : ∀ {A b} → A → RAL A 0 b → RAL A 0 (inc b)
cons x xs = cons' (leaf x) xs

head : ∀ {A b} → RAL A 0 b → (b ≢ B0) → A
head nil                         nz = ⊥-elim (nz refl)
head (more (one (leaf x)) xs)    nz = x
head (more (two (leaf x) x₁) xs) nz = x

tail : ∀ {A n b} → RAL A n b → RAL A n (dec b)
tail nil                                                 = nil
tail (more (one x) nil)                                  = nil
tail (more (one x) xs@(more (one (node2 x₁ x₂)) xs'))    = more (two x₁ x₂) (tail xs)
tail (more (one x) xs@(more (two (node2 x₁ x₂) x₃) xs')) = more (two x₁ x₂) (tail xs)
tail (more (two x x₁) xs)                                = more (one x₁) xs

data IdxTree : (n : ℕ) → Frac n → Set where
    here  : IdxTree 0 one
    left  : ∀ {n f₁ f₂} → IdxTree n f₁ → IdxTree (suc n) [ f₁ + f₂ ]/2
    right : ∀ {n f₁ f₂} → IdxTree n f₂ → IdxTree (suc n) [ f₁ + f₂ ]/2

data Idx (n : ℕ) : Binary n → Set where
    use₁L : ∀ {f₁ b} → IdxTree n f₁ → Idx n (D1 f₁ ⟨ b ⟩)
    skip₁ : ∀ {f₁ b} → Idx (suc n) b → Idx n (D1 f₁ ⟨ b ⟩)
    use₂L : ∀ {f₁ f₂ b} → IdxTree n f₁ → Idx n (D2 f₁ f₂ ⟨ b ⟩)
    use₂R : ∀ {f₁ f₂ b} → IdxTree n f₂ → Idx n (D2 f₁ f₂ ⟨ b ⟩)
    skip₂ : ∀ {f₁ f₂ b} → Idx (suc n) b → Idx n (D2 f₁ f₂ ⟨ b ⟩)
    
lookupTree : ∀ {A n f} → Tree A n f → IdxTree n f → A
lookupTree (leaf x) here = x
lookupTree (node2 l r) (left i) = lookupTree l i
lookupTree (node2 l r) (right i) = lookupTree r i

lookup : ∀ {A n b} → RAL A n b → Idx n b → A
lookup nil ()
lookup (more (one t) xs) (use₁L i) = lookupTree t i
lookup (more (one t) xs) (skip₁ i) = lookup xs i
lookup (more (two t₁ t₂) xs) (use₂L i) = lookupTree t₁ i
lookup (more (two t₁ t₂) xs) (use₂R i) = lookupTree t₂ i
lookup (more (two t₁ t₂) xs) (skip₂ i) = lookup xs i

ifirstTree : ∀ {n} (f : Frac n) → IdxTree n f
ifirstTree one = here
ifirstTree [ f₁ + f₂ ]/2 = left (ifirstTree f₁)

ifront : ∀ {n b f} → IdxTree n f → Idx n (inc' f b)
ifront {b = B0} i = use₁L i
ifront {b = D1 _ ⟨ _ ⟩} i = use₂L i
ifront {b = D2 _ _ ⟨ _ ⟩} i = use₁L i

izero : ∀ {n b f} → Idx n (inc' f b)
izero {f = f} = ifront (ifirstTree f)

isucc : ∀ {n b f} → Idx n b → Idx n (inc' f b)
isucc {b = B0} ()
isucc {b = D1 _ ⟨ _ ⟩} (use₁L i) = use₂R i
isucc {b = D1 _ ⟨ _ ⟩} (skip₁ i) = skip₂ i
isucc {b = D2 f₁ f₂ ⟨ b ⟩} {f = f} (use₂L i) = skip₁ (ifront {b = b} {f = [ f₁ + f₂ ]/2} (left i))
isucc {b = D2 f₁ f₂ ⟨ b ⟩} {f = f} (use₂R i) = skip₁ (ifront {b = b} {f = [ f₁ + f₂ ]/2} (right i))
isucc {b = D2 f₁ f₂ ⟨ b ⟩} {f = f} (skip₂ i) = skip₁ (isucc {b = b} {f = [ f₁ + f₂ ]/2} i)

sizeF : ∀ {n} → Frac n → ℕ
sizeF one = 1
sizeF [ f₁ + f₂ ]/2 = sizeF f₁ + sizeF f₂

sizeB : ∀ {n} → Binary n → ℕ
sizeB B0 = 0
sizeB (D1 f ⟨ b ⟩) = sizeF f + sizeB b
sizeB (D2 f₁ f₂ ⟨ b ⟩) = sizeF f₁ + (sizeF f₂ + sizeB b)

fromFTree : ∀ {n f} → Fin (sizeF f) → IdxTree n f
fromFTree {f = one} iz = here
fromFTree {f = [ f₁ + f₂ ]/2} i with splitAt (sizeF f₁) i
... | inj₁ il = left (fromFTree il)
... | inj₂ ir = right (fromFTree ir)

fromF : ∀ {n b} → Fin (sizeB b) → Idx n b
fromF {b = B0} ()
fromF {b = D1 f ⟨ b ⟩} i with splitAt (sizeF f) i
... | inj₁ il = use₁L (fromFTree il)
... | inj₂ ir = skip₁ (fromF ir)
fromF {b = D2 f₁ f₂ ⟨ b ⟩} i with splitAt (sizeF f₁) i
... | inj₁ il = use₂L (fromFTree il)
... | inj₂ i' with splitAt (sizeF f₂) i'
...   | inj₁ im = use₂R (fromFTree im)
...   | inj₂ ir = skip₂ (fromF ir)
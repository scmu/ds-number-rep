module SymmetricNat where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; opposite; inject₁; fromℕ) renaming (zero to iz; suc to is)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (contradiction)
open import Data.Nat.Properties using (suc-injective)

2* : ℕ → ℕ
2* zero = 0
2* (suc n) = suc (suc (2* n))

+-suc : ∀ n → suc n ≡ n + 1
+-suc zero = refl
+-suc (suc n) = cong suc (+-suc n)

data Digit : Set where
    D1 : Digit

data SNat : Set where
    N0 : SNat
    N1 : SNat
    _⟨_⟩_ : Digit → SNat → Digit → SNat

incL : SNat → SNat
incL N0 = N1
incL N1 = D1 ⟨ N0 ⟩ D1
incL (D1 ⟨ n ⟩ d) = D1 ⟨ (incL n) ⟩ d

incR : SNat → SNat
incR N0 = N1
incR N1 = D1 ⟨ N0 ⟩ D1
incR (d ⟨ n ⟩ D1) = d ⟨ (incR n) ⟩ D1

decL : SNat → SNat
decL N0 = N0
decL N1 = N0
decL (D1 ⟨ N0 ⟩ D1) = N1
decL (D1 ⟨ N1 ⟩ d) = D1 ⟨ N0 ⟩ d
decL (D1 ⟨ df ⟨ n ⟩ dr ⟩ d) = D1 ⟨ (decL (df ⟨ n ⟩ dr)) ⟩ d

decR : SNat → SNat
decR N0 = N0
decR N1 = N0
decR (d ⟨ N1 ⟩ D1) = d ⟨ N0 ⟩ D1
decR (d ⟨ df ⟨ n ⟩ dr ⟩ D1) = d ⟨ (decR (df ⟨ n ⟩ dr)) ⟩ D1
decR (D1 ⟨ N0 ⟩ D1) = N1

DtoN : Digit → ℕ
DtoN D1 = 1

toN : SNat → ℕ
toN N0 = 0
toN N1 = 1
toN (df ⟨ n ⟩ dr) = DtoN df + DtoN dr + toN n

fromN : ℕ → SNat
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

decL-incL≡id : ∀ n → decL (incL n) ≡ n
decL-incL≡id n = nonRedundant (decL (incL n)) n (trans (decL-correct (incL n)) (cong pred (incL-correct n)))

decR-incR≡id : ∀ n → decR (incR n) ≡ n
decR-incR≡id n = nonRedundant (decR (incR n)) n (trans (decR-correct (incR n)) (cong pred (incR-correct n)))

fromN-toN : ∀ n → fromN (toN n) ≡ n
fromN-toN N0 = refl
fromN-toN N1 = refl
fromN-toN (D1 ⟨ n ⟩ D1) = nonRedundant _ _ (trans (incL-correct (fromN (suc (toN n)))) (cong suc (toN-fromN (suc (toN n)))))

incL≢0 : ∀ n → toN (incL n) ≢ 0
incL≢0 N0 = λ ()
incL≢0 N1 = λ ()
incL≢0 (D1 ⟨ n ⟩ d) = λ ()

incR≢0 : ∀ n → incR n ≢ N0
incR≢0 N0 = λ ()
incR≢0 N1 = λ ()
incR≢0 (d ⟨ n ⟩ D1) = λ ()

data Peano-View : SNat → Set where
    as-zero : Peano-View N0
    as-succ : (i : SNat) → Peano-View (incL i)

view : ∀ n → Peano-View n
view N0 = as-zero
view N1 = as-succ N0
view (D1 ⟨ n ⟩ D1) with view n
... | as-zero   = as-succ N1
... | as-succ i = as-succ (D1 ⟨ i ⟩ D1)

VtoN : ∀ {n} → Peano-View n → ℕ
VtoN as-zero = 0
VtoN (as-succ n) = suc (toN n)

view-correct : ∀ n → VtoN (view n) ≡ toN n
view-correct N0 = refl
view-correct N1 = refl
view-correct (D1 ⟨ n ⟩ D1) with view n
... | as-zero   = refl
... | as-succ i = cong suc (cong suc (sym (incL-correct i)))

data Some (A : Set) : Digit → Set where
    one : A → Some A D1

data RAL (A : Set) : SNat → Set where
    nil : RAL A N0
    singleton : A → RAL A N1
    more : ∀ {df n dr} → Some A df → RAL A n → Some A dr → RAL A (df ⟨ n ⟩ dr)

cons : ∀ {A n} → A → RAL A n → RAL A (incL n)
cons x nil                   = singleton x
cons x (singleton x₁)        = more (one x) nil (one x₁)
cons x (more (one x₁) xs s) = more (one x) (cons x₁ xs) s

snoc : ∀ {A n} → A → RAL A n → RAL A (incR n)
snoc x nil                   = singleton x
snoc x (singleton x₁)        = more (one x₁) nil (one x)
snoc x (more s xs (one x₂)) = more s (snoc x₂ xs) (one x)

head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head nil                  nz = ⊥-elim (nz refl)
head (singleton x)        nz = x
head (more (one x) xs s)  nz = x

last : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
last nil                 nz = ⊥-elim (nz refl)
last (singleton x)       nz = x
last (more s xs (one x)) nz = x

more-nonzero : ∀ {A df n dr} → RAL A (df ⟨ n ⟩ dr) → (toN (df ⟨ n ⟩ dr) ≢ 0)
more-nonzero {_} {D1} xs ()

tail : ∀ {A n} → RAL A n → RAL A (decL n)
tail nil                              = nil
tail (singleton x)                    = nil
tail (more (one x) nil (one x₁))      = singleton x₁
tail (more (one x) (singleton x₁) s)  = more (one x₁) nil s
tail (more (one x) xs@(more _ _ _) s) =
    let h = head xs (more-nonzero xs)
    in  more (one h) (tail xs) s

init : ∀ {A n} → RAL A n → RAL A (decR n)
init nil = nil
init (singleton x) = nil
init (more (one x) nil (one x₁)) = singleton x
init (more (one x) (singleton x₁) (one x₂)) = more (one x) nil (one x₁)
init (more (one x) xs@(more _ _ _) (one x₁)) = 
    let l = last xs (more-nonzero xs)
    in  more (one x) (init xs) (one l)

data Idx : SNat → Set where
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

data Max-View : ∀ {n} → Fin (suc n) → Set where
    is-ip : ∀ {n} (i : Fin n) → Max-View (inject₁ i)
    is-il : ∀ {n}             → Max-View {n} (fromℕ n)

mview : ∀ {n} (i : Fin (suc n)) → Max-View i
mview {zero}  iz     = is-il
mview {suc n} iz     = is-ip iz
mview {suc n} (is i) with mview i
... | is-ip j = is-ip (is j)
... | is-il   = is-il

toF : ∀ {n} → Idx n → Fin (toN n)
toF 0b₁ = iz
toF 0f₁₁ = iz
toF {D1 ⟨ n ⟩ D1} (i 1₁₁) = is (inject₁ (toF i))
toF {D1 ⟨ n ⟩ D1} 0r₁₁ = il

fromF : ∀ {n} → Fin (toN n) → Idx n
fromF {N1} iz = 0b₁
fromF {D1 ⟨ n ⟩ D1} iz = 0f₁₁
fromF {D1 ⟨ n ⟩ D1} (is i) with mview i
... | is-il   = 0r₁₁
... | is-ip j = (fromF j) 1₁₁

ifirst : ∀ {n} → (toN n ≢ 0) → Idx n
ifirst {N0} nz = ⊥-elim (nz refl)
ifirst {N1} nz = 0b₁
ifirst {D1 ⟨ n ⟩ D1} nz = 0f₁₁

isuccL : ∀ {n} → Idx n → Idx (incL n)
isuccL 0b₁ = 0r₁₁
isuccL {D1 ⟨ n ⟩ d} 0f₁₁ = (ifirst (incL≢0 n)) 1₁₁
isuccL {D1 ⟨ n ⟩ d} (i 1₁₁) = (isuccL i) 1₁₁
isuccL {D1 ⟨ n ⟩ D1} 0r₁₁ = 0r₁₁

ilast : ∀ {n} → (n ≢ N0) → Idx n
ilast {N0} nz = ⊥-elim (nz refl)
ilast {N1} nz = 0b₁
ilast {D1 ⟨ n ⟩ D1} nz = 0r₁₁

isuccR : ∀ {n} → Idx n → Idx (incR n)
isuccR 0b₁ = 0f₁₁
isuccR {D1 ⟨ n ⟩ D1} 0f₁₁ = 0f₁₁
isuccR {df ⟨ n ⟩ D1} (i 1₁₁) = (isuccR i) 1₁₁
isuccR {d ⟨ n ⟩ D1} 0r₁₁ = ilast (incR≢0 n) 1₁₁

toF-fromF : ∀ {n} (i : Fin (toN n)) → toF {n} (fromF i) ≡ i
toF-fromF {N1} iz = refl
toF-fromF {D1 ⟨ n ⟩ D1} iz = refl
toF-fromF {D1 ⟨ n ⟩ D1} (is i) with mview i
... | is-il   = refl
... | is-ip j = cong (λ i → is (inject₁ i)) (toF-fromF {n} j)

-- ifirst-correct : ∀ {n} → (nz : toN n ≢ 0) → toF (ifirst nz) ≡ iz
-- isuccL-correct : ∀ {n} → (i : Idx n) → toF (isuccL i) ≡ is (toF i)
-- ilast-correct : ∀ {n} → toF ilast ≡ il
-- isuccR-correct : ∀ {n} → (i : Idx n) → toF (isuccR i) ≡ inject₁ (toF i)

lookup-ifirst : ∀ {A n} → (x : A) → (xs : RAL A n) → x ≡ lookup (cons x xs) (ifirst (incL≢0 n))
lookup-ifirst _ nil                        = refl
lookup-ifirst _ (singleton x)              = refl
lookup-ifirst _ (more (one x) xs (one x₁)) = refl

lookup-isuccL : ∀ {A n} → (x : A) → (xs : RAL A n) → (i : Idx n) → lookup xs i ≡ lookup (cons x xs) (isuccL i)
lookup-isuccL _ nil ()
lookup-isuccL _ (singleton x) 0b₁ = refl
lookup-isuccL _ (more (one x) xs (one x₁)) 0f₁₁ = lookup-ifirst x xs
lookup-isuccL _ (more (one x) xs (one x₁)) (i 1₁₁) = lookup-isuccL x xs i
lookup-isuccL _ (more (one x) xs (one x₁)) 0r₁₁ = refl

lookup-ilast : ∀ {A n} → (x : A) → (xs : RAL A n) → x ≡ lookup (snoc x xs) (ilast (incR≢0 n))
lookup-ilast _ nil = refl
lookup-ilast _ (singleton x) = refl
lookup-ilast _ (more (one x) xs (one x₁)) = refl

lookup-isuccR : ∀ {A n} → (x : A) → (xs : RAL A n) → (i : Idx n) → lookup xs i ≡ lookup (snoc x xs) (isuccR i)
lookup-isuccR _ nil ()
lookup-isuccR _ (singleton x)              0b₁     = refl
lookup-isuccR _ (more (one x) xs (one x₁)) 0f₁₁    = refl
lookup-isuccR _ (more (one x) xs (one x₁)) (i 1₁₁) = lookup-isuccR x₁ xs i
lookup-isuccR _ (more (one x) xs (one x₁)) 0r₁₁    = lookup-ilast x₁ xs

data List-View (A : Set) : SNat → Set where
    as-nil  : List-View A N0
    as-cons : ∀ {n : SNat} → A → RAL A (decL n) → List-View A n

lview : ∀ {A n} → RAL A n → List-View A n
lview nil = as-nil
lview (singleton x) = as-cons x nil
lview (more (one x) nil (one x₁)) = as-cons x (singleton x₁)
lview (more (one x) (singleton x₁) s) = as-cons x (more (one x₁) nil s)
lview (more (one x) xs@(more _ _ _) s) with lview xs
... | as-cons x₁ xs' = as-cons x (more (one x₁) xs' s)

head' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head' xs nz with lview xs
... | as-nil        = ⊥-elim (nz refl)
... | as-cons x xs' = x

tail' : ∀ {A n} → RAL A n → RAL A (decL n)
tail' xs with lview xs
... | as-nil        = nil
... | as-cons x xs' = xs'
{-# OPTIONS --rewriting #-}
module SymmetricZerolessBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Fin using (Fin; opposite; inject₁; fromℕ) renaming (zero to iz; suc to is; pred to ip)
open import Relation.Binary.PropositionalEquality

2* : ℕ → ℕ
2* zero = 0
2* (suc n) = suc (suc (2* n))

suc-pred : ∀ n → n ≢ 0 → suc (pred n) ≡ n
suc-pred zero    nz = ⊥-elim (nz refl)
suc-pred (suc n) nz = refl

data Digit : Set where
    D1 : Digit
    D2 : Digit

data SZBinary : Set where
    B0 : SZBinary
    B1 : SZBinary
    _⟨_⟩_ : Digit → SZBinary → Digit → SZBinary

DtoN : Digit → ℕ
DtoN D1 = 1
DtoN D2 = 2

toN : SZBinary → ℕ
toN B0 = 0
toN B1 = 1
toN (df ⟨ n ⟩ dr) = DtoN df + DtoN dr + 2* (toN n)

incL : SZBinary → SZBinary
incL B0 = B1
incL B1 = D1 ⟨ B0 ⟩ D1
incL (D1 ⟨ n ⟩ d) = D2 ⟨ n ⟩ d
incL (D2 ⟨ n ⟩ d) = D1 ⟨ (incL n) ⟩ d

incR : SZBinary → SZBinary
incR B0 = B1
incR B1 = D1 ⟨ B0 ⟩ D1
incR (d ⟨ n ⟩ D1) = d ⟨ n ⟩ D2
incR (d ⟨ n ⟩ D2) = d ⟨ (incR n) ⟩ D1

decL : SZBinary → SZBinary
decL B0 = B0
decL B1 = B0
decL (D1 ⟨ B0 ⟩ D1) = B1
decL (D1 ⟨ B0 ⟩ D2) = D1 ⟨ B0 ⟩ D1
decL (D1 ⟨ B1 ⟩ d) = D2 ⟨ B0 ⟩ d
decL (D1 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ d) = D2 ⟨ (decL n) ⟩ d
decL (D2 ⟨ n ⟩ d) = D1 ⟨ n ⟩ d

decR : SZBinary → SZBinary
decR B0 = B0
decR B1 = B0
decR (d ⟨ n ⟩ D2) = d ⟨ n ⟩ D1
decR (d ⟨ B1 ⟩ D1) = d ⟨ B0 ⟩ D2
decR (d ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D1) = d ⟨ (decR n) ⟩ D2
decR (D1 ⟨ B0 ⟩ D1) = B1
decR (D2 ⟨ B0 ⟩ D1) = D1 ⟨ B0 ⟩ D1

fromN : ℕ → SZBinary
fromN zero = B0
fromN (suc n) = incL (fromN n)

mirror : SZBinary → SZBinary
mirror B0 = B0
mirror B1 = B1
mirror (df ⟨ n ⟩ dr) = dr ⟨ (mirror n) ⟩ df

szb-nonzero : ∀ n → (n ≢ B0) → toN n ≢ 0
szb-nonzero B0 nz = ⊥-elim (nz refl)
szb-nonzero B1 nz = λ ()
szb-nonzero (D1 ⟨ n ⟩ d) nz = λ ()
szb-nonzero (D2 ⟨ n ⟩ d) nz = λ ()

incL-correct : ∀ n → toN (incL n) ≡ suc (toN n)
incL-correct B0 = refl
incL-correct B1 = refl
incL-correct (D1 ⟨ n ⟩ d) = refl
incL-correct (D2 ⟨ n ⟩ D1) = cong (λ n → suc (suc n)) (cong 2* (incL-correct n))
incL-correct (D2 ⟨ n ⟩ D2) = cong (λ n → suc (suc (suc n))) (cong 2* (incL-correct n))

incR-correct : ∀ n → toN (incR n) ≡ suc (toN n)
incR-correct B0 = refl
incR-correct B1 = refl
incR-correct (D1 ⟨ n ⟩ D1) = refl
incR-correct (D2 ⟨ n ⟩ D1) = refl
incR-correct (D1 ⟨ n ⟩ D2) = cong (λ n → suc (suc n)) (cong 2* (incR-correct n))
incR-correct (D2 ⟨ n ⟩ D2) = cong (λ n → suc (suc (suc n))) (cong 2* (incR-correct n))

decL-correct : ∀ n → toN (decL n) ≡ pred (toN n)
decL-correct B0 = refl
decL-correct B1 = refl
decL-correct (D1 ⟨ B0 ⟩ D1) = refl
decL-correct (D1 ⟨ B0 ⟩ D2) = refl
decL-correct (D1 ⟨ B1 ⟩ D1) = refl
decL-correct (D1 ⟨ B1 ⟩ D2) = refl
decL-correct (D1 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D1) = cong (λ n → suc (2* n)) (trans (cong suc (decL-correct n)) (suc-pred (toN n) (szb-nonzero n (λ ()))))
decL-correct (D1 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D2) = cong (λ n → suc (suc (2* n))) (trans (cong suc (decL-correct n)) (suc-pred (toN n) (szb-nonzero n (λ ()))))
decL-correct (D2 ⟨ n ⟩ d) = refl

decR-correct : ∀ n → toN (decR n) ≡ pred (toN n)
decR-correct B0 = refl
decR-correct B1 = refl
decR-correct (D1 ⟨ n ⟩ D2) = refl
decR-correct (D2 ⟨ n ⟩ D2) = refl
decR-correct (D1 ⟨ B0 ⟩ D1) = refl
decR-correct (D2 ⟨ B0 ⟩ D1) = refl
decR-correct (D1 ⟨ B1 ⟩ D1) = refl
decR-correct (D2 ⟨ B1 ⟩ D1) = refl
decR-correct (D1 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D1) = cong (λ n → suc (2* n)) (trans (cong suc (decR-correct n)) (suc-pred (toN n) (szb-nonzero n (λ ()))))
decR-correct (D2 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D1) = cong (λ n → suc (suc (2* n))) (trans (cong suc (decR-correct n)) (suc-pred (toN n) (szb-nonzero n (λ ()))))

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero = refl
toN-fromN (suc n) = trans (incL-correct (fromN n)) (cong suc (toN-fromN n))

redundant : ∃₂ λ x y → (x ≢ y) × (toN x ≡ toN y )
redundant = (D2 ⟨ B0 ⟩ D1) , ((D1 ⟨ B0 ⟩ D2) , ((λ ()) , refl))

zero-unique : ∀ x → toN x ≡ 0 → x ≡ B0
zero-unique B0 p = refl
zero-unique (D1 ⟨ xs ⟩ D1) ()
zero-unique (D1 ⟨ xs ⟩ D2) ()
zero-unique (D2 ⟨ xs ⟩ D1) ()
zero-unique (D2 ⟨ xs ⟩ D2) ()

decL-borrow : ∀ n {d} → (n ≢ B0) → decL (D1 ⟨ n ⟩ d) ≡ (D2 ⟨ decL n ⟩ d)
decL-borrow B0 nz = ⊥-elim (nz refl)
decL-borrow B1 nz = refl
decL-borrow (df ⟨ n ⟩ dr) nz = refl

decR-borrow : ∀ {d} n → (n ≢ B0) → decR (d ⟨ n ⟩ D1) ≡ (d ⟨ decR n ⟩ D2)
decR-borrow B0 nz = ⊥-elim (nz refl)
decR-borrow B1 nz = refl
decR-borrow (df ⟨ n ⟩ dr) nz = refl

incL-nonzero : ∀ n → incL n ≢ B0
incL-nonzero B0 = λ ()
incL-nonzero B1 = λ ()
incL-nonzero (D1 ⟨ n ⟩ d) = λ ()
incL-nonzero (D2 ⟨ n ⟩ d) = λ ()

incR-nonzero : ∀ n → incR n ≢ B0
incR-nonzero B0 = λ ()
incR-nonzero B1 = λ ()
incR-nonzero (d ⟨ n ⟩ D1) = λ ()
incR-nonzero (d ⟨ n ⟩ D2) = λ ()

decL-incL≡id : ∀ n → decL (incL n) ≡ n
decL-incL≡id B0 = refl
decL-incL≡id B1 = refl
decL-incL≡id (D1 ⟨ n ⟩ D1) = refl
decL-incL≡id (D1 ⟨ n ⟩ D2) = refl
decL-incL≡id (D2 ⟨ B0 ⟩ D1) = refl
decL-incL≡id (D2 ⟨ B1 ⟩ D1) = refl
decL-incL≡id (D2 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D1) = trans (decL-borrow (incL n) (incL-nonzero n)) (cong (λ n → D2 ⟨ n ⟩ D1) (decL-incL≡id n))
decL-incL≡id (D2 ⟨ B0 ⟩ D2) = refl
decL-incL≡id (D2 ⟨ B1 ⟩ D2) = refl
decL-incL≡id (D2 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D2) = trans (decL-borrow (incL n) (incL-nonzero n)) (cong (λ n → D2 ⟨ n ⟩ D2) (decL-incL≡id n))

decR-incR≡id : ∀ n → decR (incR n) ≡ n
decR-incR≡id B0 = refl
decR-incR≡id B1 = refl
decR-incR≡id (D1 ⟨ n ⟩ D1) = refl
decR-incR≡id (D1 ⟨ B0 ⟩ D2) = refl
decR-incR≡id (D1 ⟨ B1 ⟩ D2) = refl
decR-incR≡id (D1 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D2) = trans (decR-borrow (incR n) (incR-nonzero n)) (cong (λ n → D1 ⟨ n ⟩ D2) (decR-incR≡id n))
decR-incR≡id (D2 ⟨ n ⟩ D1) = refl
decR-incR≡id (D2 ⟨ B0 ⟩ D2) = refl
decR-incR≡id (D2 ⟨ B1 ⟩ D2) = refl
decR-incR≡id (D2 ⟨ n@(_ ⟨ _ ⟩ _) ⟩ D2) = trans (decR-borrow (incR n) (incR-nonzero n)) (cong (λ n → D2 ⟨ n ⟩ D2) (decR-incR≡id n))

data Peano-View : SZBinary → Set where
    as-zero : Peano-View B0
    as-succ : ∀ {n} → (i : SZBinary) → (p : suc (toN i) ≡ toN n) → Peano-View n

view : ∀ n → Peano-View n
view B0 = as-zero
view B1 = as-succ B0 refl
view (df ⟨ n ⟩ dr) = as-succ (decL (df ⟨ n ⟩ dr)) (trans (cong suc (decL-correct (df ⟨ n ⟩ dr))) (suc-pred (toN (df ⟨ n ⟩ dr)) (szb-nonzero (df ⟨ n ⟩ dr) (λ ()))))

VtoN : ∀ {n} → Peano-View n → ℕ
VtoN as-zero = 0
VtoN (as-succ n p) = suc (toN n)

view-correct : ∀ n → VtoN (view n) ≡ toN n
view-correct B0 = refl
view-correct B1 = refl
view-correct (df ⟨ n ⟩ dr) = trans (cong suc (decL-correct (df ⟨ n ⟩ dr))) (suc-pred (toN (df ⟨ n ⟩ dr)) (szb-nonzero (df ⟨ n ⟩ dr) (λ ())))

data Some (A : Set) : Digit → Set where
    one   : A →         Some A D1
    two   : A → A →     Some A D2

data RAL (A : Set) : SZBinary → Set where
    nil       : RAL A B0
    singleton : A → RAL A B1
    more      : ∀ {df n dr} → Some A df → RAL (A × A) n → Some A dr → RAL A (df ⟨ n ⟩ dr)

cons : ∀ {A n} → A → RAL A n → RAL A (incL n)
cons x nil = singleton x
cons x (singleton x₁) = more (one x) nil (one x₁)
cons x (more (one x₁) xs s) = more (two x x₁) xs s
cons x (more (two x₁ x₂) xs s) = more (one x) (cons (x₁ , x₂) xs) s

snoc : ∀ {A n} → RAL A n → A → RAL A (incR n)
snoc nil x = singleton x
snoc (singleton x₁) x = more (one x₁) nil (one x)
snoc (more s xs (one x₁)) x = more s xs (two x₁ x)
snoc (more s xs (two x₁ x₂)) x = more s (snoc xs (x₁ , x₂)) (one x)

more-nonzero : ∀ {A df n dr} → RAL A (df ⟨ n ⟩ dr) → (toN (df ⟨ n ⟩ dr) ≢ 0)
more-nonzero (more (one _)   _ _) = λ ()
more-nonzero (more (two _ _) _ _) = λ ()

head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head nil nz = ⊥-elim (nz refl)
head (singleton x) nz = x
head (more (one x) xs s) nz = x
head (more (two x x₁) xs s) nz = x

last : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
last nil nz = ⊥-elim (nz refl)
last (singleton x) nz = x
last (more s xs (one x)) nz = x
last (more s xs (two x x₁)) nz = x₁

tail : ∀ {A n} → RAL A n → RAL A (decL n)
tail nil = nil
tail (singleton x) = nil
tail (more (one x) nil (one x₁)) = singleton x₁
tail (more (one x) nil (two x₁ x₂)) = more (one x₁) nil (one x₂)
tail (more (one x) (singleton (x₁ , x₂)) s) = more (two x₁ x₂) nil s
tail (more (one x) xs@(more _ _ _) s) =
    let (x₁ , x₂) = head xs (more-nonzero xs)
    in  more (two x₁ x₂) (tail xs) s
tail (more (two x x₁) xs s) = more (one x₁) xs s

init : ∀ {A n} → RAL A n → RAL A (decR n)
init nil = nil
init (singleton x) = nil
init (more s xs (two x x₁)) = more s xs (one x)
init (more s (singleton (x , x₁)) (one x₂)) = more s nil (two x x₁)
init (more s xs@(more _ _ _) (one x₂)) =
    let (x , x₁) = last xs (more-nonzero xs)
    in  more s (init xs) (two x x₁)
init (more (one x) nil (one x₁)) = singleton x
init (more (two x x₁) nil (one x₂)) = more (one x) nil (one x₁)

-- lookup xs izero ≡ lookup (reverse xs) ilast
reverse : ∀ {A n} → RAL A n → RAL A (mirror n)
reverse nil             = nil
reverse (singleton x)   = singleton x
reverse (more sf xs sr) = more sr (reverse xs) sf

-- Indices for Zeroless binary RAL

_∙2+0 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+0   = iz
is i ∙2+0 = is (is (i ∙2+0))

_∙2+1 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+1   = is iz
is i ∙2+1 = is (is (i ∙2+1))

data Max-View : ∀ {n} → Fin (suc n) → Set where
    is-il : ∀ {n}             → Max-View {n} (fromℕ n)
    is-ip : ∀ {n} (i : Fin n) → Max-View (inject₁ i)

mview : ∀ {n} (i : Fin (suc n)) → Max-View i
mview {zero}  iz     = is-il
mview {suc n} iz     = is-ip iz
mview {suc n} (is i) with mview i
... | is-ip j = is-ip (is j)
... | is-il   = is-il

_/2 : ∀ {n} → Fin (2* n) → (Fin n × Fin 2)
_/2 {suc n} iz           = iz , iz
_/2 {suc n} (is iz)      = iz , is iz
_/2 {suc n} (is (is i)) with i /2
... | q , r = (is q) , r

data Idx : SZBinary → Set where
    0b₁     :                 Idx B1
    0f₁₁    : ∀ {n} →         Idx (D1 ⟨ n ⟩ D1)
    0r₁₁    : ∀ {n} →         Idx (D1 ⟨ n ⟩ D1)
    ⟪1₁_2₁⟫ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D1)
    ⟪2₁_1₁⟫ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D1)
    0f₁₂    : ∀ {n} →         Idx (D1 ⟨ n ⟩ D2)
    0r₁₂    : ∀ {n} →         Idx (D1 ⟨ n ⟩ D2)
    1r₁₂    : ∀ {n} →         Idx (D1 ⟨ n ⟩ D2)
    ⟪1₁_3₂⟫ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D2)
    ⟪2₁_2₂⟫ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D2)
    0f₂₁    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D1)
    1f₂₁    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D1)
    0r₂₁    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D1)
    ⟪2₂_2₁⟫ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩ D1)
    ⟪3₂_1₁⟫ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩ D1)
    0f₂₂    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D2)
    1f₂₂    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D2)
    0r₂₂    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D2)
    1r₂₂    : ∀ {n} →         Idx (D2 ⟨ n ⟩ D2)
    ⟪2₂_3₂⟫ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩ D2)
    ⟪3₂_2₂⟫ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩ D2)

lookup : ∀ {A n} → RAL A n → Idx n → A
lookup (singleton x)                    0b₁       = x
lookup (more (one x)    xs (one x₁))    0f₁₁      = x
lookup (more (one x)    xs (one x₁))    0r₁₁      = x₁
lookup (more (one x)    xs (one x₁))    ⟪1₁ i 2₁⟫ = proj₁ (lookup xs i)
lookup (more (one x)    xs (one x₁))    ⟪2₁ i 1₁⟫ = proj₂ (lookup xs i)
lookup (more (one x)    xs (two x₁ x₂)) 0f₁₂      = x
lookup (more (one x)    xs (two x₁ x₂)) 0r₁₂      = x₂
lookup (more (one x)    xs (two x₁ x₂)) 1r₁₂      = x₁
lookup (more (one x)    xs (two x₁ x₂)) ⟪1₁ i 3₂⟫ = proj₁ (lookup xs i)
lookup (more (one x)    xs (two x₁ x₂)) ⟪2₁ i 2₂⟫ = proj₂ (lookup xs i)
lookup (more (two x x₁) xs (one x₂))    0f₂₁      = x
lookup (more (two x x₁) xs (one x₂))    1f₂₁      = x₁
lookup (more (two x x₁) xs (one x₂))    0r₂₁      = x₂
lookup (more (two x x₁) xs (one x₂))    ⟪2₂ i 2₁⟫ = proj₁ (lookup xs i)
lookup (more (two x x₁) xs (one x₂))    ⟪3₂ i 1₁⟫ = proj₂ (lookup xs i)
lookup (more (two x x₁) xs (two x₂ x₃)) 0f₂₂      = x
lookup (more (two x x₁) xs (two x₂ x₃)) 1f₂₂      = x₁
lookup (more (two x x₁) xs (two x₂ x₃)) 0r₂₂      = x₃
lookup (more (two x x₁) xs (two x₂ x₃)) 1r₂₂      = x₂
lookup (more (two x x₁) xs (two x₂ x₃)) ⟪2₂ i 3₂⟫ = proj₁ (lookup xs i)
lookup (more (two x x₁) xs (two x₂ x₃)) ⟪3₂ i 2₂⟫ = proj₂ (lookup xs i)

il : ∀ {n} → Fin (suc n)
il = opposite iz

toF : ∀ {n} → Idx n → Fin (toN n)
toF 0b₁       = iz
toF 0f₁₁      = iz
toF 0r₁₁      = il
toF ⟪1₁ i 2₁⟫ = is (inject₁ ((toF i) ∙2+0))
toF ⟪2₁ i 1₁⟫ = is (inject₁ ((toF i) ∙2+1))
toF 0f₁₂      = iz
toF 0r₁₂      = il
toF 1r₁₂      = ip il
toF ⟪1₁ i 3₂⟫ = is (inject₁ (inject₁ ((toF i) ∙2+0)))
toF ⟪2₁ i 2₂⟫ = is (inject₁ (inject₁ ((toF i) ∙2+1)))
toF 0f₂₁      = iz
toF 1f₂₁      = is iz
toF 0r₂₁      = il
toF ⟪2₂ i 2₁⟫ = is (is (inject₁ ((toF i) ∙2+0)))
toF ⟪3₂ i 1₁⟫ = is (is (inject₁ ((toF i) ∙2+1)))
toF 0f₂₂      = iz
toF 1f₂₂      = is iz
toF 0r₂₂      = il
toF 1r₂₂      = ip il
toF ⟪2₂ i 3₂⟫ = is (is (inject₁ (inject₁ ((toF i) ∙2+0))))
toF ⟪3₂ i 2₂⟫ = is (is (inject₁ (inject₁ ((toF i) ∙2+1))))

fromF : ∀ {n} → Fin (toN n) → Idx n
fromF {B1} iz = 0b₁
fromF {D1 ⟨ n ⟩ D1} iz = 0f₁₁
fromF {D1 ⟨ n ⟩ D1} (is i) with mview i
... | is-il   = 0r₁₁
... | is-ip j with j /2
...     | q , iz    = ⟪1₁ fromF q 2₁⟫
...     | q , is iz = ⟪2₁ fromF q 1₁⟫
fromF {D1 ⟨ n ⟩ D2} iz = 0f₁₂
fromF {D1 ⟨ n ⟩ D2} (is i) with mview i
... | is-il   = 0r₁₂
... | is-ip j with mview j
...     | is-il   = 1r₁₂
...     | is-ip k with k /2
...         | q , iz    = ⟪1₁ fromF q 3₂⟫
...         | q , is iz = ⟪2₁ fromF q 2₂⟫
fromF {D2 ⟨ n ⟩ D1} iz       = 0f₂₁
fromF {D2 ⟨ n ⟩ D1} (is iz)  = 1f₂₁
fromF {D2 ⟨ n ⟩ D1} (is (is i)) with mview i
... | is-il   = 0r₂₁
... | is-ip j with j /2
...     | q , iz    = ⟪2₂ fromF q 2₁⟫
...     | q , is iz = ⟪3₂ fromF q 1₁⟫
fromF {D2 ⟨ n ⟩ D2} iz       = 0f₂₂
fromF {D2 ⟨ n ⟩ D2} (is iz)  = 1f₂₂
fromF {D2 ⟨ n ⟩ D2} (is (is i)) with mview i
... | is-il   = 0r₂₂
... | is-ip j with mview j
...     | is-il   = 1r₂₂
...     | is-ip k with k /2
...         | q , iz    = ⟪2₂ fromF q 3₂⟫
...         | q , is iz = ⟪3₂ fromF q 2₂⟫

/2-inv-even : ∀ {n} (i : Fin (2* n)) (q : Fin n) → i /2 ≡ (q , iz) → q ∙2+0 ≡ i
/2-inv-even {suc _} iz .iz refl = refl
/2-inv-even {suc _} (is iz) _ ()
/2-inv-even {suc _} (is (is i)) q eq with i /2 in eq'
/2-inv-even {suc _} (is (is i)) q refl | q' , iz  = cong is (cong is (/2-inv-even i q' eq'))

/2-inv-odd : ∀ {n} (i : Fin (2* n)) (q : Fin n) → i /2 ≡ (q , is iz) → q ∙2+1 ≡ i
/2-inv-odd {suc _} iz _ ()
/2-inv-odd {suc _} (is iz) .iz refl = refl
/2-inv-odd {suc _} (is (is i)) q eq with i /2 in eq'
/2-inv-odd {suc _} (is (is i)) .(is q') refl | q' , is iz = cong is (cong is (/2-inv-odd i q' eq'))

toF-fromF : ∀ {n} (i : Fin (toN n)) → toF {n} (fromF i) ≡ i
toF-fromF {B1} iz = refl
toF-fromF {D1 ⟨ n ⟩ D1} iz = refl
toF-fromF {D1 ⟨ n ⟩ D1} (is i) with mview i
... | is-il = refl
... | is-ip j with j /2 in eq
...     | q , iz    = cong (λ i → is (inject₁ i)) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even j q eq))
...     | q , is iz = cong (λ i → is (inject₁ i)) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd j q eq))
toF-fromF {D1 ⟨ n ⟩ D2} iz = refl
toF-fromF {D1 ⟨ n ⟩ D2} (is i) with mview i
... | is-il = refl
... | is-ip j with mview j
...     | is-il = refl
...     | is-ip k with k /2 in eq
...         | q , iz    = cong (λ i → is (inject₁ (inject₁ i))) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even k q eq))
...         | q , is iz = cong (λ i → is (inject₁ (inject₁ i))) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd k q eq))
toF-fromF {D2 ⟨ n ⟩ D1} iz      = refl
toF-fromF {D2 ⟨ n ⟩ D1} (is iz) = refl
toF-fromF {D2 ⟨ n ⟩ D1} (is (is i)) with mview i
... | is-il = refl
... | is-ip j with j /2 in eq
...     | q , iz    = cong (λ i → is (is (inject₁ i))) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even j q eq))
...     | q , is iz = cong (λ i → is (is (inject₁ i))) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd j q eq))
toF-fromF {D2 ⟨ n ⟩ D2} iz      = refl
toF-fromF {D2 ⟨ n ⟩ D2} (is iz) = refl
toF-fromF {D2 ⟨ n ⟩ D2} (is (is i)) with mview i
... | is-il = refl
... | is-ip j with mview j
...     | is-il = refl
...     | is-ip k with k /2 in eq
...         | q , iz    = cong (λ i → is (is (inject₁ (inject₁ i)))) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even k q eq))
...         | q , is iz = cong (λ i → is (is (inject₁ (inject₁ i)))) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd k q eq))

data List-View (A : Set) : SZBinary → Set where
    as-nil  : List-View A B0
    as-cons : ∀ {n : SZBinary} → A → RAL A (decL n) → List-View A n

lview : ∀ {A n} → RAL A n → List-View A n
lview nil = as-nil
lview (singleton x) = as-cons x nil
lview (more (one x) nil (one x₁)) = as-cons x (singleton x₁)
lview (more (one x) nil (two x₁ x₂)) = as-cons x (more (one x₁) nil (one x₂))
lview (more (one x) (singleton (x₁ , x₂)) s) = as-cons x (more (two x₁ x₂) nil s)
lview (more (one x) xs@(more _ _ _) s) with lview xs
... | as-cons (x₁ , x₂) xs' = as-cons x (more (two x₁ x₂) xs' s)
lview (more (two x x₁) xs s) = as-cons x (more (one x₁) xs s)

head' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head' xs nz with lview xs
... | as-nil        = ⊥-elim (nz refl)
... | as-cons x xs' = x

tail' : ∀ {A n} → RAL A n → RAL A (decL n)
tail' xs with lview xs
... | as-nil        = nil
... | as-cons x xs' = xs'

data DigitIdx' : Digit → Set where
    0₁ : DigitIdx' D1
    0₂ : DigitIdx' D2
    1₂ : DigitIdx' D2

data Idx' : SZBinary → Set where
    0₁      : Idx' B1
    _⇐     : ∀ {df n dr} → DigitIdx' df → Idx' (df ⟨ n ⟩ dr)
    ⇒_     : ∀ {df n dr} → DigitIdx' dr → Idx' (df ⟨ n ⟩ dr)
    ⟪1₁_2₁⟫ : ∀ {n} → Idx' n → Idx' (D1 ⟨ n ⟩ D1)
    ⟪2₁_1₁⟫ : ∀ {n} → Idx' n → Idx' (D1 ⟨ n ⟩ D1)
    ⟪1₁_3₂⟫ : ∀ {n} → Idx' n → Idx' (D1 ⟨ n ⟩ D2)
    ⟪2₁_2₂⟫ : ∀ {n} → Idx' n → Idx' (D1 ⟨ n ⟩ D2)
    ⟪2₂_2₁⟫ : ∀ {n} → Idx' n → Idx' (D2 ⟨ n ⟩ D1)
    ⟪3₂_1₁⟫ : ∀ {n} → Idx' n → Idx' (D2 ⟨ n ⟩ D1)
    ⟪2₂_3₂⟫ : ∀ {n} → Idx' n → Idx' (D2 ⟨ n ⟩ D2)
    ⟪3₂_2₂⟫ : ∀ {n} → Idx' n → Idx' (D2 ⟨ n ⟩ D2)

lookupSome : ∀ {A d} → Some A d → DigitIdx' d → A
lookupSome (one x) 0₁ = x
lookupSome (two x x₁) 0₂ = x
lookupSome (two x x₁) 1₂ = x₁

lookup' : ∀ {A n} → RAL A n → Idx' n → A
lookup' nil ()
lookup' (singleton x)   0₁ = x
lookup' (more sf xs sr) (i ⇐) = lookupSome sf i
lookup' (more sf xs sr) (⇒ i) = lookupSome sr i
lookup' (more sf xs sr) ⟪1₁ i 2₁⟫ = proj₁ (lookup' xs i)
lookup' (more sf xs sr) ⟪2₁ i 1₁⟫ = proj₂ (lookup' xs i)
lookup' (more sf xs sr) ⟪1₁ i 3₂⟫ = proj₁ (lookup' xs i)
lookup' (more sf xs sr) ⟪2₁ i 2₂⟫ = proj₂ (lookup' xs i)
lookup' (more sf xs sr) ⟪2₂ i 2₁⟫ = proj₁ (lookup' xs i)
lookup' (more sf xs sr) ⟪3₂ i 1₁⟫ = proj₂ (lookup' xs i)
lookup' (more sf xs sr) ⟪2₂ i 3₂⟫ = proj₁ (lookup' xs i)
lookup' (more sf xs sr) ⟪3₂ i 2₂⟫ = proj₂ (lookup' xs i)

{-
Idx' (D2 ⟨ D1 ⟨ n ⟩ D2 ⟩ D1)
(0₂ ⇐)
(1₂ ⇐)
⟪2₂ (0₁ ⇐) 2₁⟫
⟪3₂ (0₁ ⇐) 1₁⟫
⟪2₂ (⇒ 1₂) 2₁⟫
⟪3₂ (⇒ 1₂) 1₁⟫
⟪2₂ (⇒ 0₂) 2₁⟫
⟪3₂ (⇒ 0₂) 1₁⟫
        (⇒ 0₁)
-}
{-# OPTIONS --rewriting #-}
module RedundantBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to iz; suc to is)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

2* : ℕ → ℕ
2* zero    = 0
2* (suc n) = suc (suc (2* n))

suc-pred : ∀ n → n ≢ 0 → suc (pred n) ≡ n
suc-pred zero    neq = ⊥-elim (neq refl)
suc-pred (suc n) neq = refl

data Digit : Set where
    D1 : Digit
    D2 : Digit
    D3 : Digit

-- Redundant binary numbers (least significant digit first)
data RBinary : Set where
    B0  : RBinary
    _⟨_⟩ : Digit → RBinary → RBinary

DtoN : Digit → ℕ
DtoN D1 = 1
DtoN D2 = 2
DtoN D3 = 3

toN : RBinary → ℕ
toN B0        = 0
toN (d ⟨ n ⟩) = DtoN d + 2* (toN n)

inc : RBinary → RBinary
inc B0         = D1 ⟨ B0 ⟩
inc (D1 ⟨ n ⟩) = D2 ⟨ n ⟩
inc (D2 ⟨ n ⟩) = D3 ⟨ n ⟩
inc (D3 ⟨ n ⟩) = D2 ⟨ inc n ⟩

dec : RBinary → RBinary
dec B0              = B0
dec (D1 ⟨ B0 ⟩)      = B0
dec (D1 ⟨ d ⟨ n ⟩ ⟩) = D2 ⟨ dec (d ⟨ n ⟩) ⟩
dec (D2 ⟨ n ⟩)       = D1 ⟨ n ⟩
dec (D3 ⟨ n ⟩)       = D2 ⟨ n ⟩

fromN : ℕ → RBinary
fromN zero    = B0
fromN (suc n) = inc (fromN n)

d⟨n⟩-nonzero : ∀ d n → toN (d ⟨ n ⟩) ≢ 0
d⟨n⟩-nonzero D1 n ()
d⟨n⟩-nonzero D2 n ()
d⟨n⟩-nonzero D3 n ()

inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
inc-correct B0         = refl
inc-correct (D1 ⟨ n ⟩) = refl
inc-correct (D2 ⟨ n ⟩) = refl
inc-correct (D3 ⟨ n ⟩) = cong suc (cong suc (cong 2* (inc-correct n)))

{-# REWRITE inc-correct #-}

dec-correct : ∀ n → toN (dec n) ≡ pred (toN n)
dec-correct B0              = refl
dec-correct (D1 ⟨ B0 ⟩)      = refl
dec-correct (D1 ⟨ d ⟨ n ⟩ ⟩) = cong 2* (trans (cong suc (dec-correct (d ⟨ n ⟩)))
                                             (suc-pred (DtoN d + 2* (toN n)) (d⟨n⟩-nonzero d n)))
dec-correct (D2 ⟨ n ⟩)       = refl
dec-correct (D3 ⟨ n ⟩)       = refl

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero    = refl
toN-fromN (suc n) = trans (inc-correct (fromN n)) (cong suc (toN-fromN n))

zero-unique : ∀ x → toN x ≡ 0 → x ≡ B0
zero-unique B0 refl = refl
zero-unique (D1 ⟨ n ⟩) ()
zero-unique (D2 ⟨ n ⟩) ()
zero-unique (D3 ⟨ n ⟩) ()

redundant : ∃₂ λ x y → (x ≢ y) × (toN x ≡ toN y )
redundant = (D3 ⟨ B0 ⟩) , ((D1 ⟨ D1 ⟨ B0 ⟩ ⟩) , (λ ()) , refl)

dec-inc≢id : ∃ λ n → n ≢ dec (inc n)
dec-inc≢id = (D3 ⟨ B0 ⟩) , λ ()

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

data Peano-View : RBinary → Set where
    as-zero : Peano-View B0
    as-succ : ∀ {n} → (i : RBinary) → (p : suc (toN i) ≡ toN n) → Peano-View n

view : ∀ n → Peano-View n
view B0 = as-zero
view (d ⟨ n ⟩) = as-succ (dec (d ⟨ n ⟩)) (trans (cong suc (dec-correct (d ⟨ n ⟩))) (suc-pred (toN (d ⟨ n ⟩)) (d⟨n⟩-nonzero d n)))

VtoN : ∀ {n} → Peano-View n → ℕ
VtoN as-zero = 0
VtoN (as-succ n p) = suc (toN n)

view-correct : ∀ n → VtoN (view n) ≡ toN n
view-correct B0 = refl
view-correct (d ⟨ n ⟩) = trans (cong suc (dec-correct (d ⟨ n ⟩))) (suc-pred (toN (d ⟨ n ⟩)) (d⟨n⟩-nonzero d n))

-- Random Access Lists (RAL) indexed by Redundant binary
data Some (A : Set) : Digit → Set where
    one   : A →         Some A D1
    two   : A → A →     Some A D2
    three : A → A → A → Some A D3

data RAL (A : Set) : RBinary → Set where
    nil  :                                      RAL A B0
    more : ∀ {d n} → Some A d → RAL (A × A) n → RAL A (d ⟨ n ⟩)

cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
cons x nil                        = more (one x) nil
cons x (more (one x₁) xs)         = more (two x x₁) xs
cons x (more (two x₁ x₂) xs)      = more (three x x₁ x₂) xs
cons x (more (three x₁ x₂ x₃) xs) = more (two x x₁) (cons (x₂ , x₃) xs)

-- -- This version does not accept all shapes of RAL due to inc-gap
-- head : ∀ {A n} → RAL A (inc n) → A
-- head {_} {B0}      (more (one x) xs)         = x
-- head {_} {D1 ⟨ n ⟩} (more (two x x₁) xs)      = x
-- head {_} {D2 ⟨ n ⟩} (more (three x x₁ x₂) xs) = x
-- head {_} {D3 ⟨ n ⟩} (more (two x x₁) xs)      = x

more-nonzero : ∀ {A d n} → RAL A (d ⟨ n ⟩) → (toN (d ⟨ n ⟩) ≢ 0)
more-nonzero {_} {d} {n} _ p = contradiction (zero-unique (d ⟨ n ⟩) p) λ ()

head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head nil                       nz = contradiction refl nz
head (more (one x) xs)         nz = x
head (more (two x x₁) xs)      nz = x
head (more (three x x₁ x₂) xs) nz = x

tail : ∀ {A n} → RAL A n → RAL A (dec n)
tail nil                       = nil
tail (more (one x) nil)        = nil
tail (more (one x) xs@(more _ _)) =
    let (x₁ , x₂) = head xs (more-nonzero xs)
    in  more (two x₁ x₂) (tail xs)
tail (more (two x x₁) xs)      = more (one x₁) xs
tail (more (three x x₁ x₂) xs) = more (two x₁ x₂) xs

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

data Idx : RBinary → Set where
    0b₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩)
    _1₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)
    _2₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)
    0b₂ : ∀ {n} →         Idx (D2 ⟨ n ⟩)
    1b₂ : ∀ {n} →         Idx (D2 ⟨ n ⟩)
    _2₂ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩)
    _3₂ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩)
    0b₃ : ∀ {n} →         Idx (D3 ⟨ n ⟩)
    1b₃ : ∀ {n} →         Idx (D3 ⟨ n ⟩)
    2b₃ : ∀ {n} →         Idx (D3 ⟨ n ⟩)
    _3₃ : ∀ {n} → Idx n → Idx (D3 ⟨ n ⟩)
    _4₃ : ∀ {n} → Idx n → Idx (D3 ⟨ n ⟩)

lookup : ∀ {A n} → RAL A n → Idx n → A
lookup nil                       ()
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
toF 0b₁    = iz
toF (i 1₁) = is ((toF i) ∙2+0)
toF (i 2₁) = is ((toF i) ∙2+1)
toF 0b₂    = iz
toF 1b₂    = is iz
toF (i 2₂) = is (is ((toF i) ∙2+0))
toF (i 3₂) = is (is ((toF i) ∙2+1))
toF 0b₃    = iz
toF 1b₃    = is iz
toF 2b₃    = is (is iz)
toF (i 3₃) = is (is (is ((toF i) ∙2+0)))
toF (i 4₃) = is (is (is ((toF i) ∙2+1)))

fromF : ∀ {n} → Fin (toN n) → Idx n
fromF {D1 ⟨ n ⟩} iz = 0b₁
fromF {D1 ⟨ n ⟩} (is i) with i /2
... | j , iz    = (fromF j) 1₁
... | j , is iz = (fromF j) 2₁
fromF {D2 ⟨ n ⟩} iz = 0b₂
fromF {D2 ⟨ n ⟩} (is iz) = 1b₂
fromF {D2 ⟨ n ⟩} (is (is i)) with i /2
... | j , iz    = (fromF j) 2₂
... | j , is iz = (fromF j) 3₂
fromF {D3 ⟨ n ⟩} iz = 0b₃
fromF {D3 ⟨ n ⟩} (is iz) = 1b₃
fromF {D3 ⟨ n ⟩} (is (is iz)) = 2b₃
fromF {D3 ⟨ n ⟩} (is (is (is i))) with i /2
... | j , iz    = (fromF j) 3₃
... | j , is iz = (fromF j) 4₃

izero : ∀ {n} → (toN n ≢ 0) → Idx n
izero {B0}      nz = ⊥-elim (nz refl)
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
isucc (i 3₂) = i 4₃
isucc 0b₃ = 1b₂
isucc 1b₃ = (izero λ ()) 2₂
isucc 2b₃ = (izero λ ()) 3₂
isucc (i 3₃) = (isucc i) 2₂
isucc (i 4₃) = (isucc i) 3₂

ishift : ∀ {n} → Idx (dec n) → Idx n
ishift {D1 ⟨ d ⟨ n ⟩ ⟩} 0b₂ = (izero (d⟨n⟩-nonzero d n)) 1₁
ishift {D1 ⟨ d ⟨ n ⟩ ⟩} 1b₂ = (izero (d⟨n⟩-nonzero d n)) 2₁
ishift {D1 ⟨ d ⟨ n ⟩ ⟩} (i 2₂) = (ishift i) 1₁
ishift {D1 ⟨ d ⟨ n ⟩ ⟩} (i 3₂) = (ishift i) 2₁
ishift {D2 ⟨ n ⟩} 0b₁ = 1b₂
ishift {D2 ⟨ n ⟩} (i 1₁) = i 2₂
ishift {D2 ⟨ n ⟩} (i 2₁) = i 3₂
ishift {D3 ⟨ n ⟩} 0b₂ = 1b₃
ishift {D3 ⟨ n ⟩} 1b₂ = 2b₃
ishift {D3 ⟨ n ⟩} (i 2₂) = i 3₃
ishift {D3 ⟨ n ⟩} (i 3₂) = i 4₃

-- izero-correct : ∀ {n} → (nz : toN n ≢ 0) → toF (izero {n} nz) ≡ {!   !}

isucc-correct : ∀ {n} → (i : Idx n) → toF (isucc i) ≡ is (toF i)
isucc-correct 0b₁ = refl
isucc-correct (i 1₁) = refl
isucc-correct (i 2₁) = refl
isucc-correct 0b₂ = refl
isucc-correct 1b₂ = refl
isucc-correct (i 2₂) = refl
isucc-correct (i 3₂) = refl
isucc-correct 0b₃ = refl
isucc-correct 1b₃ = cong is (cong is {!   !})
isucc-correct 2b₃ = cong is (cong is {!   !})
isucc-correct (i 3₃) = cong is (cong is (cong _∙2+0 (isucc-correct i)))
isucc-correct (i 4₃) = cong is (cong is (cong _∙2+1 (isucc-correct i)))

-- ishift-correct : ∀ {n} → (i : Idx (dec n)) → toF (ishift i) ≡ {!   !} (toF i)

lookup-izero : ∀ {A n} → (x : A) → (xs : RAL A n) → x ≡ lookup (cons x xs) (izero λ ())
lookup-izero _ nil                       = refl
lookup-izero _ (more (one x) xs)         = refl
lookup-izero _ (more (two x x₁) xs)      = refl
lookup-izero _ (more (three x x₁ x₂) xs) = refl

lookup-isucc : ∀ {A n} → (x : A) → (xs : RAL A n) → (i : Idx n) → lookup xs i ≡ lookup (cons x xs) (isucc i)
lookup-isucc _ nil                       ()
lookup-isucc _ (more (one x) xs)         0b₁    = refl
lookup-isucc _ (more (one x) xs)         (i 1₁) = refl
lookup-isucc _ (more (one x) xs)         (i 2₁) = refl
lookup-isucc _ (more (two x x₁) xs)      0b₂    = refl
lookup-isucc _ (more (two x x₁) xs)      1b₂    = refl
lookup-isucc _ (more (two x x₁) xs)      (i 2₂) = refl
lookup-isucc _ (more (two x x₁) xs)      (i 3₂) = refl
lookup-isucc _ (more (three x x₁ x₂) xs) 0b₃    = refl
lookup-isucc _ (more (three x x₁ x₂) xs) 1b₃    = cong proj₁ (lookup-izero (x₁ , x₂) xs)
lookup-isucc _ (more (three x x₁ x₂) xs) 2b₃    = cong proj₂ (lookup-izero (x₁ , x₂) xs)
lookup-isucc _ (more (three x x₁ x₂) xs) (i 3₃) = cong proj₁ (lookup-isucc (x₁ , x₂) xs i)
lookup-isucc _ (more (three x x₁ x₂) xs) (i 4₃) = cong proj₂ (lookup-isucc (x₁ , x₂) xs i)

lookup-head : ∀ {A n} → (xs : RAL A n) → (nz : toN n ≢ 0) → head xs nz ≡ lookup xs (izero nz)
lookup-head nil                       nz = contradiction refl nz
lookup-head (more (one x) xs)         nz = refl
lookup-head (more (two x x₁) xs)      nz = refl
lookup-head (more (three x x₁ x₂) xs) nz = refl

lookup-tail : ∀ {A n} → (xs : RAL A n) → (i : Idx (dec n)) → lookup (tail xs) i ≡ lookup xs (ishift i)
lookup-tail (more (one x) (more s xs)) 0b₂ = cong proj₁ (lookup-head (more s xs) (more-nonzero (more s xs)))
lookup-tail (more (one x) (more s xs)) 1b₂ = cong proj₂ (lookup-head (more s xs) (more-nonzero (more s xs)))
lookup-tail (more (one x) (more s xs)) (i 2₂) = cong proj₁ (lookup-tail (more s xs) i)
lookup-tail (more (one x) (more s xs)) (i 3₂) = cong proj₂ (lookup-tail (more s xs) i)
lookup-tail (more (two x x₁) xs) 0b₁ = refl
lookup-tail (more (two x x₁) xs) (i 1₁) = refl
lookup-tail (more (two x x₁) xs) (i 2₁) = refl
lookup-tail (more (three x x₁ x₂) xs) 0b₂ = refl
lookup-tail (more (three x x₁ x₂) xs) 1b₂ = refl
lookup-tail (more (three x x₁ x₂) xs) (i 2₂) = refl
lookup-tail (more (three x x₁ x₂) xs) (i 3₂) = refl

data List-View (A : Set) : RBinary → Set where
    as-nil : List-View A B0
    as-cons : ∀ {n : RBinary} → A → RAL A (dec n) → List-View A n

lview : ∀ {A n} → RAL A n → List-View A n
lview nil = as-nil
lview (more (one x) nil) = as-cons x nil
lview (more (one x) xs@(more _ _)) with lview xs
... | as-cons (x₁ , x₂) xs' = as-cons x (more (two x₁ x₂) xs')
lview (more (two x x₁) xs) = as-cons x (more (one x₁) xs)
lview (more (three x x₁ x₂) xs) = as-cons x (more (two x₁ x₂) xs)

head' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head' xs nz with lview xs
... | as-nil = contradiction refl nz
... | as-cons x xs' = x

tail' : ∀ {A n} → RAL A n → RAL A (dec n)
tail' xs with lview xs
... | as-nil = xs
... | as-cons x xs' = xs'
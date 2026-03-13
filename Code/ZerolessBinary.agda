{-# OPTIONS --rewriting #-}
module ZerolessBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to iz; suc to is)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (suc-injective)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

suc-pred : ∀ n → n ≢ 0 → suc (pred n) ≡ n
suc-pred zero    nz = contradiction refl nz
suc-pred (suc n) nz = refl

2*-injective : ∀ {n m} → 2* n ≡ 2* m → n ≡ m
2*-injective {zero}  {zero}  eq = eq
2*-injective {suc n} {suc m} eq = 
    cong suc (2*-injective (suc-injective (suc-injective eq)))

even≢odd : ∀ {m n} → 2* m ≡ suc (2* n) → ⊥
even≢odd {suc m} {suc n} eq = even≢odd (suc-injective (suc-injective eq))

data Digit : Set where
    D1 : Digit
    D2 : Digit

-- Zeroless binary numbers (least significant digit first)
data ZBinary : Set where
    B0  : ZBinary
    _⟨_⟩ : Digit → ZBinary → ZBinary

DtoN : Digit → ℕ
DtoN D1 = 1
DtoN D2 = 2

toN : ZBinary → ℕ
toN B0       = 0
toN (d ⟨ n ⟩) = DtoN d + 2* (toN n)

inc : ZBinary → ZBinary
inc B0         = D1 ⟨ B0 ⟩
inc (D1 ⟨ n ⟩) = D2 ⟨ n ⟩
inc (D2 ⟨ n ⟩) = D1 ⟨ inc n ⟩

dec : ZBinary → ZBinary
dec B0              = B0
dec (D1 ⟨ B0 ⟩)     = B0
dec (D1 ⟨ d ⟨ n ⟩ ⟩) = D2 ⟨ dec (d ⟨ n ⟩) ⟩
dec (D2 ⟨ n ⟩)      = D1 ⟨ n ⟩

fromN : ℕ → ZBinary
fromN zero    = B0
fromN (suc n) = inc (fromN n)

d⟨n⟩-nonzero : ∀ d n → toN (d ⟨ n ⟩) ≢ 0
d⟨n⟩-nonzero D1 n ()
d⟨n⟩-nonzero D2 n ()

-- Increment corresponds to suc
inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
inc-correct B0         = refl
inc-correct (D1 ⟨ n ⟩) = refl
inc-correct (D2 ⟨ n ⟩) = cong suc (cong 2* (inc-correct n))

-- Decrement corresponds to pred
dec-correct : ∀ n → toN (dec n) ≡ pred (toN n)
dec-correct B0              = refl
dec-correct (D1 ⟨ B0 ⟩)     = refl
dec-correct (D1 ⟨ d ⟨ n ⟩ ⟩) = 
    cong 2* (trans (cong suc (dec-correct (d ⟨ n ⟩))) 
                   (suc-pred (DtoN d + 2* (toN n)) (d⟨n⟩-nonzero d n)))
dec-correct (D2 ⟨ n ⟩)      = refl

dec-inc≡id : ∀ n → dec (inc n) ≡ n
dec-inc≡id B0 = refl
dec-inc≡id (D1 ⟨ n ⟩) = refl
dec-inc≡id (D2 ⟨ B0 ⟩) = refl
dec-inc≡id (D2 ⟨ D1 ⟨ n ⟩ ⟩) = refl
dec-inc≡id (D2 ⟨ D2 ⟨ n ⟩ ⟩) = cong (_⟨_⟩ D2) (dec-inc≡id (D2 ⟨ n ⟩))

toN-fromN : ∀ n → toN (fromN n) ≡ n
toN-fromN zero    = refl
toN-fromN (suc n) =
    trans (inc-correct (fromN n)) (cong suc (toN-fromN n))

nonRedundant : ∀ x y → toN x ≡ toN y → x ≡ y
nonRedundant B0        B0        refl = refl
nonRedundant B0        (D1 ⟨ y ⟩) ()
nonRedundant B0        (D2 ⟨ y ⟩) ()
nonRedundant (D1 ⟨ x ⟩) B0        ()
nonRedundant (D2 ⟨ x ⟩) B0        ()
nonRedundant (D1 ⟨ x ⟩) (D1 ⟨ y ⟩) eq = 
    cong (_⟨_⟩ D1) (nonRedundant x y (2*-injective (suc-injective eq)))
nonRedundant (D1 ⟨ x ⟩) (D2 ⟨ y ⟩) eq = 
    contradiction (suc-injective eq) even≢odd
nonRedundant (D2 ⟨ x ⟩) (D1 ⟨ y ⟩) eq =
    contradiction (suc-injective (sym eq)) even≢odd
nonRedundant (D2 ⟨ x ⟩) (D2 ⟨ y ⟩) eq =
    cong (_⟨_⟩ D2) (nonRedundant x y (2*-injective (suc-injective (suc-injective eq))))

fromN-toN : ∀ n → fromN (toN n) ≡ n
fromN-toN B0        = refl
fromN-toN (D1 ⟨ n ⟩) =
    nonRedundant _ _ (trans (inc-correct (fromN (2* (toN n))))
                            (cong suc (toN-fromN (2* (toN n)))))
fromN-toN (D2 ⟨ n ⟩) = 
    nonRedundant _ _ (trans (inc-correct (inc (fromN (2* (toN n)))))
                            (cong suc (trans (inc-correct (fromN (2* (toN n))))
                                             (cong suc (toN-fromN (2* (toN n)))))))

data Peano-View : ZBinary → Set where
    as-zero : Peano-View B0
    as-succ : (i : ZBinary) → Peano-View (inc i)

view : ∀ n → Peano-View n
view B0 = as-zero
view (D1 ⟨ n ⟩) with view n
... | as-zero = as-succ B0
... | as-succ m = as-succ (D2 ⟨ m ⟩)
view (D2 ⟨ n ⟩) = as-succ (D1 ⟨ n ⟩)

VtoN : ∀ {n} → Peano-View n → ℕ
VtoN as-zero = 0
VtoN (as-succ n) = suc (toN n)

view-correct : ∀ n → VtoN (view n) ≡ toN n
view-correct B0 = refl
view-correct (D1 ⟨ n ⟩) with view n
... | as-zero = refl
... | as-succ m = cong suc (cong 2* (sym (inc-correct m)))
view-correct (D2 ⟨ n ⟩) = refl

-- Random Access Lists (RAL) indexed by Zeroless binary
data Some (A : Set) : Digit → Set where
    one : A     → Some A D1
    two   : A → A → Some A D2

data RAL (A : Set) : ZBinary → Set where
    nil  :                                      RAL A B0
    more : ∀ {d n} → Some A d → RAL (A × A) n → RAL A (d ⟨ n ⟩)

cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
cons x nil                 = more (one x) nil
cons x (more (one y) xs)   = more (two x y) xs
cons x (more (two y z) xs) = more (one x) (cons (y , z) xs)

head : ∀ {A n} → RAL A (inc n) → A
head {_} {B0}       (more (one x) xs)  = x
head {_} {D1 ⟨ n ⟩} (more (two x _) xs) = x
head {_} {D2 ⟨ n ⟩} (more (one x) xs)   = x

-- Generalized head (used in tail')
head' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head' nil                 nz = contradiction refl nz
head' (more (one x) xs)   nz = x
head' (more (two x _) xs) nz = x

more-nonzero : ∀ {A d n} → RAL A (d ⟨ n ⟩) → (toN (d ⟨ n ⟩) ≢ 0)
more-nonzero {_} {d} {n} _ nz =
  contradiction (nonRedundant (d ⟨ n ⟩) B0 nz) λ ()

tail : ∀ {A n} → RAL A (inc n) → RAL A n
tail {A} {B0} xs = nil
tail {A} {D1 ⟨ n ⟩} (more (two x x₁) xs) = more (one x₁) xs
tail {A} {D2 ⟨ n ⟩} (more (one x) xs) = more (two (proj₁ (head xs)) (proj₂ (head xs))) (tail xs)

tail' : ∀ {A n} → RAL A n → RAL A (dec n)
tail' nil                 = nil
tail' (more (one x) nil)  = nil
tail' (more (one x) xs@(more _ _)) =
    let (x₁ , x₂) = head' xs (more-nonzero xs)
    in  more (two x₁ x₂) (tail' xs)
tail' (more (two _ y) xs) = more (one y) xs

-- Indices for Zeroless binary RAL

_∙2+0 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+0   = iz
is i ∙2+0 = is (is (i ∙2+0))

_∙2+1 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+1   = is iz
is i ∙2+1 = is (is (i ∙2+1))

_/2 : ∀ {n} → Fin (2* n) → (Fin n × Fin 2)
_/2 {suc n} iz      = iz , iz
_/2 {suc n} (is iz) = iz , is iz
_/2 {suc n} (is (is i)) with i /2
... | q , r = (is q) , r

data Idx : ZBinary → Set where
    0b₁ : ∀ {n} →         Idx (D1 ⟨ n ⟩)   -- first element
    _1₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)   -- left child
    _2₁ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩)   -- right child
    0b₂ : ∀ {n} →         Idx (D2 ⟨ n ⟩)   -- first element
    1b₂ : ∀ {n} →         Idx (D2 ⟨ n ⟩)   -- second element
    _2₂ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩)   -- left child
    _3₂ : ∀ {n} → Idx n → Idx (D2 ⟨ n ⟩)   -- right child
    
lookup : ∀ {A n} → RAL A n → Idx n → A
lookup nil                   ()
lookup (more (one x) xs)   0b₁    = x
lookup (more (one x) xs)   (i 1₁) = proj₁ (lookup xs i)
lookup (more (one x) xs)   (i 2₁) = proj₂ (lookup xs i)
lookup (more (two x y) xs) 0b₂    = x
lookup (more (two x y) xs) 1b₂    = y
lookup (more (two x y) xs) (i 2₂) = proj₁ (lookup xs i)
lookup (more (two x y) xs) (i 3₂) = proj₂ (lookup xs i)

toF : ∀ {n} → Idx n → Fin (toN n)
toF 0b₁    = iz
toF (i 1₁) = is ((toF i) ∙2+0)
toF (i 2₁) = is ((toF i) ∙2+1)
toF 0b₂    = iz
toF 1b₂    = is iz
toF (i 2₂) = is (is ((toF i) ∙2+0))
toF (i 3₂) = is (is ((toF i) ∙2+1))

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

izero : ∀ {n} → Idx (inc n)
izero {B0}      = 0b₁
izero {D1 ⟨ n ⟩} = 0b₂
izero {D2 ⟨ n ⟩} = 0b₁

isucc : ∀ {n} → Idx n → Idx (inc n)
isucc 0b₁    = 1b₂
isucc (i 1₁) = i 2₂
isucc (i 2₁) = i 3₂
isucc 0b₂    = izero 1₁
isucc 1b₂    = izero 2₁
isucc (i 2₂) = (isucc i) 1₁
isucc (i 3₂) = (isucc i) 2₁

{-# REWRITE inc-correct #-}

izero-correct : ∀ {n} → toF (izero {n}) ≡ iz
izero-correct {B0}       = refl
izero-correct {D1 ⟨ n ⟩} = refl
izero-correct {D2 ⟨ n ⟩} = refl

isucc-correct : ∀ {n} → (i : Idx n) → toF (isucc i) ≡ is (toF i)
isucc-correct 0b₁    = refl
isucc-correct (i 1₁) = refl
isucc-correct (i 2₁) = refl
isucc-correct 0b₂    = cong is (cong _∙2+0 izero-correct)
isucc-correct 1b₂    = cong is (cong _∙2+1 izero-correct)
isucc-correct (i 2₂) = cong is (cong _∙2+0 (isucc-correct i))
isucc-correct (i 3₂) = cong is (cong _∙2+1 (isucc-correct i))

lookup-izero : ∀ {A n} → (x : A) → (xs : RAL A n) → lookup (cons x xs) izero ≡ x
lookup-izero _ nil                  = refl
lookup-izero _ (more (one x) xs)    = refl
lookup-izero _ (more (two x x₁) xs) = refl

lookup-isucc : ∀ {A n} → (x : A) → (xs : RAL A n) → (i : Idx n) → lookup (cons x xs) (isucc i) ≡ lookup xs i
lookup-isucc _ nil                  ()
lookup-isucc _ (more (one x) xs)    0b₁    = refl
lookup-isucc _ (more (one x) xs)    (i 1₁) = refl
lookup-isucc _ (more (one x) xs)    (i 2₁) = refl
lookup-isucc _ (more (two x x₁) xs) 0b₂    = cong proj₁ (lookup-izero (x , x₁) xs)
lookup-isucc _ (more (two x x₁) xs) 1b₂    = cong proj₂ (lookup-izero (x , x₁) xs)
lookup-isucc _ (more (two x x₁) xs) (i 2₂) = cong proj₁ (lookup-isucc (x , x₁) xs i)
lookup-isucc _ (more (two x x₁) xs) (i 3₂) = cong proj₂ (lookup-isucc (x , x₁) xs i)

lookup-head : ∀ {A n} → (xs : RAL A (inc n)) → head xs ≡ lookup xs izero
lookup-head {n = B0}      (more (one x) xs)    = refl
lookup-head {n = D1 ⟨ n ⟩} (more (two x x₁) xs) = refl
lookup-head {n = D2 ⟨ n ⟩} (more (one x) xs)    = refl

lookup-tail : ∀ {A n} → (xs : RAL A (inc n)) → (i : Idx n) → lookup (tail xs) i ≡ lookup xs (isucc i)
lookup-tail {n = D1 ⟨ n ⟩} (more (two x x₁) xs) 0b₁    = refl
lookup-tail {n = D1 ⟨ n ⟩} (more (two x x₁) xs) (i 1₁) = refl
lookup-tail {n = D1 ⟨ n ⟩} (more (two x x₁) xs) (i 2₁) = refl
lookup-tail {n = D2 ⟨ n ⟩} (more (one x) xs)    0b₂    = cong proj₁ (lookup-head xs)
lookup-tail {n = D2 ⟨ n ⟩} (more (one x) xs)    1b₂    = cong proj₂ (lookup-head xs)
lookup-tail {n = D2 ⟨ n ⟩} (more (one x) xs)    (i 2₂) = cong proj₁ (lookup-tail xs i)
lookup-tail {n = D2 ⟨ n ⟩} (more (one x) xs)    (i 3₂) = cong proj₂ (lookup-tail xs i)

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
toF-fromF {D1 ⟨ n ⟩} iz = refl
toF-fromF {D1 ⟨ n ⟩} (is i) with i /2 in eq
... | q , iz    = cong is (trans (cong _∙2+0 (toF-fromF q)) (/2-inv-even i q eq))
... | q , is iz = cong is (trans (cong _∙2+1 (toF-fromF q)) (/2-inv-odd i q eq))
toF-fromF {D2 ⟨ n ⟩} iz = refl
toF-fromF {D2 ⟨ n ⟩} (is iz) = refl
toF-fromF {D2 ⟨ n ⟩} (is (is i)) with i /2 in eq
... | q , iz    = cong is (cong is (trans (cong _∙2+0 (toF-fromF q)) (/2-inv-even i q eq)))
... | q , is iz = cong is (cong is (trans (cong _∙2+1 (toF-fromF q)) (/2-inv-odd i q eq)))

-- data List-View (A : Set) : ZBinary → Set where
--     as-nil : List-View A B0
--     as-cons : ∀ {n : ZBinary} → A → RAL A n → List-View A (inc n)

-- lview : ∀ {A n} → RAL A n → List-View A n
-- lview nil = as-nil
-- lview (more (one x) xs) with lview xs
-- ... | as-nil = as-cons x nil
-- ... | as-cons (x₁ , x₂) xs' = as-cons x (more (two x₁ x₂) xs')
-- lview (more (two x x₁) xs) = as-cons x (more (one x₁) xs)

-- head'' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
-- head'' xs nz with lview xs
-- ... | as-nil = contradiction refl nz
-- ... | as-cons x xs' = x

-- tail'' : ∀ {A n} → RAL A (inc n) → RAL A n
-- tail'' xs with lview xs
-- ... | v = {!   !}

data List-View (A : Set) : ZBinary → Set where
    as-nil : List-View A B0
    as-cons : ∀ {n : ZBinary} → A → RAL A (dec n) → List-View A n

lview : ∀ {A n} → RAL A n → List-View A n
lview nil = as-nil
lview (more (one x) nil) = as-cons x nil
lview (more (one x) xs@(more _ _)) with lview xs
... | as-cons (x₁ , x₂) xs' = as-cons x (more (two x₁ x₂) xs')
lview (more (two x x₁) xs) = as-cons x (more (one x₁) xs)

head'' : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head'' xs nz with lview xs
... | as-nil        = contradiction refl nz
... | as-cons x xs' = x

tail'' : ∀ {A n} → RAL A n → RAL A (dec n)
tail'' xs with lview xs
... | as-nil        = nil
... | as-cons x xs' = xs'
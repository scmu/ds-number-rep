module SymmetricZerolessBinary where

open import Data.Nat using (ℕ; zero; suc; _+_; pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Fin using (Fin; opposite; inject₁; fromℕ) renaming (zero to iz; suc to is; pred to ip)
open import Relation.Binary.PropositionalEquality
import Data.Nat.Properties as NP
open import Data.Nat.Tactic.RingSolver using (solve-∀)

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

addDL : Digit → SZBinary → SZBinary
addDL D1 n = incL n
addDL D2 n = incL (incL n)

add : SZBinary → SZBinary → SZBinary
add B0 m = m
add n B0 = n
add B1 m = incL m
add n B1 = incR n
add (dl ⟨ n ⟩ D1) (D1 ⟨ m ⟩ dr) = dl ⟨ addDL D1 (add n m) ⟩ dr
add (dl ⟨ n ⟩ D2) (D2 ⟨ m ⟩ dr) = dl ⟨ addDL D2 (add n m) ⟩ dr
add (dl ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D1) = dl ⟨ (addDL D1 (add n m)) ⟩ D2
add (D1 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ dr) = D2 ⟨ (addDL D1 (add n m)) ⟩ dr
add (D2 ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D2) = D1 ⟨ (addDL D2 (add n m)) ⟩ D2
add (D2 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ D2) = D2 ⟨ (addDL D2 (add n m)) ⟩ D1
add (D1 ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D2) = D2 ⟨ (addDL D1 (add n m)) ⟩ D2
add (D2 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ D1) = D2 ⟨ (addDL D1 (add n m)) ⟩ D2

data Carry : Set where
    C0 : Carry
    C1 : Carry
    C2 : Carry
    C3 : Carry
    C4 : Carry

CtoN : Carry → ℕ
CtoN C0 = 0
CtoN C1 = 1
CtoN C2 = 2
CtoN C3 = 3
CtoN C4 = 4

addCarryL : Carry → SZBinary → SZBinary
addCarryL C0 n = n
addCarryL C1 n = incL n
addCarryL C2 n = incL (incL n)
addCarryL C3 n = incL (incL (incL n))
addCarryL C4 n = incL (incL (incL (incL n)))

addCarryR : SZBinary → Carry → SZBinary
addCarryR n C0 = n
addCarryR n C1 = incR n
addCarryR n C2 = incR (incR n)
addCarryR n C3 = incR (incR (incR n))
addCarryR n C4 = incR (incR (incR (incR n)))

-- The three inner digits (rear of the left number, incoming carry, front of
-- the right number) hold a total of t ∈ [4..12] units; repackage them into two
-- outer digits and a carry of the same total value, one level deeper:
--   DtoN dL + DtoN dR + 2 * CtoN c' ≡ t.
fromTotal : ℕ → (Digit × Carry × Digit)
fromTotal 4  = D1 , C1 , D1
fromTotal 5  = D1 , C1 , D2
fromTotal 6  = D1 , C2 , D1
fromTotal 7  = D1 , C2 , D2
fromTotal 8  = D1 , C3 , D1
fromTotal 9  = D1 , C3 , D2
fromTotal 10 = D1 , C4 , D1
fromTotal 11 = D1 , C4 , D2
fromTotal 12 = D2 , C4 , D2
fromTotal _  = D1 , C0 , D1

combine : Digit → Digit → Carry → Digit → Digit → (Digit × Carry × Digit)
combine a b c d e = fromTotal (DtoN a + DtoN b + CtoN c + DtoN d + DtoN e)

add3 : SZBinary → Carry → SZBinary → SZBinary
add3 B0 c m = addCarryL c m
add3 B1 c m = incL (addCarryL c m)
add3 n c B0 = addCarryR n c
add3 n c B1 = incR (addCarryR n c)
add3 (a ⟨ n ⟩ b) c (d ⟨ m ⟩ e) with combine a b c d e
... | dL , c' , dR = dL ⟨ (add3 n c' m) ⟩ dR

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
decR-correct (D1 ⟨ n ⟩ D2)  = refl
decR-correct (D2 ⟨ n ⟩ D2)  = refl
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

-- Helpers for add-correct.

2*-distrib : ∀ x y → 2* (x + y) ≡ 2* x + 2* y
2*-distrib zero y    = refl
2*-distrib (suc x) y = cong (λ z → suc (suc z)) (2*-distrib x y)

addDL-correct : ∀ d n → toN (addDL d n) ≡ DtoN d + toN n
addDL-correct D1 n = incL-correct n
addDL-correct D2 n = trans (incL-correct (incL n)) (cong suc (incL-correct n))

red1 : ∀ x y → 2* (1 + (x + y)) ≡ suc (suc (2* x + 2* y))
red1 x y = cong (λ z → suc (suc z)) (2*-distrib x y)

red2 : ∀ x y → 2* (2 + (x + y)) ≡ suc (suc (suc (suc (2* x + 2* y))))
red2 x y = cong (λ z → suc (suc (suc (suc z)))) (2*-distrib x y)

-- Pure additive rearrangements, closed by the ring solver.  In each, a and b
-- stand for 2* (toN n) and 2* (toN m).
slv1  : ∀ p q a b → p + q + (2 + (a + b)) ≡ (p + 1 + a) + (1 + q + b)
slv1  = solve-∀
slv2  : ∀ p q a b → p + q + (4 + (a + b)) ≡ (p + 2 + a) + (2 + q + b)
slv2  = solve-∀
slv3  : ∀ a b → 1 + 2 + (2 + (a + b)) ≡ (1 + 1 + a) + (2 + 1 + b)
slv3  = solve-∀
slv4  : ∀ a b → 2 + 2 + (2 + (a + b)) ≡ (1 + 1 + a) + (2 + 2 + b)
slv4  = solve-∀
slv5  : ∀ a b → 2 + 2 + (2 + (a + b)) ≡ (2 + 1 + a) + (2 + 1 + b)
slv5  = solve-∀
slv6  : ∀ a b → 1 + 2 + (4 + (a + b)) ≡ (2 + 1 + a) + (2 + 2 + b)
slv6  = solve-∀
slv7  : ∀ a b → 2 + 1 + (2 + (a + b)) ≡ (1 + 2 + a) + (1 + 1 + b)
slv7  = solve-∀
slv8  : ∀ a b → 2 + 2 + (2 + (a + b)) ≡ (1 + 2 + a) + (1 + 2 + b)
slv8  = solve-∀
slv9  : ∀ a b → 2 + 2 + (2 + (a + b)) ≡ (2 + 2 + a) + (1 + 1 + b)
slv9  = solve-∀
slv10 : ∀ a b → 2 + 1 + (4 + (a + b)) ≡ (2 + 2 + a) + (1 + 2 + b)
slv10 = solve-∀

add-correct : ∀ n m → toN (add n m) ≡ toN n + toN m
add-correct B0 B0 = refl
add-correct B0 B1 = refl
add-correct B0 (df ⟨ m ⟩ dr) = refl
add-correct B1 B0 = refl
add-correct B1 B1 = refl
add-correct B1 (df ⟨ m ⟩ dr) = incL-correct (df ⟨ m ⟩ dr)
add-correct (df ⟨ n ⟩ dr) B0 = sym (NP.+-identityʳ (toN (df ⟨ n ⟩ dr)))
add-correct (x ⟨ n ⟩ x₁) B1 =
  trans (incR-correct (x ⟨ n ⟩ x₁)) (sym (NP.+-comm (toN (x ⟨ n ⟩ x₁)) 1))
add-correct (dl ⟨ n ⟩ D1) (D1 ⟨ m ⟩ dr) =
  trans (cong (λ z → DtoN dl + DtoN dr + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN dl + DtoN dr + z) (red1 (toN n) (toN m)))
               (slv1 (DtoN dl) (DtoN dr) (2* (toN n)) (2* (toN m))))
add-correct (dl ⟨ n ⟩ D2) (D2 ⟨ m ⟩ dr) =
  trans (cong (λ z → DtoN dl + DtoN dr + 2* z)
              (trans (addDL-correct D2 (add n m)) (cong (DtoN D2 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN dl + DtoN dr + z) (red2 (toN n) (toN m)))
               (slv2 (DtoN dl) (DtoN dr) (2* (toN n)) (2* (toN m))))
add-correct (D1 ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D1) =
  trans (cong (λ z → DtoN D1 + DtoN D2 + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D1 + DtoN D2 + z) (red1 (toN n) (toN m)))
               (slv3 (2* (toN n)) (2* (toN m))))
add-correct (D1 ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D2) =
  trans (cong (λ z → DtoN D2 + DtoN D2 + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D2 + DtoN D2 + z) (red1 (toN n) (toN m)))
               (slv4 (2* (toN n)) (2* (toN m))))
add-correct (D2 ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D1) =
  trans (cong (λ z → DtoN D2 + DtoN D2 + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D2 + DtoN D2 + z) (red1 (toN n) (toN m)))
               (slv5 (2* (toN n)) (2* (toN m))))
add-correct (D2 ⟨ n ⟩ D1) (D2 ⟨ m ⟩ D2) =
  trans (cong (λ z → DtoN D1 + DtoN D2 + 2* z)
              (trans (addDL-correct D2 (add n m)) (cong (DtoN D2 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D1 + DtoN D2 + z) (red2 (toN n) (toN m)))
               (slv6 (2* (toN n)) (2* (toN m))))
add-correct (D1 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ D1) =
  trans (cong (λ z → DtoN D2 + DtoN D1 + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D2 + DtoN D1 + z) (red1 (toN n) (toN m)))
               (slv7 (2* (toN n)) (2* (toN m))))
add-correct (D1 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ D2) =
  trans (cong (λ z → DtoN D2 + DtoN D2 + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D2 + DtoN D2 + z) (red1 (toN n) (toN m)))
               (slv8 (2* (toN n)) (2* (toN m))))
add-correct (D2 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ D1) =
  trans (cong (λ z → DtoN D2 + DtoN D2 + 2* z)
              (trans (addDL-correct D1 (add n m)) (cong (DtoN D1 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D2 + DtoN D2 + z) (red1 (toN n) (toN m)))
               (slv9 (2* (toN n)) (2* (toN m))))
add-correct (D2 ⟨ n ⟩ D2) (D1 ⟨ m ⟩ D2) =
  trans (cong (λ z → DtoN D2 + DtoN D1 + 2* z)
              (trans (addDL-correct D2 (add n m)) (cong (DtoN D2 +_) (add-correct n m))))
        (trans (cong (λ z → DtoN D2 + DtoN D1 + z) (red2 (toN n) (toN m)))
               (slv10 (2* (toN n)) (2* (toN m))))


data Some (A : Set) : Digit → Set where
    one   : A →         Some A D1
    two   : A → A →     Some A D2

data RAL (A : Set) : SZBinary → Set where
    nil       : RAL A B0
    singleton : A → RAL A B1
    more      : ∀ {df n dr} → Some A df → RAL (A × A) n → Some A dr → RAL A (df ⟨ n ⟩ dr)

cons : ∀ {A n} → A → RAL A n → RAL A (incL n)
cons x nil                     = singleton x
cons x (singleton x₁)          = more (one x) nil (one x₁)
cons x (more (one x₁) xs s)    = more (two x x₁) xs s
cons x (more (two x₁ x₂) xs s) = more (one x) (cons (x₁ , x₂) xs) s

snoc : ∀ {A n} → RAL A n → A → RAL A (incR n)
snoc nil x                     = singleton x
snoc (singleton x₁) x          = more (one x₁) nil (one x)
snoc (more s xs (one x₁)) x    = more s xs (two x₁ x)
snoc (more s xs (two x₁ x₂)) x = more s (snoc xs (x₁ , x₂)) (one x)

more-nonzero : ∀ {A df n dr} → RAL A (df ⟨ n ⟩ dr) → (toN (df ⟨ n ⟩ dr) ≢ 0)
more-nonzero (more (one _)   _ _) = λ ()
more-nonzero (more (two _ _) _ _) = λ ()

head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head nil nz                    = ⊥-elim (nz refl)
head (singleton x) nz          = x
head (more (one x) xs s) nz    = x
head (more (two x x₁) xs s) nz = x

last : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
last nil nz                    = ⊥-elim (nz refl)
last (singleton x) nz          = x
last (more s xs (one x)) nz    = x
last (more s xs (two x x₁)) nz = x₁

tail : ∀ {A n} → RAL A n → RAL A (decL n)
tail nil           = nil
tail (singleton x) = nil
tail (more (one x) nil (one x₁))            = singleton x₁
tail (more (one x) nil (two x₁ x₂))         = more (one x₁) nil (one x₂)
tail (more (one x) (singleton (x₁ , x₂)) s) = more (two x₁ x₂) nil s
tail (more (one x) xs@(more _ _ _) s) =
    let (x₁ , x₂) = head xs (more-nonzero xs)
    in  more (two x₁ x₂) (tail xs) s
tail (more (two x x₁) xs s)                 = more (one x₁) xs s

init : ∀ {A n} → RAL A n → RAL A (decR n)
init nil           = nil
init (singleton x) = nil
init (more s xs (two x x₁))                 = more s xs (one x)
init (more s (singleton (x , x₁)) (one x₂)) = more s nil (two x x₁)
init (more s xs@(more _ _ _) (one x₂)) =
    let (x , x₁) = last xs (more-nonzero xs)
    in  more s (init xs) (two x x₁)
init (more (one x) nil (one x₁))            = singleton x
init (more (two x x₁) nil (one x₂))         = more (one x) nil (one x₁)

_∙2+0 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+0   = iz
is i ∙2+0 = is (is (i ∙2+0))

_∙2+1 : ∀ {n} → Fin n → Fin (2* n)
iz ∙2+1   = is iz
is i ∙2+1 = is (is (i ∙2+1))

data LastView : ∀ {n} → Fin (suc n) → Set where
    is-il : ∀ {n}             → LastView {n} (fromℕ n)
    is-ij : ∀ {n} (i : Fin n) → LastView (inject₁ i)

lview : ∀ {n} (i : Fin (suc n)) → LastView i
lview {zero}  iz     = is-il
lview {suc n} iz     = is-ij iz
lview {suc n} (is i) with lview i
... | is-ij j = is-ij (is j)
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
    ⟪1₁_2₁⟫ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D1) -- proj₁
    ⟪2₁_1₁⟫ : ∀ {n} → Idx n → Idx (D1 ⟨ n ⟩ D1) -- proj₂
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
fromF {D1 ⟨ n ⟩ D1} (is i) with lview i
... | is-il   = 0r₁₁
... | is-ij j with j /2
...     | q , iz    = ⟪1₁ fromF q 2₁⟫
...     | q , is iz = ⟪2₁ fromF q 1₁⟫
fromF {D1 ⟨ n ⟩ D2} iz = 0f₁₂
fromF {D1 ⟨ n ⟩ D2} (is i) with lview i
... | is-il   = 0r₁₂
... | is-ij j with lview j
...     | is-il   = 1r₁₂
...     | is-ij k with k /2
...         | q , iz    = ⟪1₁ fromF q 3₂⟫
...         | q , is iz = ⟪2₁ fromF q 2₂⟫
fromF {D2 ⟨ n ⟩ D1} iz       = 0f₂₁
fromF {D2 ⟨ n ⟩ D1} (is iz)  = 1f₂₁
fromF {D2 ⟨ n ⟩ D1} (is (is i)) with lview i
... | is-il   = 0r₂₁
... | is-ij j with j /2
...     | q , iz    = ⟪2₂ fromF q 2₁⟫
...     | q , is iz = ⟪3₂ fromF q 1₁⟫
fromF {D2 ⟨ n ⟩ D2} iz       = 0f₂₂
fromF {D2 ⟨ n ⟩ D2} (is iz)  = 1f₂₂
fromF {D2 ⟨ n ⟩ D2} (is (is i)) with lview i
... | is-il   = 0r₂₂
... | is-ij j with lview j
...     | is-il   = 1r₂₂
...     | is-ij k with k /2
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
toF-fromF {D1 ⟨ n ⟩ D1} (is i) with lview i
... | is-il = refl
... | is-ij j with j /2 in eq
...     | q , iz    = cong (λ i → is (inject₁ i)) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even j q eq))
...     | q , is iz = cong (λ i → is (inject₁ i)) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd j q eq))
toF-fromF {D1 ⟨ n ⟩ D2} iz = refl
toF-fromF {D1 ⟨ n ⟩ D2} (is i) with lview i
... | is-il = refl
... | is-ij j with lview j
...     | is-il = refl
...     | is-ij k with k /2 in eq
...         | q , iz    = cong (λ i → is (inject₁ (inject₁ i))) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even k q eq))
...         | q , is iz = cong (λ i → is (inject₁ (inject₁ i))) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd k q eq))
toF-fromF {D2 ⟨ n ⟩ D1} iz      = refl
toF-fromF {D2 ⟨ n ⟩ D1} (is iz) = refl
toF-fromF {D2 ⟨ n ⟩ D1} (is (is i)) with lview i
... | is-il = refl
... | is-ij j with j /2 in eq
...     | q , iz    = cong (λ i → is (is (inject₁ i))) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even j q eq))
...     | q , is iz = cong (λ i → is (is (inject₁ i))) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd j q eq))
toF-fromF {D2 ⟨ n ⟩ D2} iz      = refl
toF-fromF {D2 ⟨ n ⟩ D2} (is iz) = refl
toF-fromF {D2 ⟨ n ⟩ D2} (is (is i)) with lview i
... | is-il = refl
... | is-ij j with lview j
...     | is-il = refl
...     | is-ij k with k /2 in eq
...         | q , iz    = cong (λ i → is (is (inject₁ (inject₁ i)))) (trans (cong _∙2+0 (toF-fromF {n} q)) (/2-inv-even k q eq))
...         | q , is iz = cong (λ i → is (is (inject₁ (inject₁ i)))) (trans (cong _∙2+1 (toF-fromF {n} q)) (/2-inv-odd k q eq))

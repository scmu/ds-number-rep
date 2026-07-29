{-# OPTIONS --rewriting #-}
module ReindexRedundantBinary where

open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Fin using (Fin; toℕ; inject₁) renaming (zero to iz; suc to is)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Fin.Properties using (toℕ-injective)

open import RedundantBinary


-- Fin helpers
toℕ-∙2+0 : ∀ {m} (i : Fin m) → toℕ (i ∙2+0) ≡ 2* (toℕ i)
toℕ-∙2+0 iz     = refl
toℕ-∙2+0 (is i) = cong (λ z → suc (suc z)) (toℕ-∙2+0 i)

toℕ-∙2+1 : ∀ {m} (i : Fin m) → toℕ (i ∙2+1) ≡ suc (2* (toℕ i))
toℕ-∙2+1 iz     = refl
toℕ-∙2+1 (is i) = cong (λ z → suc (suc z)) (toℕ-∙2+1 i)

/2-∙2+0 : ∀ {m} (x : Fin m) → (x ∙2+0) /2 ≡ (x , iz)
/2-∙2+0 iz     = refl
/2-∙2+0 (is x) rewrite /2-∙2+0 x = refl

/2-∙2+1 : ∀ {m} (x : Fin m) → (x ∙2+1) /2 ≡ (x , is iz)
/2-∙2+1 iz     = refl
/2-∙2+1 (is x) rewrite /2-∙2+1 x = refl

recombine : ∀ {m} → Fin m × Fin 2 → Fin (2* m)
recombine (q , iz)         = q ∙2+0
recombine (q , is iz)      = q ∙2+1
recombine (q , is (is ()))

/2-inverse : ∀ {m} (i : Fin (2* m)) → recombine (i /2) ≡ i
/2-inverse {suc m} iz          = refl
/2-inverse {suc m} (is iz)     = refl
/2-inverse {suc m} (is (is i)) with i /2 in eq
... | q , iz          = cong (λ z → is (is z)) (trans (cong recombine (sym eq)) (/2-inverse i))
... | q , is iz       = cong (λ z → is (is z)) (trans (cong recombine (sym eq)) (/2-inverse i))
... | q , is (is ())

toℕ-subst : ∀ {m m'} (eq : m ≡ m') (i : Fin m) → toℕ (subst Fin eq i) ≡ toℕ i
toℕ-subst refl i = refl


fromF-toF : ∀ {n} (i : Idx n) → fromF (toF i) ≡ i
fromF-toF 0b₁    = refl
fromF-toF (i 1₁) rewrite /2-∙2+0 (toF i) = cong (λ z → z 1₁) (fromF-toF i)
fromF-toF (i 2₁) rewrite /2-∙2+1 (toF i) = cong (λ z → z 2₁) (fromF-toF i)
fromF-toF 0b₂    = refl
fromF-toF 1b₂    = refl
fromF-toF (i 2₂) rewrite /2-∙2+0 (toF i) = cong (λ z → z 2₂) (fromF-toF i)
fromF-toF (i 3₂) rewrite /2-∙2+1 (toF i) = cong (λ z → z 3₂) (fromF-toF i)
fromF-toF 0b₃    = refl
fromF-toF 1b₃    = refl
fromF-toF 2b₃    = refl
fromF-toF (i 3₃) rewrite /2-∙2+0 (toF i) = cong (λ z → z 3₃) (fromF-toF i)
fromF-toF (i 4₃) rewrite /2-∙2+1 (toF i) = cong (λ z → z 4₃) (fromF-toF i)

toF-fromF : ∀ {n} (i : Fin (toN n)) → toF (fromF {n} i) ≡ i
toF-fromF {B0} ()
toF-fromF {D1 ⟨ m ⟩} iz     = refl
toF-fromF {D1 ⟨ m ⟩} (is i) with i /2 in eq
... | j , iz          = cong is (trans (cong (λ z → z ∙2+0) (toF-fromF {m} j)) (trans (cong recombine (sym eq)) (/2-inverse i)))
... | j , is iz       = cong is (trans (cong (λ z → z ∙2+1) (toF-fromF {m} j)) (trans (cong recombine (sym eq)) (/2-inverse i)))
... | j , is (is ())
toF-fromF {D2 ⟨ m ⟩} iz          = refl
toF-fromF {D2 ⟨ m ⟩} (is iz)     = refl
toF-fromF {D2 ⟨ m ⟩} (is (is i)) with i /2 in eq
... | j , iz          = cong (λ z → is (is z)) (trans (cong (λ z → z ∙2+0) (toF-fromF {m} j)) (trans (cong recombine (sym eq)) (/2-inverse i)))
... | j , is iz       = cong (λ z → is (is z)) (trans (cong (λ z → z ∙2+1) (toF-fromF {m} j)) (trans (cong recombine (sym eq)) (/2-inverse i)))
... | j , is (is ())
toF-fromF {D3 ⟨ m ⟩} iz              = refl
toF-fromF {D3 ⟨ m ⟩} (is iz)         = refl
toF-fromF {D3 ⟨ m ⟩} (is (is iz))    = refl
toF-fromF {D3 ⟨ m ⟩} (is (is (is i))) with i /2 in eq
... | j , iz          = cong (λ z → is (is (is z))) (trans (cong (λ z → z ∙2+0) (toF-fromF {m} j)) (trans (cong recombine (sym eq)) (/2-inverse i)))
... | j , is iz       = cong (λ z → is (is (is z))) (trans (cong (λ z → z ∙2+1) (toF-fromF {m} j)) (trans (cong recombine (sym eq)) (/2-inverse i)))
... | j , is (is ())

toF-injective : ∀ {n} {i j : Idx n} → toF i ≡ toF j → i ≡ j
toF-injective {n} {i} {j} eq =
  trans (sym (fromF-toF i)) (trans (cong fromF eq) (fromF-toF j))

-- reindex and its laws

reindex : ∀ {r r'} → toN r ≡ toN r' → Idx r → Idx r'
reindex eq i = fromF (subst Fin eq (toF i))

reindex-pos : ∀ {r r'} (eq : toN r ≡ toN r') (i : Idx r)
            → toℕ (toF (reindex {r' = r'} eq i)) ≡ toℕ (toF i)
reindex-pos eq i =
  trans (cong toℕ (toF-fromF (subst Fin eq (toF i)))) (toℕ-subst eq (toF i))

reindex-refl : ∀ {r} (i : Idx r) → reindex {r' = r} refl i ≡ i
reindex-refl i = fromF-toF i

subst-∘trans : ∀ {m m' m''} (p : m ≡ m') (q : m' ≡ m'') (x : Fin m)
             → subst Fin q (subst Fin p x) ≡ subst Fin (trans p q) x
subst-∘trans refl q x = refl

reindex-trans : ∀ {r r' r''} (p : toN r ≡ toN r') (q : toN r' ≡ toN r'') (i : Idx r)
              → reindex {r' = r''} q (reindex {r' = r'} p i) ≡ reindex {r' = r''} (trans p q) i
reindex-trans p q i =
  cong fromF (trans (cong (subst Fin q) (toF-fromF (subst Fin p (toF i))))
                    (subst-∘trans p q (toF i)))

trans-sym : ∀ {a} {A : Set a} {x y : A} (eq : x ≡ y) → trans eq (sym eq) ≡ refl
trans-sym refl = refl

reindex-inv : ∀ {r r'} (eq : toN r ≡ toN r') (i : Idx r)
            → reindex {r' = r} (sym eq) (reindex {r' = r'} eq i) ≡ i
reindex-inv {r} {r'} eq i =
  trans (reindex-trans {r' = r'} {r'' = r} eq (sym eq) i)
        (trans (cong (λ z → reindex {r' = r} z i) (trans-sym eq)) (reindex-refl i))

-- ishift explained by reindex
izero'-pos : ∀ {n} (nz : toN n ≢ 0) → toℕ (toF (izero' {n} nz)) ≡ 0
izero'-pos {B0}       nz = ⊥-elim (nz refl)
izero'-pos {D1 ⟨ n ⟩} nz = refl
izero'-pos {D2 ⟨ n ⟩} nz = refl
izero'-pos {D3 ⟨ n ⟩} nz = refl

ishift-correct : ∀ {n} (i : Idx (dec n)) → toℕ (toF (ishift i)) ≡ suc (toℕ (toF i))
ishift-correct {D1 ⟨ d ⟨ n ⟩ ⟩} 0b₂ =
  cong suc (trans (toℕ-∙2+0 (toF (izero' {d ⟨ n ⟩} (d⟨n⟩-nonzero d n))))
                  (cong 2* (izero'-pos {d ⟨ n ⟩} (d⟨n⟩-nonzero d n))))
ishift-correct {D1 ⟨ d ⟨ n ⟩ ⟩} 1b₂ =
  cong suc (trans (toℕ-∙2+1 (toF (izero' {d ⟨ n ⟩} (d⟨n⟩-nonzero d n))))
                  (cong (λ z → suc (2* z)) (izero'-pos {d ⟨ n ⟩} (d⟨n⟩-nonzero d n))))
ishift-correct {D1 ⟨ d ⟨ n ⟩ ⟩} (i 2₂)
  rewrite toℕ-∙2+0 (toF (ishift {d ⟨ n ⟩} i)) | toℕ-∙2+0 (toF i) | ishift-correct {d ⟨ n ⟩} i = refl
ishift-correct {D1 ⟨ d ⟨ n ⟩ ⟩} (i 3₂)
  rewrite toℕ-∙2+1 (toF (ishift {d ⟨ n ⟩} i)) | toℕ-∙2+1 (toF i) | ishift-correct {d ⟨ n ⟩} i = refl
ishift-correct {D2 ⟨ n ⟩} 0b₁    = refl
ishift-correct {D2 ⟨ n ⟩} (i 1₁) = refl
ishift-correct {D2 ⟨ n ⟩} (i 2₁) = refl
ishift-correct {D3 ⟨ n ⟩} 0b₂    = refl
ishift-correct {D3 ⟨ n ⟩} 1b₂    = refl
ishift-correct {D3 ⟨ n ⟩} (i 2₂) = refl
ishift-correct {D3 ⟨ n ⟩} (i 3₂) = refl

shift-eq : ∀ n → toN n ≢ 0 → suc (toN (dec n)) ≡ toN n
shift-eq n nz = trans (cong suc (dec-correct n)) (suc-pred (toN n) nz)

ishift-reindex : ∀ {n} (nz : toN n ≢ 0) (i : Idx (dec n)) → ishift i ≡ reindex {r' = n} (shift-eq n nz) (isucc i)
ishift-reindex {n} nz i =
  toF-injective (toℕ-injective
    (trans (ishift-correct {n} i)
           (trans (sym (cong toℕ (isucc-correct i)))
                  (sym (reindex-pos {r' = n} (shift-eq n nz) (isucc i))))))

-- reindex relabels each position into the other numeral's coordinates

_ : reindex {D3 ⟨ B0 ⟩} {D1 ⟨ D1 ⟨ B0 ⟩ ⟩} refl 0b₃ ≡ 0b₁
_ = refl

_ : reindex {D3 ⟨ B0 ⟩} {D1 ⟨ D1 ⟨ B0 ⟩ ⟩} refl 1b₃ ≡ 0b₁ 1₁
_ = refl

_ : reindex {D3 ⟨ B0 ⟩} {D1 ⟨ D1 ⟨ B0 ⟩ ⟩} refl 2b₃ ≡ 0b₁ 2₁
_ = refl

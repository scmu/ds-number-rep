\section{Indexing}
\label{sec:indexing}

\todo{introduce indexing.}

\subsection{Indices as binary numbers}
\label{sec:binary-index}

Just as |Fin n|, the type of naturals below |n|, with |iz : Fin (inc n)| and |is : Fin n → Fin (inc n)| mirroring |zero| and |suc| --- indexes a length-|n| vector, |Idx n| indexes a |BList A n|.
Where |Fin| gives a unary account of the naturals below a bound, |Idx| gives a binary one, laid out along the digits of |n|.

A digit |D1| contributes one local position and two copies of the positions below |n|; a digit |D2| contributes two local positions and the same two copies.
Naming those summands gives |Idx|.
A |D1| digit stores one element and has two ways into the doubled tail, hence one base position |ez1| and two recursive branches |_cA1|, |_cB1|; a |D2| digit stores two elements, hence base positions |ez2|, |eo2| and branches |_cA2|, |_cB2|:
\begin{code}
  data Idx : Binary → Set where
    ez1   : ∀ {n} →          Idx (D1 ∷ n)
    _cA1  : ∀ {n} → Idx n →  Idx (D1 ∷ n)
    _cB1  : ∀ {n} → Idx n →  Idx (D1 ∷ n)
    ez2   : ∀ {n} →          Idx (D2 ∷ n)
    eo2   : ∀ {n} →          Idx (D2 ∷ n)
    _cA2  : ∀ {n} → Idx n →  Idx (D2 ∷ n)
    _cB2  : ∀ {n} → Idx n →  Idx (D2 ∷ n) {-"~~."-}
\end{code}
Counting the constructors of a digit recovers its weight: |D1| contributes |1| base position plus |2| branches into the tail, and |D2| contributes |2| plus |2|.

The function |lookup| follows an index as a path through the list.
A local constructor returns the element stored at this digit; a branch projects one half of the paired tail and recurses:
\begin{code}
  lookup : ∀ {A n} → BList A n → Idx n → A
  lookup (one x    ∷ xs)  ez1      = x
  lookup (one x    ∷ xs)  (i cA1)  = proj₁ (lookup xs i)
  lookup (one x    ∷ xs)  (i cB1)  = proj₂ (lookup xs i)
  lookup (two x y  ∷ xs)  ez2      = x
  lookup (two x y  ∷ xs)  eo2      = y
  lookup (two x y  ∷ xs)  (i cA2)  = proj₁ (lookup xs i)
  lookup (two x y  ∷ xs)  (i cB2)  = proj₂ (lookup xs i) {-"~~."-}
\end{code}

An index can be seen as a binary numeral. Reading it outward, |toF| sends |Idx n| to the position it denotes in |Fin (toN n)|.
A local constructor is the first position, or the first or second; a branch doubles the tail's position and sets the low bit.
The postfix operations |_dblO| and |_dblI| send |i| to the even position |2 * i| and the odd position |2 * i + 1|, both below a doubled bound:
\begin{code}
  toF : ∀ {n} → Idx n → Fin (toN n)
  toF ez1      = iz
  toF (i cA1)  = is ((toF i) dblO)
  toF (i cB1)  = is ((toF i) dblI)
  toF ez2      = iz
  toF eo2      = is iz
  toF (i cA2)  = is (is ((toF i) dblO))
  toF (i cB2)  = is (is ((toF i) dblI)) {-"~~."-}
\end{code}

The other direction, |fromF|, sends a |Fin| back to an |Idx|.
Given a position in |Fin (toN n)|, it peels off the current digit by halving.
The auxiliary |_halfF| splits a doubled position into a quotient and a remainder:
\begin{code}
  _halfF : ∀ {n} → Fin (2 * n) → (Fin n × Fin 2)
  iz           halfF = iz  , iz
  is iz        halfF = iz  , is iz
  is (is i)    with i halfF
  ... | q , r  = is q , r {-"~~,"-}

  fromF : ∀ {n} → Fin (toN n) → Idx n
  fromF {D1 ∷ n} iz           = ez1
  fromF {D1 ∷ n} (is i)       with i halfF
  ... | j , iz    = (fromF j) cA1
  ... | j , is iz = (fromF j) cB1
  fromF {D2 ∷ n} iz           = ez2
  fromF {D2 ∷ n} (is iz)      = eo2
  fromF {D2 ∷ n} (is (is i))  with i halfF
  ... | j , iz    = (fromF j) cA2
  ... | j , is iz = (fromF j) cB2 {-"~~."-}
\end{code}
This shows that the outward reading recovers every |Fin| position,
\begin{code}
  toF-fromF : ∀ {n} (i : Fin (toN n)) → toF (fromF i) ≡ i {-"~~,"-}
\end{code}
and the same induction on |Idx| gives the other round trip, |fromF (toF i) ≡ i|.
With both maps on the page, |Idx n| and |Fin (toN n)| are two notations for one finite range: |Fin| writes it in unary, and |Idx| writes it in the digits of |n|.

Because |Idx| is a number system, it carries its own arithmetic.
The zero index |izero| points at the element |cons| has just placed at the front, and |isucc| is successor on positions:
\begin{code}
  izero : ∀ {n} → Idx (inc n)
  izero {B0}      = ez1
  izero {D1 ∷ n}  = ez2
  izero {D2 ∷ n}  = ez1 {-"~~,"-}

  isucc : ∀ {n} → Idx n → Idx (inc n)
  isucc ez1      = eo2
  isucc (i cA1)  = i cA2
  isucc (i cB1)  = i cB2
  isucc ez2      = izero cA1
  isucc eo2      = izero cB1
  isucc (i cA2)  = (isucc i) cA1
  isucc (i cB2)  = (isucc i) cB1 {-"~~."-}
\end{code}
The clauses for a |D1| digit retag it as a |D2| digit, which is what |inc| does to the size.
\todo{explain isucc behaves like suc}
\begin{code}
  isucc-correct : ∀ {n} (i : Idx n) → toF (isucc i) ≡ is (toF i) {-"~~."-}
\end{code}

These connect to the container through the specification of a one-sided flexible array:
\begin{spec}
  lookup-izero  : ∀ {A n} (x : A) (xs : BList A n)
                → lookup (cons x xs) izero ≡ x
  lookup-isucc  : ∀ {A n} (x : A) (xs : BList A n) (i : Idx n)
                → lookup (cons x xs) (isucc i) ≡ lookup xs i
  lookup-head   : ∀ {A n} (xs : BList A (inc n))
                → head xs ≡ lookup xs izero
  lookup-tail   : ∀ {A n} (xs : BList A (inc n)) (i : Idx n)
                → lookup (tail xs) i ≡ lookup xs (isucc i) {-"~~."-}
\end{spec}
The move from unary lists to binary numbers for sizes thus also yields binary numbers for positions.
|Idx| is the ornament of the zeroless |Binary| in the index direction, just as |BList| is its ornament in the data direction, both cut to the same digits.

\subsection{Indices for redundant binary}
\label{sec:redundant-index}

A |D3| digit stores three elements and has two ways into the doubled tail.
The index gains three base positions and two branches:
\begin{code}
  ez3   : ∀ {n} →          Idx (D3 ∷ n)
  eo3   : ∀ {n} →          Idx (D3 ∷ n)
  et3   : ∀ {n} →          Idx (D3 ∷ n)
  _cA3  : ∀ {n} → Idx n →  Idx (D3 ∷ n)
  _cB3  : ∀ {n} → Idx n →  Idx (D3 ∷ n) {-"~~."-}
\end{code}
|lookup|, |toF|, and |fromF| extend those already given in Section~\ref{sec:binary-index}.
The round trips still hold for a fixed numeral, so |Idx n| and |Fin (toN n)| are still two writings of one range.

Each numeral has its own |Idx|.
Both |D3 ∷ []| and |D1 ∷ D1 ∷ []| denote |3|, so a position below |3| may be written in either family.
|reindex| translates an index from one writing to the other:
\begin{code}
  reindex : ∀ {r r'} → toN r ≡ toN r' → Idx r → Idx r'
  reindex eq i = fromF (subst Fin eq (toF i)) {-"~~."-}
\end{code}
The position denoted by |toF| is unchanged.
The front element is |ez1|, and the other two are the two halves of the element in the tail:
\begin{spec}
  reindex {D3 ∷ B0} {D1 ∷ D1 ∷ B0} refl ez3  ≡ ez1
  reindex {D3 ∷ B0} {D1 ∷ D1 ∷ B0} refl eo3  ≡ (ez1 cA1)
  reindex {D3 ∷ B0} {D1 ∷ D1 ∷ B0} refl et3  ≡ (ez1 cB1) {-"~~."-}
\end{spec}
\todo{avoid explain isucc again?}

|toF (isucc i) ≡ is (toF i)| still holds.

After |tail|, an element that remains has an index of type |Idx (dec n)| in the tail and of type |Idx n| in the original list.
|ishift| sends the first to the second.
Successor steps from |Idx (dec n)| into |Idx (inc (dec n))|; |reindex| then steps to |n|, along the equality of the two values:
\begin{code}
  shift-eq : ∀ n → toN n ≢ 0 → toN (inc (dec n)) ≡ toN n

  ishift : ∀ {n} → Idx (dec n) → Idx n

  ishift-reindex : ∀ {n} (nz : toN n ≢ 0) (i : Idx (dec n))
                 → ishift i ≡ reindex (shift-eq n nz) (isucc i) {-"~~."-}
\end{code}
In the zeroless representation, |inc (dec n)| and |n| are the same numeral, so the relabelling is the identity and |ishift| is |isucc|.
That is the |lookup-tail| law of the previous subsection.
|izero'| is the front position of a non-empty numeral:
\begin{code}
  izero' : ∀ {n} → (n ≢ []) → Idx n {-"~~."-}
\end{code}
The specification is unchanged for |cons|, while |head| and |tail| take the types of Section~\ref{sec:redundant-binary}:
\begin{spec}
  lookup-head   : ∀ {A n} (xs : BList A n) (nz : n ≢ [])
                → head xs nz ≡ lookup xs (izero' nz)
  lookup-tail   : ∀ {A n} (xs : BList A n) (i : Idx (dec n))
                → lookup (tail xs) i ≡ lookup xs (ishift i) {-"~~."-}
\end{spec}

\subsection{Indices for symmetric binary}
\label{sec:symmetric-index}

In the symmetric representation of Section~\ref{sec:sym-binary}, a position lies in one of the outer digits or in the doubled middle.
For each pair of outer digits in |df ⟨ n ⟩ dr|, the index type has local constructors for the positions in |df| and |dr|, and two recursive constructors selecting the two halves of a position in |n|.
The recursive constructors record the contributions at both ends, extending the numerical reading of the one-sided indices.
\begin{spec}
  Idx : SBinary → Set {-"~~."-}
\end{spec}
\todo{Give the constructors of Idx}

Lookup follows the index as before, but can now stop at either outer digit.
\begin{code}
  lookup : ∀ {A n} → List A n → Idx n → A {-"~~."-}
\end{code}
\todo{some cases of lookup?}

The same index can be read numerically from both ends.
For example, in |D1 ⟨ n ⟩ D1|, the constructor $\langle\!\langle 1_1\,i\,2_1\rangle\!\rangle$ selects the first half of the middle position |i|.
If |i| has |k| positions before it and |l| after it, the resulting index has |1 + 2 * k| positions before it and |2 + 2 * l| after it.
The front count includes the one element in the front digit; the rear count includes both the other half of the selected pair and the one element in the rear digit.
The index operations now come in left and right variants:
\begin{code}
  izeroL : ∀ {n} →         Idx (incL n)
  izeroR : ∀ {n} →         Idx (incR n)
  isuccL : ∀ {n} → Idx n → Idx (incL n)
  isuccR : ∀ {n} → Idx n → Idx (incR n) {-"~~."-}
\end{code}
Writing |before i| and |after i| for the numbers of positions before and after |i|, we can describe each operation from the corresponding end.
As before, |toF| reads an index as a position from the front, so its numerical value is |before i|; together, the two counts satisfy |before i + 1 + after i = toN n| for |i : Idx n|.
The zero indices point at the newly inserted elements, while the successors locate the old elements after insertion:
\begin{spec}
  before izeroL       ≡ 0
  after izeroR        ≡ 0
  before (isuccL i)   ≡ suc (before i)
  after (isuccR i)    ≡ suc (after i) {-"~~."-}
\end{spec}
Thus |isuccR| increases the distance from the rear while leaving the distance from the front unchanged: appending an element adds one position after every old element.
Symmetrically, |isuccL| increases the distance from the front while leaving the distance from the rear unchanged.

The definitions follow the carries in |incL| and |incR|, and satisfy the familiar lookup laws at both ends:
\begin{spec}
  lookup-izeroL : ∀ {A n} (x : A) (xs : List A n)
                → lookup (cons x xs) izeroL ≡ x
  lookup-isuccL : ∀ {A n} (x : A) (xs : List A n) (i : Idx n)
                → lookup (cons x xs) (isuccL i) ≡ lookup xs i
  lookup-izeroR : ∀ {A n} (xs : List A n) (x : A)
                → lookup (snoc xs x) izeroR ≡ x
  lookup-isuccR : ∀ {A n} (xs : List A n) (x : A) (i : Idx n)
                → lookup (snoc xs x) (isuccR i) ≡ lookup xs i {-"~~."-}
\end{spec}

Deletion gives two variants of |ishift|:
\begin{code}
  ishiftL : ∀ {n} → Idx (decL n) → Idx n
  ishiftR : ∀ {n} → Idx (decR n) → Idx n {-"~~."-}
\end{code}
These map a position in |tail xs| or |init xs| back to its position in |xs|.
The first increases |before| by one, and the second increases |after| by one.
As in Section~\ref{sec:redundant-index}, each is a successor followed by reindexing.
For non-empty |n|, both |incL (decL n)| and |incR (decR n)| have the same value as |n|, although their representations may differ.
Reindexing preserves the position and hence both distances, giving the specifications:
\begin{spec}
  lookup-tail : ∀ {A n} (xs : List A n) (i : Idx (decL n))
               → lookup (tail xs) i ≡ lookup xs (ishiftL i)
  lookup-init : ∀ {A n} (xs : List A n) (i : Idx (decR n))
               → lookup (init xs) i ≡ lookup xs (ishiftR i) {-"~~."-}
\end{spec}
Finally, |head| selects the position with no elements before it, and |last| the position with no elements after it.

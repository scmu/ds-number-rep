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
The last two clauses are the carry: a position that has run off the end of a |D2| digit forces a successor one digit up, exactly as |inc| carries, and the new low bit says which half of the doubled tail the position occupies.
Reading with |toF| turns this into successor on |Fin|,
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

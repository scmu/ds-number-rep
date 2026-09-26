\section{Indexing}
\label{sec:indexing}
\todo{Temporarily moving all indexing related stuffs to here.}

\todo{FingerTree indexing}


\subsection{Index types}

The index type |Idx| extends the zeroless version with constructors for the |D3| digit: three base indices and two recursive branches.
The successor operation on indices, |isucc|, maps |Idx n| to |Idx (inc n)| and satisfies:
\begin{code}
  isucc-correct : ∀ {n} (i : Idx n) → toF (isucc i) ≡ is (toF i) {-"~~."-}
\end{code}

A new operation |ishift : Idx (dec n) → Idx n| maps an index for the decremented number back into the original, enabling the verification of:
\begin{code}
  lookup-tail : ∀ {A n} (xs : RAL A n) (i : Idx (dec n))
                  → lookup (tail xs) i ≡ lookup xs (ishift i) {-"~~."-}
\end{code}
The key interface lemmas |lookup-izero|, |lookup-isucc|, and |lookup-tail| are all verified, ensuring that the RAL behaves as a correct flexible array.

\paragraph{Summary}
With the redundant binary representation we induced a list that offers $O(1)$ |head|,
worst-case $O(\log n)$ and amortised $O(1)$ |cons| and |tail|,
$O(\log n)$ |lookup|, and amortised $O(n)$ |append|.
Asymptote-wise, it appears to be a good improvement over the simple built-in list implemented as left-biased linked-lists,
provided that you only add to and remove from one end of the list, and perform indexing more than |append|.
What if we want a faster append?

\subsection{Indices as binary numbers}
\label{sec:binary-index}

Just as |Fin n| --- the type of naturals below |n|, with |iz : Fin (inc n)| and |is : Fin n → Fin (inc n)| mirroring |zero| and |suc| --- indexes a length-|n| vector, |Idx n| will index a |RAL A n|.
Our claim is that |Idx| is itself a number system: where |Fin| gives a \emph{unary} account of the naturals below a bound, |Idx| gives a \emph{binary} one, laid out along digits of |n|.
We make the correspondence exact with a pair of conversions between |Idx n| and |Fin (toN n)|.

Consider first the zeroless representation.
An index selects a position within one digit and, if the element it seeks lives further in, descends into the doubled tail.
A |D1| digit stores one element and has two subtrees, giving one base position |ez1| and two recursive branches |_cA1|, |_cB1|; a |D2| digit stores two elements, giving base positions |ez2|, |eo2| and branches |_cA2|, |_cB2|:
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
The function |lookup| follows an index through the list in lockstep, projecting from the paired-up elements as it recurses:
\begin{code}
  lookup : ∀ {A n} → RAL A n → Idx n → A
  lookup (one x    ∷ xs)  ez1      = x
  lookup (one x    ∷ xs)  (i cA1)  = proj₁ (lookup xs i)
  lookup (one x    ∷ xs)  (i cB1)  = proj₂ (lookup xs i)
  lookup (two x y  ∷ xs)  ez2      = x
  lookup (two x y  ∷ xs)  eo2      = y
  lookup (two x y  ∷ xs)  (i cA2)  = proj₁ (lookup xs i)
  lookup (two x y  ∷ xs)  (i cB2)  = proj₂ (lookup xs i) {-"~~."-}
\end{code}

To pin down that |Idx n| enumerates the naturals below |toN n|, we convert to |Fin (toN n)|.
Following \citet{HinzeSwierstra:22:Calculating}, reading an index outward as a binary numeral yields |toF : Idx n → Fin (toN n)|, doubling the tail contribution at each digit with |_dblO| and |_dblI|.

The inverse direction is more interesting.
Given a position in |Fin (toN n)|, we peel off the current digit by halving with |_halfF|, which splits a doubled range into a tail position and a remainder:
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
Each |with| clause is one digit of binary long division: |_halfF| tells us whether the position falls on the left or right subtree, or on one of the elements stored locally, and |fromF| recurses on the quotient.
Together with |toF|, this exhibits |Idx n| as just another notation for |Fin (toN n)| --- a binary numeral for the same finite range that |Fin| writes in unary.

Because |Idx| is a number system, it carries its own arithmetic.
The zero index |izero| points at the element |cons| has just placed at the front, and |isucc| is the successor on positions:
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
The last two clauses are the carry: incrementing a position that has run off the end of a |D2| digit forces a successor \emph{one digit up}, exactly as |inc| carries.
These connect to the container through the specification of a one-sided flexible array \citep{HinzeSwierstra:22:Calculating}:
\begin{spec}
  lookup-izero  : ∀ {A n} (x : A) (xs : RAL A n)
                → lookup (cons x xs) izero ≡ x
  lookup-isucc  : ∀ {A n} (x : A) (xs : RAL A n) (i : Idx n)
                → lookup (cons x xs) (isucc i) ≡ lookup xs i
  lookup-head   : ∀ {A n} (xs : RAL A (inc n))
                → head xs ≡ lookup xs izero
  lookup-tail   : ∀ {A n} (xs : RAL A (inc n)) (i : Idx n)
                → lookup (tail xs) i ≡ lookup xs (isucc i) {-"~~."-}
\end{spec}
With the zeroless |tail : RAL A (inc n) → RAL A n|, dropping the head is mirrored on indices by |isucc|.

Moving to the redundant representation of Section~\ref{sec:redundant-binary} changes nothing structural.
We added a digit to the number, so we add constructors to the index; the recipe is unchanged.
A |D3| digit stores three elements and keeps its two subtrees, contributing three base positions |ez3|, |eo3|, |et3| and two branches |_cA3|, |_cB3|:
\begin{code}
    ez3   : ∀ {n} →          Idx (D3 ∷ n)
    eo3   : ∀ {n} →          Idx (D3 ∷ n)
    et3   : ∀ {n} →          Idx (D3 ∷ n)
    _cA3  : ∀ {n} → Idx n →  Idx (D3 ∷ n)
    _cB3  : ∀ {n} → Idx n →  Idx (D3 ∷ n) {-"~~."-}
\end{code}
The clauses of |fromF| and |isucc| for |D3| are filled in by the same pattern; the carry in |isucc| again threads through |izero| on the tail, just as it did for |D2|:
\begin{spec}
  isucc eo3      = izero cA2
  isucc et3      = izero cB2
  isucc (i cA3)  = (isucc i) cA2
  isucc (i cB3)  = (isucc i) cB2 {-"~~."-}
\end{spec}

In Section~\ref{sec:redundant-binary} the redundant |tail| takes a |RAL A n| to a |RAL A (dec n)|, so an index for the shortened list lives in |Idx (dec n)|.
To state how |lookup| behaves under |tail| we must send such an index back into the original number, which is the role of |ishift|:
\begin{spec}
  ishift : ∀ {n} → Idx (dec n) → Idx n
  ishift {D2 ∷ n}  ez1      = eo2
  ishift {D2 ∷ n}  (i cA1)  = i cA2
  ishift {D2 ∷ n}  (i cB1)  = i cB2 {-"~~."-}
\end{spec}
On a digit that has spare room, |ishift| merely relabels a position one digit up.
The interesting clauses are those where |dec| borrowed from the tail (the case |D1 ∷ d ∷ n|): there |ishift| reaches inside with |izero| on the now-nonempty tail, the mirror image of the borrow.
With |ishift| in hand the tail law now phrased with |dec| rather than |inc|:
\begin{spec}
  lookup-tail : ∀ {A n} (xs : RAL A n) (i : Idx (dec n))
              → lookup (tail xs) i ≡ lookup xs (ishift i) {-"~~."-}
\end{spec}

The move that took us from unary lists to binary numbers for \emph{sizes} thus also yields binary numbers for \emph{positions}: |Idx| is the ornament of |Binary| in the index direction, just as |RAL| is its ornament in the data direction, both cut to the same digits.

\section{Zeroless binary numbers}

It appears that the presence of zero's is the main culprit in the naive binary representation.
What if we eliminate |D0| and use other digits instead?

\subsection{The Leibniz numeral}

We adopt a number representation that is still |2|-based, but the digits are $\{1, 2\}$ rather than $\{0, 1\}$,
which \citet{HinzeSwierstra:22:Calculating} termed \emph{Leibniz numerals}:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data Digit : Set where
    D1  : Digit
    D2  : Digit {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data ZBinary : Set where
    B0   : ZBinary
    _∷_  : Digit → ZBinary → ZBinary {-"~~."-}
\end{code}
\end{minipage}\\
The semantic function assigns still weight $2^k$ to the digit at position~$k$:
\begin{code}
  toN : ZBinary → ℕ
  toN B0       = 0
  toN (d ∷ n)  = DtoN d + 2 * toN n {-"~~,"-}
\end{code}
where |DtoN D1 = 1| and |DtoN D2 = 2|.
For example, |D1 ∷ D2 ∷ D1 ∷ []| denotes
$1 \times 2^0 +$ $2 \times$ $2^1 +$ $1 \times 2^2 = 1 + 4 + 4 = 9$.
Since every digit is at least~$1$, any representation other than |B0| necessarily denotes a positive number.

Increment flips a |D1| to |D2| without carry, and wraps a |D2| to |D1| while carrying to the next position:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  inc : ZBinary → ZBinary
  inc B0        = D1 ∷ B0
  inc (D1 ∷ n)  = D2 ∷ n
  inc (D2 ∷ n)  = D1 ∷ inc n {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  dec : ZBinary → ZBinary
  dec B0        = B0
  dec (D1 ∷ B0) = B0
  dec (D1 ∷ n)  = D2 ∷ dec n
  dec (D2 ∷ n)  = D1 ∷ n {-"~~."-}
\end{code}
\end{minipage}\\
The worst case running time of |inc| is still $O(\log n)$ when a chain of |D2| digits forces successive carries.
\todo{But is it $O(1)$ amortised?}
Decrement is dual to increment, borrowing from the next position when a |D1| is encountered.
Correctness of both operations is verified, along with the property |dec-inc≡id : ∀ n → dec (inc n) ≡ n|, showing that decrement is a left inverse of increment at the representation level.


\todo{rewrite this} The central advantage of the zeroless system is that every natural number has a \emph{unique} representation.
\todo{Why is this an advantage?}
We formalise this as injectivity of~|toN|:
\begin{code}
  nonRedundant : ∀ x y → toN x ≡ toN y → x ≡ y {-"~~."-}
\end{code}

Together with |toN-fromN|, injectivity yields a full bijection:
\begin{code}
  fromN-toN : ∀ n → fromN (toN n) ≡ n {-"~~."-}
\end{code}
This is strictly stronger than what standard binary affords, where leading zeros prevent the round-trip from holding.

\subsection{Random-Access Lists}

As before, each digit is ornamented with data.
The digit |D1| carries one element; |D2| carries two:
\begin{code}
  data Some (A : Set) : Digit → Set where
    one  : A → Some A D1
    two  : A → A → Some A D2 {-"~~."-}
\end{code}
The definition of |RAL| remains the same and is omitted.
The |cons| operation mirrors |inc|: adding to a |D1| position produces a |D2|, while adding to a |D2| position wraps back to |D1| and carries a pair upward:
\begin{code}
  cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
  cons x nil              = one x    ∷ nil
  cons x (one y    ∷ xs)  = two x y  ∷ xs
  cons x (two y z  ∷ xs)  = one x    ∷ cons (y , z) xs {-"~~."-}
\end{code}
Since |inc| recurses only upon encountering |D2|, the operation is $O(1)$ amortised.
The |head| and |tail| functions can be typed to accept |RAL A (inc n)|, leveraging the Peano view to ensure the list is non-empty:
\begin{code}
  head : ∀ {A n} → RAL A (inc n) → A {-"~~,"-}
  tail : ∀ {A n} → RAL A (inc n) → RAL A n {-"~~."-}
\end{code}

\subsection{Index Types and Interface Laws}

The index type |Idx| mirrors the digit decomposition.
For a |D1| digit there is one base index (the element stored at that position) and two recursive branches (left and right children in the implicit tree); for |D2|, there are two base indices and two recursive branches.
We establish that |Idx| is isomorphic to |Fin ∘ toN| via mutually inverse maps |toF| and |fromF|, verified by:
\begin{code}
  toF-fromF : ∀ {n} (i : Fin (toN n)) → toF (fromF i) ≡ i {-"~~."-}
\end{code}

The index operations |izero| and |isucc| mirror the natural-number constructors at the index level.
Their correctness is expressed by:
\begin{code}
  izero-correct : ∀ {n} → toF (izero {n}) ≡ iz
  isucc-correct : ∀ {n} (i : Idx n) → toF (isucc i) ≡ is (toF i) {-"~~."-}
\end{code}
These enable verification of the full interface specification for one-sided flexible arrays \cite{HinzeSwierstra:22:Calculating}:
\begin{code}
  lookup-izero  : ∀ {A n} (x : A) (xs : RAL A n)
                    → lookup (cons x xs) izero ≡ x
  lookup-isucc  : ∀ {A n} (x : A) (xs : RAL A n) (i : Idx n)
                    → lookup (cons x xs) (isucc i) ≡ lookup xs i
  lookup-head   : ∀ {A n} (xs : RAL A (inc n))
                    → head xs ≡ lookup xs izero
  lookup-tail   : ∀ {A n} (xs : RAL A (inc n)) (i : Idx n)
                    → lookup (tail xs) i ≡ lookup xs (isucc i) {-"~~."-}
\end{code}
\todo{expand the arithmetic operations on Idx}

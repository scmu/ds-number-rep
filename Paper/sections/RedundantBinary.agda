
\section{Redundancy for amortised efficiency}

The zeroless binary system of the previous section provides unique representations and a clean interface.
When only |inc| is used, the amortised cost per operation is $O(1)$.
However, when |inc| and |dec| are \emph{interleaved}, it can force repeated carry and borrow chains that degrade the amortised bound.
In this section we explore how \emph{adding redundancy} to the digit set restores good amortised performance under arbitrary sequences of increments and decrements, at the expense of uniqueness of representation.

\subsection{Redundant binary numbers}

We extend the digit set to $\{1, 2, 3\}$:
\begin{code}
  data Digit : Set where
    D1  : Digit
    D2  : Digit
    D3  : Digit {-"~~,"-}
  data RBinary : Set where
    B0   : RBinary
    _∷_  : Digit → RBinary → RBinary {-"~~."-}
\end{code}
The semantic function retains its uniform shape:
\begin{code}
  toN : RBinary → ℕ
  toN B0       = 0
  toN (d ∷ n)  = DtoN d + 2 * toN n {-"~~."-}
\end{code}
Increment absorbs a carry locally whenever the digit is below its maximum:
\begin{code}
  inc : RBinary → RBinary
  inc B0        = D1 ∷ B0
  inc (D1 ∷ n)  = D2 ∷ n
  inc (D2 ∷ n)  = D3 ∷ n
  inc (D3 ∷ n)  = D2 ∷ inc n {-"~~."-}
\end{code}
A carry propagates only when the digit is already |D3|, and the digit then resets to |D2| rather than |D1|.
The worst-case cost of a single |inc| remains $O(\log n)$, since a chain of |D3| digits forces successive carries just as a chain of |D2| digits does in the zeroless system.
The crucial difference emerges under mixed sequences of |inc| and |dec|: after a carry resets a |D3| to |D2|, a subsequent |dec| at that position merely decreases |D2| to |D1| without triggering a borrow.
Symmetrically, after a borrow resets a |D1| to |D2|, a subsequent |inc| increases |D2| to |D3| without carrying.
The extra room in the digit range $\{1, 2, 3\}$ thus acts as a buffer that prevents carries and borrows from cascading in alternation, ensuring that the amortised cost per operation remains $O(1)$ even when |inc| and |dec| are interleaved arbitrarily.
\todo{simplify the explanation done by Chris Okasaki}

Decrement is defined symmetrically, borrowing when the digit is |D1|:
\begin{code}
  dec : RBinary → RBinary
  dec B0            = B0
  dec (D1 ∷ B0)     = B0
  dec (D1 ∷ d ∷ n)  = D2 ∷ dec (d ∷ n)
  dec (D2 ∷ n)      = D1 ∷ n
  dec (D3 ∷ n)      = D2 ∷ n {-"~~."-}
\end{code}
Correctness of both operations is verified:
\begin{code}
  inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
  dec-correct : ∀ n → toN (dec n) ≡ pred (toN n) {-"~~."-}
\end{code}

\subsection{Consequences of redundancy}

The enlarged digit set introduces three complications absent from the zeroless system.

\paragraph{Non-unique representation.}
Multiple representations can denote the same value.
For example, both |D3 ∷ B0| and |D1 ∷ D1 ∷ B0| represent the number~$3$:
\begin{code}
  redundant : ∃ (λ x → ∃ (λ y → (x ≢ y) × (toN x ≡ toN y))) {-"~~."-}
\end{code}

\paragraph{Decrement does not invert increment.}
Since multiple representations coexist, |dec (inc n)| need not return |n| itself:
\begin{code}
  dec-inc≢id : ∃ (λ n → n ≢ dec (inc n)) {-"~~."-}
\end{code}
For instance, |inc| maps |D3 ∷ B0| to |D2 ∷ D1 ∷ B0|, and |dec| then yields |D1 ∷ D1 ∷ B0|, a different representation of the same number~$3$.

\paragraph{Gaps in the image of increment.}
Not every non-zero |RBinary| is of the form |inc y| for some~|y|:
\begin{code}
  inc-gap : ∃ (λ x → (toN x ≢ 0) × (∀ y → x ≢ inc y)) {-"~~."-}
\end{code}
The witness is |D1 ∷ D1 ∷ B0|: no |y| satisfies |inc y ≡ D1 ∷ D1 ∷ B0|, because |inc| always produces an initial |D1| only at the base case |B0|, never as a result of carrying.
This directly affects the type of |head|: the signature |head : RAL A (inc n) → A| used in the zeroless system cannot accept all non-empty RALs.
We must instead require an explicit non-emptiness proof:
\begin{code}
  head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A {-"~~."-}
\end{code}

\subsection{Random-access lists}

Each digit carries a number of elements equal to its value:
\begin{code}
  data Some (A : Set) : Digit → Set where
    one    : A → Some A D1
    two    : A → A → Some A D2
    three  : A → A → A → Some A D3 {-"~~."-}
\end{code}
The |cons| operation mirrors |inc|.
When the least-significant digit is |D3|, two of the three stored elements are paired and carried to the next level:
\begin{code}
  cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
  cons x nil                  = one x        ∷ nil
  cons x (one y        ∷ xs)  = two x y      ∷ xs
  cons x (two y z      ∷ xs)  = three x y z  ∷ xs
  cons x (three y z w  ∷ xs)  = two x y      ∷ cons (z , w) xs {-"~~."-}
\end{code}
The worst-case cost of |cons| mirrors that of |inc| and is $O(\log n)$.
However, when |cons| and |tail| are interleaved, the redundant digit range prevents cascading carries and borrows, yielding $O(1)$ amortised cost per operation --- a strict improvement over the zeroless system under mixed workloads.

The |tail| operation is defined via |dec|.
When the leading digit is |D1| and the remaining number is non-empty, |tail| borrows from the next level, splitting a pair and increasing the local digit to |D2|.

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

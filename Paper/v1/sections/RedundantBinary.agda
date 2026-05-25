
\section{Redundancy for amortised efficiency}
\label{sec:redundant-binary}

Surprisingly, amortised $O(1)$ performance of mixed |cons| and |tail| can be achieved by \emph{adding another digit}, thereby allowing redundancy, in our numerical representation.

\subsection{Redundant binary numbers}

In the \emph{redundant binary} representation, the set of digits is extended to $\{1, 2, 3\}$:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data Digit : Set where
    D1  : Digit
    D2  : Digit
    D3  : Digit {-"~~,"-}
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data RBinary : Set where
    B0   : RBinary
    _∷_  : Digit → RBinary → RBinary {-"~~."-}
\end{code}
\end{minipage}\\
The semantic function stays the same, while |⟦_⟧| is extended with |⟦ D3 ⟧ = 3|:
\begin{code}
  toN : RBinary → ℕ
  toN B0       = 0
  toN (d ∷ n)  = ⟦ d ⟧ + 2 * toN n {-"~~."-}
\end{code}
A consequence is that representation of a number is no longer unique.
For example, both |D3 ∷ D1 ∷ []| and |D1 ∷ D2 ∷ []| denote |5|.
We will soon see that such redundancy turns out to be beneficial efficiency-wise.

In |inc|, a carry propagates to the tail in the case for |D3 ∷ n|, in which the least-significant digit |D3| resets to |D2|.
In |dec|, we borrow a one from the tail in the case for |D1 ∷ n|:
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  inc : RBinary → RBinary
  inc B0        = D1 ∷ B0
  inc (D1 ∷ n)  = D2 ∷ n
  inc (D2 ∷ n)  = D3 ∷ n
  inc (D3 ∷ n)  = D2 ∷ inc n {-"~~."-}
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  dec : RBinary → RBinary
  dec B0            = B0
  dec (D1 ∷ B0)     = B0
  dec (D1 ∷ n)      = D2 ∷ dec n
  dec (D2 ∷ n)      = D1 ∷ n
  dec (D3 ∷ n)      = D2 ∷ n {-"~~."-}
\end{code}
\end{minipage}\\
It is important that |inc| and |dec| recurse on different cases.
The worst-case cost of a single |inc| or |dec| remains $O(\log n)$, while the amortised cost for consecutive calls to |inc| and |dec| are $O(1)$.
The crucial difference emerges under mixed sequences of |inc| and |dec|: after a carry resets a |D3| to |D2|, a subsequent |dec| at that position merely decreases |D2| to |D1| without triggering a borrow.
Symmetrically, after a borrow resets a |D1| to |D2|, a subsequent |inc| increases |D2| to |D3| without carrying.
The extra room in the digit range $\{1, 2, 3\}$ thus acts as a buffer that prevents carries and borrows from cascading in alternation, ensuring that the amortised cost per operation remains $O(1)$ even when |inc| and |dec| are interleaved arbitrarily.
\todo{simplify the explanation done by Chris Okasaki}

Correctness of both operations is verified:
\begin{code}
  inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
  dec-correct : ∀ n → toN (dec n) ≡ pred (toN n) {-"~~."-}
\end{code}

With the discussion above, it is apparent that |dec| is no longer a left inverse of |inc| --- which is the whole point.
Another consequence is that not every non-zero |RBinary| is the result of |inc y| for some~|y|.
For example, there exists no |y| such that |inc y = D1 ∷ D1 ∷ B0|,
because |inc B0| is the only case where |inc| returns a number starting with |D1|.
This means that we cannot give |head| the type |RAL A (inc n) → A| if we want it to work on all non-empty lists, similarly with |tail|.

% \paragraph{Non-unique representation.}
% Multiple representations can denote the same value.
% For example, both |D3 ∷ B0| and |D1 ∷ D1 ∷ B0| represent the number~$3$:
% \begin{code}
%   redundant : ∃ (λ x → ∃ (λ y → (x ≢ y) × (toN x ≡ toN y))) {-"~~."-}
% \end{code}
%
% \paragraph{Decrement does not invert increment.}
% Since multiple representations coexist, |dec (inc n)| need not return |n| itself:
% \begin{code}
%   dec-inc≢id : ∃ (λ n → n ≢ dec (inc n)) {-"~~."-}
% \end{code}
% For instance, |inc| maps |D3 ∷ B0| to |D2 ∷ D1 ∷ B0|, and |dec| then yields |D1 ∷ D1 ∷ B0|, a different representation of the same number~$3$.

% \paragraph{Gaps in the image of increment.}
% Not every non-zero |RBinary| is of the form |inc y| for some~|y|:
% \begin{code}
%   inc-gap : ∃ (λ x → (toN x ≢ 0) × (∀ y → x ≢ inc y)) {-"~~."-}
% \end{code}
% The witness is |D1 ∷ D1 ∷ B0|: no |y| satisfies |inc y ≡ D1 ∷ D1 ∷ B0|, because |inc| always produces an initial |D1| only at the base case |B0|, never as a result of carrying.
% This directly affects the type of |head|: the signature |head : RAL A (inc n) → A| used in the zeroless system cannot accept all non-empty RALs.
% We must instead require an explicit non-emptiness proof:
% \begin{code}
%   head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A {-"~~."-}
% \end{code}

\subsection{Random-access lists}

Consider the random-access list induced by |Rbinary|.
The |Some| type is extended with a case |three| that stores three elements:
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
As discussed in the previous section, we cannot let |tail| have type |RAL A (inc n) → RAL A n| if we want it to accept all non-empty lists.
Instead we give it the type |RAL A n → RAL A (dec n)|, which makes its definition a direct translation of |dec|:
%format ∷-nonzero = "::\!\mbox{-}\Varid{nonzero}"
\begin{code}
tail : ∀ {A n} → RAL A n → RAL A (dec n)
tail nil                   =  nil
tail (one x ∷ nil)         =  nil
tail (one x ∷ xs@(_ ∷ _))  =  let  (y , z) = head xs (∷-nonzero xs)
                              in   two y z ∷ tail xs
tail (two x y ∷ xs)        =  one y ∷ xs
tail (three x y z ∷ xs)    =  two y z ∷ xs {-"~~."-}
\end{code}
It makes a call to |head|, which now takes a proof promising that the given list is not empty:
\begin{code}
head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A
head nil                  nz = contradiction refl nz
head (one x        ∷ xs)  nz = x
head (two x y      ∷ xs)  nz = x
head (three x y z  ∷ xs)  nz = x {-"~~."-}
\end{code}
When |cons| and |tail| are interleaved, the redundant digit range prevents cascading carries and borrows, yielding $O(1)$ amortised cost per operation --- a strict improvement over the zeroless system under mixed workloads.

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

In summary, with the redundant binary representation we induced a list that offers $O(1)$ |head|,
worst-case $O(\log n)$ and amortised $O(1)$ |cons| and |tail|,
$O(\log n)$ |lookup|, and amortised $O(n)$ |append|.
Asymptote-wise, it appears to be a good improvement over the simple built-in list implemented as left-biased linked-lists,
provided that you only add to and remove from one end of the list, and perform |lookup| more than |append|.
What, then, if we wish to add to and remove from both ends, or we want a faster append?

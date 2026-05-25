\section{Binary numbers for logarithmic-time efficiency}

A standard trick to achieve logarithmic-time operations is to switch to a binary representation.
Let us see how well it works.

\subsection{Naive binary numbers}

We start with a naive binary representation, where
the type |RAL| is still a sequence of digits, but now |Digit| could be zero or one:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data Digit : Set where
    D0  : Digit
    D1  : Digit {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data Binary : Set where
    B0   : Binary
    _∷_  : Digit → Binary → Binary {-"~~."-}
\end{code}
\end{minipage}\\
To make the connection with lists clear, in this article we present binary numbers least-significant first.
For example, |D1 ∷ D0 ∷ D1 ∷ D1 ∷ B0| denotes $1 \times 2^0 + 0 \times 2^1 + 1 \times 2^2 + 1 \times 2^3 =$ $1 + 4 + 8 = 13$.
The semantic function is:
\begin{code}
  toN : Binary → ℕ
  toN B0       = 0
  toN (d ∷ b)  = ⟦ d ⟧ + 2 * toN b {-"~~,"-}
\end{code}
where |_*_| denotes multiplication of |ℕ|.
One may already have noticed a potential problem: both |D1 ∷ D1 ∷ B0| and |D1 ∷ D1 ∷ D0 ∷ B0| denote $4$.
We will ensure that our operations maintain the invariant that there are no trailing zeros: the rightmost (most significant) digit of a constructed |Binary|, if any, is always |D1|.
This invariant could have been enforced by some clever design in the datatype, but we will keep it simple for now, before moving on to another representation.

Increment and decrement are defined as below.
The function |inc| propagates a carry when the least-significant digit is |D1|.
In |dec|, the pattern |D1 ∷ B0| is made a special case, without which |dec (D1 ∷ B0)| would yield |D0 ∷ B0|, which breaks the no-trailing-zero invariant.\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
inc : Binary → Binary
inc B0        = D1 ∷ B0
inc (D0 ∷ b)  = D1 ∷ b
inc (D1 ∷ b)  = D0 ∷ inc b {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
dec : Binary → Binary
dec B0         = B0
dec (D0 ∷ b)   = D1 ∷ dec b
dec (D1 ∷ B0)  = B0
dec (D1 ∷ b)   = D0 ∷ b  {-"~~."-}
\end{code}
\end{minipage}\\
The worst-case cost for incrementing a number is $O(\log n)$, since a carry may propagate through every digit.
A good news is that the amortised cost of repeated application of |inc| is $O(1)$.
\todo{reason?}
Similarly, |dec| has worst-case cost $O(\log n)$, while repeated |dec| has amortised cost $O(1)$.

However, mixed sequences of |inc| and |dec| are no longer amortised $O(1)$.
To see why \todo{explanation or example}.

\todo{efficiency of decrement; non-constant amortised efficiency of mixed |inc| and |dec|.}

Correctness of |inc| and |dec| is verified by induction, with the carry case appealing to the correctness of doubling:
\begin{code}
  inc-correct : ∀ b → toN (inc b) ≡ suc (toN b) {-"~~."-}
\end{code}
We also verify |toN-fromN : ∀ n → toN (fromN n) ≡ n|, establishing that |toN| is a left inverse of |fromN|.

% \paragraph{The redundancy problem.}
% Standard binary numbers admit \emph{leading zeros}: |B0|, |D0 ∷ B0|, |D0 ∷ D0 ∷ B0|, \ldots\ all denote zero.
% More generally, distinct representations can map to the same natural number:
% \begin{code}
%   redundant : ∃ (λ x → ∃ (λ y → (x ≢ y) × (toN x ≡ toN y))) {-"~~,"-}
% \end{code}
% witnessed by |B0| and |D0 ∷ B0|.
% As a consequence, the converse direction |fromN-toN : ∀ b → fromN (toN b) ≡ b| does \emph{not} hold: the round-trip through |ℕ| normalises away leading zeros.
% \todo{Redundacy itself shouldn't be a problem... we will introduce redundancy later! Why do we not like |B0|s in this stage?}

\subsection{Random-access lists from naive binary numbers}

Now we consider random-access lists induced by binary numbers.
The type |Some| now has two cases: when indexed by |D0| it carries nothing, and when indexed by |D1| it carries one element:
\begin{code}
  data Some (A : Set) : Digit → Set where
    zero  :          Some A D0
    one   : A →      Some A D1 {-"~~."-}
\end{code}
The type |RAL A n| contains |toN n| elements.
To achieve that, at each successive position the element type \emph{doubles} to |A × A|, corresponding to the multiplication by |2| in |toN|:
\begin{code}
  data RAL (A : Set) : Binary → Set where
    nil   : RAL A B0
    _∷_  : ∀ {d b} → Some A d → RAL (A × A) b → RAL A (d ∷ b) {-"~~."-}
\end{code}
Each position of |RAL A n| may contain some data (|one _|) or not (|zero|).
Data in the left most position, if any, has type |A|;
that in the next position has type |A × A|, followed by |(A × A) × (A × A)|, etc.
They are essentially leaf-valued complete binary trees of increasing depth.

The definition of |cons| mirrors that of |inc|.
In fact, when coding up |cons| in Agda, guided by |inc| in its type, the programmer is often left with only one reasonable way fill in each of the right hand side.
\begin{code}
  cons : ∀ {A b} → A → RAL A b → RAL A (inc b)
  cons x nil           = one x  ∷ nil
  cons x (zero ∷ xs)   = one x  ∷ xs
  cons x (one y ∷ xs)  = zero   ∷ cons (x , y) xs {-"~~."-}
\end{code}
Note that in the last case where the least-significant digit is |D1|, the new element is paired with the existing one and carried to the next level.
Like |inc|, the worse-case running time of |cons| is $O(\log n)$, while the amortised complexity of repeated |cons| is  $O(1)$.

The situation with |tail| is a bit tricky.
One may assign it the type |RAL A (inc n) → RAL A n|, which ensures that it is only applied to non-empty lists,
or |RAL A n → RAL A (dec n)|. For this section we go with the former.
The shape of the function |tail| below does not strictly mirror that of |inc| (rather, it looks like the inverse of |inc|), but its development is still guided by |inc|:
\begin{code}
tail : ∀ {A b} → RAL A (inc b) → RAL A b
tail {_} {B0}      xs             = nil
tail {_} {D0 ∷ b}  (one x  ∷ xs)  = zero ∷ xs
tail {_} {D1 ∷ b}  (zero   ∷ xs)  = one (proj₂ (head xs)) ∷ tail xs {-"~~."-}
\end{code}
In the |zero  ∷ xs| case we need to return a list having the form |one _ ∷ tail xs|, which corresponds to borrowing a |D1| when decrementing a binary number.
But what value shall we fill in the |one _|?
For that we need to make a call to |head|, and since the head of |xs| has type |A × A|, we apply |proj₂| to drop the first element of |head xs| and keep the second.
Now consider how one implements |head|:
\begin{code}
head : ∀ {A b} → RAL A (inc b) → A
head {_} {B0}      (one x  ∷ xs) = x
head {_} {D0 ∷ b}  (one x  ∷ xs) = x
head {_} {D1 ∷ b}  (zero   ∷ xs) = proj₁ (head xs) {-"~~."-}
\end{code}
We have immediate access to the head of a list if it starts with |one|.
If the least-significant bit is |zero|, we have to recurse until we meet a |one|.
Therefore the time complexity of |head| is now $O(\log n)$.

Like the situation of |inc| and |dec|, |cons| and |tail| are no longer amortised $O(1)$ when they are interleaved.

%\begin{minipage}[t]{0.45\textwidth}
% \begin{code}
% head' : ∀ {A b} → RAL A b → (toN b ≢ 0) → A
% head' nil           p = ⊥-elim (p refl)
% head' (zero ∷ xs)   p = proj₁ (head' xs (2*n≢0⇒n≢0 p))
% head' (one x ∷ xs)  p = x
% \end{code}
%\end{minipage}
%\begin{minipage}[t]{0.45\textwidth}
% \begin{code}
% tail : ∀ {A n} → RAL A n → RAL A (dec n)
% tail nil                 = nil
% tail (zero ∷ nil)  = nil
% tail (zero ∷ xs@(_ ∷ _)) =
%     let (x₁ , x₂) = head' xs (? xs)
%     in  one x₂ ∷ tail xs
% tail (one x ∷ xs) = zero ∷ xs
% \end{code}
%\end{minipage}


\todo{more on indexing}
The index type |Idx| for binary RALs branches on the digit: a |D0| digit contributes two recursive directions (left and right child of the implicit complete binary tree at that level), while a |D1| digit adds a base index for the element it stores plus two recursive branches.
Lookup runs in $O(\log n)$ time.

With the naive representation of binary numbers, we induced a data structure with $O(\log n)$ |lookup|,
but |head| is no longer constant-time, and |append| is still out of the question.

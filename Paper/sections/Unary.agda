\section{The starting point: unary number and list}

For the rest of the article, we will present a series of number systems and the data structures derived from them.
Following \citet{HinzeSwierstra:22:Calculating}, we adopt a uniform framework in which every number system is defined by a type for |Digit|s, based upon which a type for natural numbers, say |Nat|, is defined.
For each |Nat| we define its semantics by a function |toN : Nat -> ℕ|,
as well as operations such as increment, decrement, and addition on |Nat|, whose correctness is established by showing that they commute with~|toN|.
We then construct the data structure corresponding to |Nat| by \emph{indexing} a container type by |Nat|: each digit is ornamented with data, and structural operations on the container mirror arithmetic operations on the index.

For completeness we start with unary natural numbers, which is isomorphic to |ℕ|.
There is only a single digit, |D1|, denoting a "one".
A number is a sequence of such digits:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
data Digit : Set where
  D1 : Digit {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
data Unary : Set where
  N0    : Unary
  _∷_   : Digit → Unary → Unary {-"~~,"-}
\end{code}
\end{minipage}\\
whose semantics is given by counting the occurrences of |D1|s:
\begin{code}
toN : Unary → ℕ
toN N0       = 0
toN (d ∷ n)  = DtoN d + toN n {-"~~,"-}
\end{code}
where |DtoN D1 = 1|.
For example, |3| is represented by |D1 ∷ D1 ∷ D1 ∷ N0|.

%Since the only available digit is |D1|, we recover the standard Peano representation: the number $k$ is represented by $k$ copies of |D1| prepended to |N0|.

Increment and decrement are both $O(1)$:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  inc : Unary → Unary
  inc n = D1 ∷ n {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  dec : Unary → Unary
  dec N0        = N0
  dec (D1 ∷ n)  = n {-"~~."-}
\end{code}
\end{minipage}\\
Addition |m + n| of two |Unary|s, however, takes $O(m)$ time.
% Correctness of these operations follows immediately --- all proofs reduce to |refl|:
% \begin{code}
%   inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
%   inc-correct n = refl {-"~~."-}
% \end{code}
% Moreover, |toN| and |fromN| (defined by iterating |inc|) constitute a bijection between |Nat| and |ℕ|, verified in both directions:
% \begin{code}
%   toN-fromN  : ∀ n → toN (fromN n) ≡ n  {-"~~,"-}
%   fromN-toN  : ∀ n → fromN (toN n) ≡ n  {-"~~."-}
% \end{code}

% \subsection{Random-Access Lists from Unary Numbers} % SCM: joining the two sections together, for a quicker pace

Now consider the container datatype induced from |Unary|.
For each number system, we introduce two datatypes |Some A| and |RAL A|, respectively indexed by a |Digit| and an |Unary|.
Given |d : Digit|, |Some A d| contains |d| occurrences of |A|;
given |n : Unary|, |RAL A d| denotes a \emph{random-access list} having |n| elements.
For |Unary| defined above, the induced |Some| and |RAL| are shown below:%
\footnote{In this article we use bold font, e.g. |D1|, for constructors of |Digit| and |Unary|,
and blackboard bold font, e.g. |one|, for those of |Some| and |RAL|.}
\begin{code}
  data Some (A : Set) : Digit → Set where
    one : A → Some A D1 {-"~~,"-}

  data RAL (A : Set) : Unary → Set where
    nil  : RAL A N0
    _∷_  : ∀ {d n} → Some A d → RAL A n → RAL A (d ∷ n) {-"~~."-}
\end{code}
The type |Some| contains exactly one element, and |RAL| is isomorphic to |Vec|, the familiar type of length-indexed vectors.
For example,
\begin{spec}
 one 'a' ∷ one 'b' ∷ one 'c' ∷ nil {-"~~,"-}
\end{spec}
having type |RAL Char (D1 ∷ D1 ∷ D1 ∷ N0)|, is a vector having three elements.

The operations |cons| and |tail|, respectively corresponding to |inc| and |dec| on |Nat|, are $O(1)$.
The function |append|, corresponding to addition, takes time proportional to the size of its first argument.

The data structure is called a \emph{random access list} because it provides an operation |lookup| which, takes a list and a \emph{position}, returns the corresponding element.
For the RAL induced by |Unary|, the induced type of positions is
\todo{Give the details?}
To locate the item at position |p|, the function lookup has to traverse the list from the font until position |p|.
Therefore looking up a list is a linear time operation.
Can we do better?

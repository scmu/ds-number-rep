\section{Fractional digits}

What if we allow mixed fractions in digits?

In decimal representation, the digits are integers in $\{0..9\}$, and $987$, for example, denotes $9 \times 10^2 + 8 \times 10 + 7$.
In a decimal number $d_2 d_1 d_0$, the value contained by the $d_2 d_1$ part is always a multiple of $10$,
just like in |d ⟨ b ⟩ c| in Section~\ref{sec:sym-binary} where the value contained in |b| is always a multiple of $2$.
But if we allow a mixed faction, say $8\frac{3}{10}$, to be a digit, the same number $987$ could be written $9\,8\frac{3}{10}\,4$, denoting $9 \times 10^2 + 8\frac{3}{10} \times 10 + 4$ --- the two most significant digits now represent $983$!
Pushing it a bit further, $9\frac{21}{100}\, 6\frac{3}{10}\,3$ is yet another representation of $987$.
%
Note that we still want every prefix of a number to represent a whole number.
Therefore, the most significat digit in $9\frac{21}{100}\, 6\frac{3}{10}\,3$ may have $100$ as its denominator, while the second digit may only use $10$ and not $100$.

Our view is that \emph{Finger Trees arise
from symmetrical, redundant, zeroless binary numbers with mixed fractional digits}.
Consider again |m = | $17 =$  |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1|.
Let |k = D2 ⟨ B0 ⟩ D1| (decimal $3$).
The result of |add m k| could be
\begin{spec}
   D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D2{-"\!\frac{1}{2}"-} ⟩ D1 {-"~~,"-}
\end{spec}
which represents $20$.
The leftmost |D2| and the rightmost |D1| are respectively inherited from |m| and |k|,
while |D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D2{-"\!\frac{1}{2}"-}| in the middle represents $17$.
Let |n = | $7 =$ |D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1|. The result of |add m n| is
\begin{spec}
 D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D2{-"\!\frac{3}{4}"-} ⟩ D1 ⟩ D1 {-"~~,"-}
\end{spec}
which reprsents $24$.
The two |D2|'s on the lefthand side are taken from |n|, while the two |D1|'s from the righthand side are from |m|.
One can imagine the possibilty of a digit-by-digit implementation of |add| that traverses through the structures of |m| and |n| while constructing the result.
The |D1 ⟨ B0 ⟩ D2{-"\!\frac{3}{4}"-}| in the middle represents $(1 + 2\frac{3}{4})\times 2^2 = 15$.

Likewise, in this representation we still want the partially constructed numbers in every depth to represent a whole number.
In |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D2{-"\!\frac{1}{2}"-} ⟩ D1|,
the digit |D2{-"\!\frac{1}{2}"-}| has depth $1$ and is therefore allowed to have $2^1$ in the denominator;
in |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D2{-"\!\frac{3}{4}"-} ⟩ D1 ⟩ D1|
the digit |D2{-"\!\frac{3}{4}"-}| has depth $2$, and is allowed to have $2^2 = 4$ in the denominator.

These ideas will be made precise in the next few sections.

\subsection{Representing fractional digits}

How shall we represent a fractional digit?
The following datatype |Sesq| represents a ``one'' possibly trailed by a fraction number (we loosely adopt the Latin prefix \emph{sesqui} that means ``one and a half'').
The type |Sesq n| is a non-empty tree whose internal nodes may have two or three children, and every leaf, |one|, sits at the same depth |n|.
\begin{code}
  data Sesq : ℕ → Set where
    one        : Sesq 0
    [_+_]/2    : ∀ {n} → Sesq n → Sesq n → Sesq (suc n)
    [_+_+_]/2  : ∀ {n} → Sesq n → Sesq n → Sesq n → Sesq (suc n) {-"~~."-}
\end{code}
The intention is that |Sesq n| is a mixed fraction that may appear at depth |n| in a symmetric binary number.
The leaf |one| is the only ``one'' that may appear at depth $0$ --- no fractions allowed.
At depth |1|, we may have |[ one + one ]/2 : Sesq 1|, which corresponds to a digit $1$ in binary representation.
It accommodates two |one|'s, since each time we descend a level in binary representation, the value contained is doubled.
It is the third constructor that is new:
we may also have |[ one + one + one ]/2 : Sesq 1| at depth $1$, which represents $\frac{3}{2} = 1\frac{1}{2}$.

More generally, let the function |sizeS| count the number of |one|'s in a tree:
\begin{code}
  sizeS : ∀ {n} → Sesq n → ℕ
  sizeS one              = 1
  sizeS [ f + g ]/2      = sizeS f + sizeS g
  sizeS [ f + g + h ]/2  = sizeS f + sizeS g + sizeS h {-"~~."-}
\end{code}
A tree |f| having type |Sesq n| denotes the dyadic rational |sizeS f / {-"2^n"-}|.

\subsection{The symmetric fractional binary}

Each of the digits |D1|, |D2|, and |D3| is indexed by the depth where it may appear, and contains the corresponding number of |Sesq|s:
\begin{code}
  data Digit : ℕ → Set where
    D1 : ∀ {n} → Sesq n                    → Digit n
    D2 : ∀ {n} → Sesq n → Sesq n           → Digit n
    D3 : ∀ {n} → Sesq n → Sesq n → Sesq n  → Digit n {-"~~,"-}
  data Binary : ℕ → Set where
    B0     : ∀ {n} → Binary n
    B1     : ∀ {n} → Sesq n → Binary n
    _⟨_⟩_  : ∀ {n} → Digit n → Binary (suc n) → Digit n → Binary n {-"~~."-}
\end{code}
The depth |n| increments as we descend towards the middle.
A whole number is a |Binary 0|.
Its value is obtained by summing the fractional contributions:
\begin{code}
  sizeB : ∀ {n} → Binary n → ℕ
  sizeB B0             = 0
  sizeB (B1 f)         = sizeS f
  sizeB (df ⟨ b ⟩ dr)  = sizeD df + sizeB b + sizeD dr {-"~~,"-}

  toN : Binary 0 → ℕ
  toN = sizeB {-"~~,"-}
\end{code}
where |sizeD : ∀ {n} → Digit n → ℕ| sums up the mixed fractions of a digit.

The function |incL|, which increments a number by $1$ at the left end,
is now a special case of |incL'|, which adds a |Sesq| to a number at the left end:
\begin{code}
  incL : Binary 0 → Binary 0
  incL b = incL' one b {-"~~,"-}

  incL' : ∀ {n} → Sesq n → Binary n → Binary n
  incL' f B0                   = B1 f
  incL' f (B1 g)               = D1 f ⟨ B0 ⟩ D1 g
  incL' f (D1 g ⟨ b ⟩ dr)      = D2 f g ⟨ b ⟩ dr
  incL' f (D2 g h ⟨ b ⟩ dr)    = D3 f g h ⟨ b ⟩ dr
  incL' f (D3 g h i ⟨ b ⟩ dr)  = D2 f g ⟨ incL' [ h + i ]/2 b ⟩ dr {-"~~."-}
\end{code}
The last case of |incL'| is the crucial one.
When the leftmost digit is saturated (|D3 g h i|), we keep |D2 f g|, pair up the overflowing |h| and |i| into a single next-depth fraction |[ h + i ]/2|, and carry \emph{that} inward with a recursive |incL'|.
The function |incR'|, which adds a |Sesq| at the right end, is defined symmetrically.

While |incL' f| adds a |Sesq| to a number, |decL| removes the leftmost |Sesq| from a number:
\begin{code}
  decL : ∀ {n} → Binary n → Binary n
  decL B0                            = B0
  decL (B1 f)                        = B0
  decL (D2 f g ⟨ b ⟩ dr)             = D1 g ⟨ b ⟩ dr
  decL (D3 f g h ⟨ b ⟩ dr)           = D2 g h ⟨ b ⟩ dr
  decL (D1 f ⟨ B0 ⟩ D1 g)            = B1 g
  decL (D1 f ⟨ B1 [ g + h ]/2 ⟩ dr)  = D2 g h ⟨ B0 ⟩ dr
  decL (D1 f ⟨ m@(D1 [ g + h ]/2 ⟨ _ ⟩ _) ⟩ dr) = D2 g h ⟨ decL m ⟩ dr
  {-"\mbox{... other cases omitted.}"-}
\end{code}
The cases for |B0|, |B1|, |D2|, and |D3| are relatively easy.
The more interesting cases are those where the leftmost digit is |D1|, where we have to borrow from the inside and, when necessary, split the next digit we encounter.

It can be proved that |incL' f b| does increase the value of |b| by |sizeS f|,
and |decL b| decreases |b| by |leadSize b|, size of the leftmost |Sesq| of |b|:
\begin{code}
incL'-correct : ∀ {n} (f : Sesq n) (b : Binary n)
      → sizeB (incL' f b) ≡ sizeS f + sizeB b {-"~~,"-}
decL-general : ∀ {n} (b : Binary n)
      → sizeB (decL b) ≡ sizeB b ∸ leadSize b {-"~~,"-}
\end{code}
therefore, |incL| does perform increment, while |decL| decrements a number when it is a |Binary 0|, whose leftmost |Sesq| must be a |one|:
\begin{code}
incL-correct  : ∀ (b : Binary 0) → toN (incL b)  ≡ suc (toN b) {-"~~,"-}
decL-correct  : ∀ (b : Binary 0) → toN (decL b)  ≡ pred (toN b) {-"~~."-}
\end{code}

\subsection{Addition}

We are now ready to present a digit-by-digit implementation of addition.
The main idea is that, to add |x| and |y|, we keep the leftmost digit of |x| and the rightmost digit of |y|, while recursively process the middle.
To maintain the middle part, we generalise addition to take three arguments:
\begin{code}
add : Binary 0 → Binary 0 → Binary 0
add x y = add3 x D0 y {-"~~."-}
\end{code}
It turns out that the middle part needs only be a digit!
For the initial value, we extend |Digit| to allow an additional constructor that represents $0$:
\begin{code}
  data Digit' : ℕ → Set where
    D0 : ∀ {n} → Digit' n
    D1 : ∀ {n} → Sesq n                    → Digit' n
    D2 : ∀ {n} → Sesq n → Sesq n           → Digit' n
    D3 : ∀ {n} → Sesq n → Sesq n → Sesq n  → Digit' n {-"~~."-}
\end{code}
The type of |add3| is then given by:
\begin{code}
add3 : ∀ {n} → Binary n → Digit' n → Binary n → Binary n {-"~~."-}
\end{code}

%format xf = "{\Var x}_{f}"
%format xr = "{\Var x}_{r}"
%format yf = "{\Var y}_{f}"
%format yr = "{\Var y}_{r}"
Given the flexibility of factional digits, the function |add3| turns out to be surprisingly simple.
Let |addDL : ∀ {n} → Digit' → Binary n → Binary n| add a digit to a number (by repeatedly calling |incL'|), and let |addDR| be its righthand side counterpart.
The base cases of |add3|, where at least one of the numbers is |B0| or |B1|, are easy:
\begin{code}
add3 B0      d y       = addDL d y
add3 (B1 f)  d y       = incL' f (addDL d y)
add3 x       d B0      = addDR xd
add3 x       d (B1 f)  = incR' (addDR x d) f {-"~~."-}
\end{code}
The last case is when both numbers are |_⟨_⟩_|:
\begin{code}
add3 (xf ⟨ x ⟩ xr) d (yf ⟨ y ⟩ yr) = xf ⟨ add3 x (combine xr d yf) y ⟩ yr {-"~~,"-}
\end{code}
where we recurse on |x| and |y|, and use an auxiliary function |combine| that squeezes |xr|, |d|, and |yf| into a single digit.
But is that possible?

Certainly! The function |combine| has type:
\begin{code}
combine : ∀ {n} → Digit n → Digit' n → Digit n → Digit' (suc n)
\end{code}
In |combine a d b|, the values of |a| and |b| are between |{1..3}|, and the value of |d| is between |{0..3}|. The sum of the three digits ranges between |{2..9}| --- which certainly fits into a |Digit'| {one level deeper}!
\todo{Are the ranges still correct if we consider fractions?}
There are more than one way to do so.
The |Digit'| is built using |[ _ + _ ]/2| and |[ _ + _ + _ ]/2|.
A reasonable heuristic is to try to evenly partition the values into the branches.
The following are some example cases:
\begin{spec}
  combine (D1 f)      D0           (D1 g)        = D1 [ f + g ]/2
  combine (D1 f)      D0           (D3 g h i)    = D2 [ f + g ]/2 [ h + i ]/2
  combine (D3 f g h)  (D3 i j k)   (D3 l m p)    = D3 [ f + g + h ]/2 [ i + j + k ]/2 [ l + m + p ]/2
  {-"\mbox{(other cases omitted)}"-}
\end{spec}
How |combine| actually builds the digit does not matter to the asymptotic complexity of |add|.
What matter is that |combine| is a constant time operation.
While there are more clever ways to define |combine|,
it is essentially a constant-time function that can be defined non-recursively by exhaustively matching all the cases.

The function |add3| is defined inductively on the structure of the given numbers and calls, |combine|, a constant time operation before each recursion.
It calls |incL'| and |incR'|, etc., only at the base cases.
Therefore |add| has a logarithmic worst-case time-complexity.
By a lengthy but routine proof one may show that |add| is correct:
\begin{code}
  add-correct : ∀ (x y : Binary 0) → toN (add x y) ≡ toN x + toN y {-"~~."-}
\end{code}

\subsection{Finger Trees}

The Finger Tree is obtained by ornamenting the symmetrical, redundant binary numbers with mixed fractional digits with data.
A fraction |f : Sesq n| induces a tree holding |sizeS f| elements:
\begin{code}
  data Tree (A : Set) : (n : ℕ) → Sesq n → Set where
    leaf   : A → Tree A 0 one
    node2  : ∀ {n f g}    → Tree A n f → Tree A n g
           → Tree A (suc n) [ f + g ]/2
    node3  : ∀ {n f g h}  → Tree A n f → Tree A n g → Tree A n h
           → Tree A (suc n) [ f + g + h ]/2 {-"~~."-}
\end{code}
These are precisely the internal $2$-$3$ nodes of a Finger Tree.
The types |Some| and |FingerTree| are respectively induced by |Digit| and |Binary|:
\begin{code}
  data Some (A : Set) (n : ℕ) : Digit n → Set where
   one    : ∀ {f}     → Tree A n f                             → Some A n (D1 f)
   two    : ∀ {f g}   → Tree A n f → Tree A n g                → Some A n (D2 f g)
   three  : ∀ {f g h} → Tree A n f → Tree A n g → Tree A n h   → Some A n (D3 f g h) {-"~~,"-}

  data FingerTree (A : Set) (n : ℕ) : Binary n → Set where
    nil    : FingerTree A n B0
    [_]    : ∀ {f} → Tree A n f → FingerTree A n (B1 f)
    _⟨_⟩_  : ∀ {df dr b}  → Some A n df → FingerTree A (suc n) b
                          → Some A n dr → FingerTree A n (df ⟨ b ⟩ dr) {-"~~."-}
\end{code}

Adding an element to the left mirrors |incL'|:
\begin{code}
  cons' : ∀ {A n b f} → Tree A n f → FingerTree A n b → FingerTree A n (incL' f b)
  cons' x nil                     = [ x ]
  cons' x [ y ]                   = one x ⟨ nil ⟩ one y
  cons' x (one y        ⟨ b ⟩ r)  = two x y ⟨ b ⟩ r
  cons' x (two y z      ⟨ b ⟩ r)  = three x y z ⟨ b ⟩ r
  cons' x (three y z w  ⟨ b ⟩ r)  = two x y ⟨ cons' (node2 z w) b ⟩ r {-"~~,"-}

  cons : ∀ {A b} → A → FingerTree A 0 b → FingerTree A 0 (incL b)
  cons x xs = cons' (leaf x) xs {-"~~."-}
\end{code}
The carry case builds a |node2 z w| and conses it into the spine --- the ornamented image of |addSL| turning a |D3| into a next-depth |[ h + i ]/2|.
Because the leftmost element always sits at the front, |head| is $O(1)$:
\begin{code}
  head : ∀ {A b} → FingerTree A 0 b → (b ≢ B0) → A {-"~~,"-}
\end{code}
while |snoc| and |tail| mirror |incR| and |decL|:
\begin{code}
  snoc : ∀ {A b} → FingerTree A 0 b → A → FingerTree A 0 (incR b) {-"~~,"-}
  tail : ∀ {A n b} → FingerTree A n b → FingerTree A n (decL b) {-"~~."-}
\end{code}

\subsection{Concatenation}

The function |append| is the container version of |add|.
Like |add|, it is defined in terms of an auxiliary function |glue|, the container version of |add3|.
The latter function now joins two |FingerTree|s, with a |Some'| in the middle that contains zero to three |Tree|s.
\begin{code}
  glue : ∀ {A n b₁ d b₂}  → FingerTree A n b₁ → Some' A n d
                          → FingerTree A n b₂ → FingerTree A n (add3 b₁ d b₂)
  glue nil    s ys     = appendSome'L s ys
  glue [ x ]  s ys     = cons' x (appendSome'L s ys)
  glue xs     s nil    = appendSome'R xs s
  glue xs     s [ y ]  = snoc' (appendSome'R xs s) y
  glue (xf ⟨ xs ⟩ xr) s (yf ⟨ ys ⟩ yr) = xf ⟨ glue xs (combineSome xr s yf) ys ⟩ yr {-"~~,"-}

  append  : ∀ {A b₁ b₂}  → FingerTree A 0 b₁ → FingerTree A 0 b₂
                         → FingerTree A 0 (add b₁ b₂)
  append xs ys = glue xs zero ys {-"~~."-}
\end{code}
Utilised by |glue| is a function |combineSome|, corresponding to |combine|, having type:
\begin{code}
combineSome  : ∀ {A n d₁ d₂ d₃} → Some A n d₁ → Some' A n d₂
             → Some A n d₃ → Some' A (suc n) (combine d₁ d₂ d₃) {-"~~,"-}
\end{code}
that joins two |Some| and a |Some'| into a |Some'| of the next level.
All these functions inherit the same time complexities of their numerical counterparts.

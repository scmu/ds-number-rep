\section{Fractional digits}

What if we allow mixed fractions in digits?

In decimal representation, the digits are integers in $\{0..9\}$, and $987$, for example, denotes $9 \times 10^2 + 8 \times 10 + 7$.
In a decimal number $d_2 d_1 d_0$, the value contained by the $d_2 d_1$ part is always a multiple of $10$,
just like in |d ⟨ b ⟩ c| in Section~\ref{sec:sym-binary} where the value contained in |b| is always a multiple of $2$.
But if we allow a mixed faction, say $8\frac{3}{10}$, to be a digit, the same number $987$ could be written $9\,8\frac{3}{10}\,4$, denoting $9 \times 10^2 + 8\frac{3}{10} \times 10 + 4$ --- the two most significant digits now represent $983$!
Pushing it a bit further, $9\frac{21}{100}\, 6\frac{3}{10}\,3$ is yet another representation of $987$.

Note that we still want every prefix of a number to represent a whole integer.
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
One can imagine the possibilty of a digit-by-digit implementation of |add| that traverses through the structures of |m| and |n|.
The |D1 ⟨ B0 ⟩ D2{-"\!\frac{3}{4}"-}| in the middle represents $(1 + 2\frac{3}{4})\times 2^2 = 15$.

Likewise, in this representation we still want the partially constructed numbers in every depth to represent a whole integer.
In |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D2{-"\!\frac{1}{2}"-} ⟩ D1|,
the digit |D2{-"\!\frac{1}{2}"-}| has depth $1$ and is therefore allowed to have $2^1$ in the denominator;
in |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D2{-"\!\frac{3}{4}"-} ⟩ D1 ⟩ D1|
the digit |D2{-"\!\frac{3}{4}"-}| has depth $2$, and is allowed to have $2^2 = 4$ in the denominator.

These ideas will be made precise in the next few sections.

\subsection{Fractional digits}

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
The leaf |one| is the only ``one'' allowed at depth $0$ --- no fractions allowed.
At depth |1|, we may have |[ one + one ]/2|, which corresponds to a digit $1$ in binary representation.
It accommodates two |one|'s, since each time we descend a level in binary representation, the value contained is doubled.
It is the third constructor that is new:
we may also have |[ one + one + one ]/2| at depth $1$, which represents $\frac{3}{2} = 1\frac{1}{2}$.

More generally, let the function |sizeS| count the number of |one|'s in a tree:
\begin{code}
  sizeS : ∀ {n} → Sesq n → ℕ
  sizeS one              = 1
  sizeS [ f + g ]/2      = sizeS f + sizeS g
  sizeS [ f + g + h ]/2  = sizeS f + sizeS g + sizeS h {-"~~."-}
\end{code}
A tree |f| having type |Sesq n| thus denotes the dyadic rational |sizeS f / {-"2^n"-}|.

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
where |sizeD| sums up the mixed fractions of a digit.

The function |incL|, which increments a number by $1$ to the lefthand side,
is now a special case of |addSL|, which adds a |Sesq| to a number at the left end:
\begin{code}
  incL : Binary 0 → Binary 0
  incL b = addSL one b {-"~~,"-}

  addSL : ∀ {n} → Sesq n → Binary n → Binary n
  addSL f B0                   = B1 f
  addSL f (B1 g)               = D1 f ⟨ B0 ⟩ D1 g
  addSL f (D1 g ⟨ b ⟩ dr)      = D2 f g ⟨ b ⟩ dr
  addSL f (D2 g h ⟨ b ⟩ dr)    = D3 f g h ⟨ b ⟩ dr
  addSL f (D3 g h i ⟨ b ⟩ dr)  = D2 f g ⟨ addSL [ h + i ]/2 b ⟩ dr {-"~~."-}
\end{code}
The last case of |addSL| is the crucial one.
When the leftmost digit is saturated (|D3 g h i|), we keep |D2 f g|, pair up the overflowing |h| and |i| into the single next-depth fraction |[ h + i ]/2|, and carry \emph{that} inward with a recursive |addSL|.
Adding a |Sesq| at the right end, |addSR|, is defined symmetrically.

While |addSL f| adds a |Sesq| to a number, |decL| removes the leftmost |Sesq| from a number:
\begin{code}
  decL : ∀ {n} → Binary n → Binary n
  decL B0                            = B0
  decL (B1 f)                        = B0
  decL (D2 f g ⟨ b ⟩ dr)             = D1 g ⟨ b ⟩ dr
  decL (D3 f g h ⟨ b ⟩ dr)           = D2 g h ⟨ b ⟩ dr
  decL (D1 f ⟨ B0 ⟩ D1 g)            = B1 g
  decL (D1 f ⟨ B1 [ g + h ]/2 ⟩ dr)  = D2 g h ⟨ B0 ⟩ dr
  decL (D1 f ⟨ m@(D1 [ g + h ]/2 ⟨ _ ⟩ _) ⟩ dr) = D2 g h ⟨ decL m ⟩ dr {-"~~..."-}
\end{code}
(we omit the rest of the cases that are similar),
The cases for |B0|, |B1|, |D2|, and |D3| are relatively easy.
The more interesting cases are those where the leftmost digit is |D1|, where we have to borrow from the inside and split the next digit we encounter.

These operations respect the semantics at every depth: |addSL f| adds a whole tree of |sizeS f| elements, and |decL| removes the leftmost such tree.
\begin{code}
  addSL-correct : ∀ {n} (f : Sesq n) (b : Binary n)
                → sizeB (addSL f b) ≡ sizeS f + sizeB b {-"~~,"-}
  decL-general : ∀ {n} (b : Binary n) → sizeB (decL b) ≡ sizeB b ∸ leadSize b {-"~~,"-}
\end{code}
The genuine increment and decrement are the special case at depth |0|, where |one| --- and hence the leftmost tree --- is a single leaf of size |1|.
They therefore change the element count by exactly one:
\begin{code}
  incL-correct  : ∀ (b : Binary 0) → toN (incL b)  ≡ suc (toN b) {-"~~,"-}
  decL-correct  : ∀ (b : Binary 0) → toN (decL b)  ≡ pred (toN b) {-"~~."-}
\end{code}

\subsection{Addition}

We can now solve the problem that stumped the plain symmetric representation.
Recall that, adding two numbers by stripping their outermost digits and recursing, we were forced to store an \emph{odd} number in the middle.
Fractional digits absorb the difficulty.
Rather than splitting an odd leftover evenly, we gather all the fractions that meet in the middle and repackage them into next-depth fractions --- each the average of two or three of the originals --- threading the result inward as an ordinary carry.
To carry a whole digit we allow it to be empty as well:
\begin{code}
  data Digit' : ℕ → Set where
    D0 : ∀ {n} → Digit' n
    D1 : ∀ {n} → Frac n                    → Digit' n
    D2 : ∀ {n} → Frac n → Frac n           → Digit' n
    D3 : ∀ {n} → Frac n → Frac n → Frac n  → Digit' n {-"~~."-}
\end{code}
The heart of addition is |combineDigits|, which merges the two inner digits meeting in the middle (one from each operand) with the incoming carry digit into a single digit \emph{one level deeper}.
Together the three inputs hold some number $t$ of depth-|n| fractions, with $2 \le t \le 9$.
We repartition them into groups of two or three --- each group becoming one next-depth fraction via |[ _ + _ ]/2| or |[ _ + _ + _ ]/2| --- producing a |Digit'| of $a + b$ fractions with $t = 2a + 3b$.
The division into twos and threes is not forced, we simply fix one:
\begin{spec}
  combineDigits (D1 f)      D0           (D1 g)        = D1 [ f + g ]/2
  combineDigits (D1 f)      D0           (D3 g h i)    = D2 [ f + g ]/2 [ h + i ]/2
  combineDigits (D3 f g h)  (D3 i j k)   (D3 l m p)    = D3 [ f + g + h ]/2 [ i + j + k ]/2 [ l + m + p ]/2 {-"~~,"-}
\end{spec}
and so on for the remaining cases, which group their fractions in the same left-to-right fashion.
Addition then keeps the two outermost digits and recurses on the middles, feeding the combined carry inward:
\begin{code}
  add3 : ∀ {n} → Binary n → Digit' n → Binary n → Binary n
  add3 B0            d y               = addD'L d y
  add3 (B1 f)        d y               = addFL f (addD'L d y)
  add3 (xf ⟨ x ⟩ xr) d B0             = addD'R (xf ⟨ x ⟩ xr) d
  add3 (xf ⟨ x ⟩ xr) d (B1 f)         = addFR (addD'R (xf ⟨ x ⟩ xr) d) f
  add3 (xf ⟨ x ⟩ xr) d (yf ⟨ y ⟩ yr)  = xf ⟨ add3 x (combineDigits xr d yf) y ⟩ yr {-"~~,"-}

  add : Binary 0 → Binary 0 → Binary 0
  add x y = add3 x D0 y {-"~~."-}
\end{code}
Here |addD'L| and |addD'R| add a carry digit to a number by repeated |addFL|/|addFR|.
Crucially, |add3| is a genuine \emph{digit-by-digit} algorithm, each recursive call descends one depth, where the weights have doubled.
It computes the right answer:
\begin{code}
  add-correct : ∀ (x y : Binary 0) → toN (add x y) ≡ toN x + toN y {-"~~."-}
\end{code}

\subsection{Finger Trees}

As before, each numerical type induces a container by ornamenting its constructors with data.
A fraction |f : Frac n| becomes a \emph{tree} holding |sizeF f| elements, whose branching follows |f| exactly:
\begin{code}
  data Tree (A : Set) : (n : ℕ) → Frac n → Set where
    leaf   : A → Tree A 0 one
    node2  : ∀ {n f g}    → Tree A n f → Tree A n g               → Tree A (suc n) [ f + g ]/2
    node3  : ∀ {n f g h}  → Tree A n f → Tree A n g → Tree A n h  → Tree A (suc n) [ f + g + h ]/2 {-"~~."-}
\end{code}
These are precisely the internal $2$-$3$ nodes of a Finger Tree: |[ f + g ]/2| is realised by a |node2|, and |[ f + g + h ]/2| by a |node3|.
A |Digit| ornaments into a |Some|, and a |Binary| into a |FingerTree|:
\begin{code}
  data Some (A : Set) (n : ℕ) : Digit n → Set where
    one    : ∀ {f}     → Tree A n f                             → Some A n (D1 f)
    two    : ∀ {f g}   → Tree A n f → Tree A n g                → Some A n (D2 f g)
    three  : ∀ {f g h} → Tree A n f → Tree A n g → Tree A n h   → Some A n (D3 f g h) {-"~~,"-}
  data FingerTree (A : Set) (n : ℕ) : Binary n → Set where
    nil        : FingerTree A n B0
    singleton  : ∀ {f} → Tree A n f → FingerTree A n (B1 f)
    more       : ∀ {df dr b} → Some A n df → FingerTree A (suc n) b → Some A n dr
               → FingerTree A n (df ⟨ b ⟩ dr) {-"~~."-}
\end{code}
This is exactly the Finger Tree of \citet{HinzePaterson:06:Finger}: a |more| node is a prefix (|Some|), a spine of one-deeper trees, and a suffix (|Some|); |nil| and |singleton| are the two shallow cases.
The operations transfer directly.
Adding an element to the left mirrors |addFL|:
\begin{code}
  cons' : ∀ {A n b f} → Tree A n f → FingerTree A n b → FingerTree A n (addFL f b)
  cons' x nil                    = singleton x
  cons' x (singleton y)          = more (one x) nil (one y)
  cons' x (more (one y) b r)     = more (two x y) b r
  cons' x (more (two y z) b r)   = more (three x y z) b r
  cons' x (more (three y z w) b r) = more (two x y) (cons' (node2 z w) b) r {-"~~,"-}

  cons : ∀ {A b} → A → FingerTree A 0 b → FingerTree A 0 (incL b)
  cons x xs = cons' (leaf x) xs {-"~~."-}
\end{code}
The carry case builds a |node2 z w| and conses it into the spine --- the ornamented image of |addFL| turning a |D3| into a next-depth |[ h + i ]/2|.
Because the leftmost element always sits at the front, |head| is $O(1)$:
\begin{code}
  head : ∀ {A b} → FingerTree A 0 b → (b ≢ B0) → A {-"~~,"-}
\end{code}
while |snoc| and |tail| mirror |addFR| and |decL|:
\begin{code}
  tail : ∀ {A n b} → FingerTree A n b → FingerTree A n (decL b) {-"~~."-}
\end{code}

\subsection{Concatenation}

Concatenation is the container-level image of |add|, and it inherits its digit-by-digit efficiency.
The carry digit of |add3| becomes a bundle of up to three trees, a |Some'| (the ornament of |Digit'|, with an empty case |zero|), and |combineDigits| becomes |combineSome|, which packs the two inner suffix/prefix bundles together with the carry into next-depth nodes.
The recursion mirrors |add3| line for line:
\begin{code}
  glue : ∀ {A n b₁ d b₂} → FingerTree A n b₁ → Some' A n d → FingerTree A n b₂
       → FingerTree A n (add3 b₁ d b₂)
  glue nil             s ys              = appendSome'L s ys
  glue (singleton x)   s ys              = cons' x (appendSome'L s ys)
  glue (more xf xs xr) s nil             = appendSome'R (more xf xs xr) s
  glue (more xf xs xr) s (singleton y)   = snoc' (appendSome'R (more xf xs xr) s) y
  glue (more xf xs xr) s (more yf ys yr) = more xf (glue xs (combineSome xr s yf) ys) yr {-"~~,"-}

  append : ∀ {A b₁ b₂} → FingerTree A 0 b₁ → FingerTree A 0 b₂ → FingerTree A 0 (add b₁ b₂)
  append xs ys = glue xs zero ys {-"~~."-}
\end{code}
This is the standard Finger Tree concatenation, and its type states precisely that |append| realises |add| on the sizes.
Since |add| is digit-by-digit, |append| runs in $O(\log (\min (m , n)))$ time.

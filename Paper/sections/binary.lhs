\section{Binary numbers}

As mentioned in Section~\ref{sec:intro}, cons-lists can be seen as derived from the unary representation of natural numbers.
The |cons| operator corresponds to successor, and |append| addition.
In this representation we get $O(1)$ |cons|, |head|, and |tail|, linear-time append, and linear-time indexing.%
\footnote{The term ``indexing'' has two meaning in this pearl:
finding a certain element in a list given its index,
or indexing an inductive family of types.
We believe that they should be distinguishable from the context.
}

Can we achieve $O(\log n)$ indexing if we switch to a binary representation?

\subsection{Naive binary representation}

Consider the following representation of binary numbers:%
\footnote{While we use Agda in this pearl, we sometimes switch to this Haskell-like notation for brevity.}
\begin{spec}
data Digit   = D0 | D1 {-"~~,"-}
data Binary  = [] | Digit ∷ Binary {-"~~."-}
\end{spec}
To manifest its connection with cons-lists, in this pearl we present binary numbers least-significant digit first.
For example, |D1 ∷ D0 ∷ D1 ∷ D1 ∷ B0| denotes $1 \times 2^0 + 0 \times 2^1 + 1 \times 2^2 + 1 \times 2^3 =$ $1 + 4 + 8 = 13$.
One may already have noticed a potential problem: one may construct a |Binary| with a long sequence of trailing |D0|'s that contributes nothing.
For example, while |D1 ∷ D1 ∷ B0| denotes $4$, so does |D1 ∷ D1 ∷ D0 ∷ D0 ... B0|, and when we process a number left-to-right we do not know whether we end up with all |D0|'s.
There are several approaches we can take to avoid the trailing zeros, but we will keep it simple for now, before moving on to another representation.

The definitions above induce two datatypes, respectively indexed by |Digit| and |Binary|:
\begin{code}
  data Some (A : Set) : Digit → Set where
    zero  :          Some A D0
    one   : A →      Some A D1 {-"~~,"-}
  data BList (A : Set) : Binary → Set where
    nil   : BList A B0
    _∷_  : ∀ {d b} → Some A d → BList (A × A) b → BList A (d ∷ b) {-"~~."-}
\end{code}
Each position of |BList A n| may contain some data (|one _|) or not (|zero|).
Notice that at each successive position in |BList|, the element type \emph{doubles} to |A × A|, corresponding to the fact that the base doubles in a binary representation.

Incrementing a |Binary| and |cons|ing to a |BList| are respectively defined by:\\[-0.8\baselineskip]
\begin{minipage}[t]{0.33\textwidth}
\begin{code}
inc : Binary → Binary
inc B0        = D1 ∷ B0
inc (D0 ∷ b)  = D1 ∷ b
inc (D1 ∷ b)  = D0 ∷ inc b {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
cons : ∀ {A b} → A → BList A b → BList A (inc b)
cons x nil           = one x  ∷ nil
cons x (zero ∷ xs)   = one x  ∷ xs
cons x (one y ∷ xs)  = zero   ∷ cons (x{-"\!"-}, y) xs {-"~~."-}
\end{code}
\end{minipage}\\
The definition of |cons| mirrors that of |inc|.
Notice how the carrying in |inc| corresponds to consing |( x{-"\!"-}, y )| to the tail of the list.
In fact, when coding up |cons| in Agda, the programmer, guided by |inc| in its type, is often left with only one reasonable way to fill in the right hand sides.

One problem with |BList| is that |head| is no longer $O(1)$.
The easy case |head (one x ∷ xs)| yields |x| immediately,
but when encountering |head (zero ∷ xs)|, we have to look into |xs| to find the leftmost element, which may turn out to start with |zero| as well!
It appears that the presence of |D0| has caused various issues.
Can we do away with it?

\subsection{Zeroless representation}

Let us drop |D0| and let the digits be |D1| and |D2| instead:
\begin{spec}
data Digit = D1 | D2 {-"~~."-}
\end{spec}
The definition of |Binary| stays the same. Albeit having |D2| as a digit, we still intend the number to be 2-based.
For example, |D1 ∷ D2 ∷ D1 ∷ []| denotes $1 \times 2^0 +$ $2 \times$ $2^1 +$ $1 \times 2^2 = 1 + 4 + 4 = 9$.
The induced list-like datatype contains the following |Some| in each position:
\begin{code}
  data Some (A : Set) : Digit → Set where
    one  : A → Some A D1
    two  : A → A → Some A D2 {-"~~."-}
\end{code}
With this representation we resolve two problems at once: no more trailing zeros, and |head| always sees an element in the leftmost position!

Consider how increment and decrement are defined:
\\[-0.8\baselineskip]
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  inc : Binary → Binary
  inc B0        = D1 ∷ B0
  inc (D1 ∷ n)  = D2 ∷ n
  inc (D2 ∷ n)  = D1 ∷ inc n {-"~~,"-}
\end{code}
\end{minipage}%
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  dec : Binary → Binary
  dec B0         = B0
  dec (D1 ∷ B0)  = B0
  dec (D1 ∷ n)   = D2 ∷ dec n
  dec (D2 ∷ n)   = D1 ∷ n {-"~~."-}
\end{code}
\end{minipage}\\
Carrying in |inc| happens when we counter a leading |D2|, in that case we increment the tail, \emph{whose weights are doubled}, and leave a |D1| behind.
The corresponding case in |cons| makes the passing of values more explicit:
\begin{spec}
cons x (two y z ∷ xs) = one x ∷ cons (y{-"\!"-}, z) xs {-"~~,"-}
\end{spec}
one can see that we leave |x| behind and carry |(y{-"\!\!"-}, z)| to the tail.
Decrement does the reverse: when decrementing |D1 ∷ n|, we borrow a $1$ from |n|, and the least significant digit becomes |D2|.

Having |inc| and |dec|, one of the ways to define addition of two |Binary|s is given below:
\begin{spec}
add : Binary -> Binary
add B0  n = n
add m   n = inc (add (dec m) n) {-"~~."-}
\end{spec}

Let $n$ be the number represented by some |Binary|.
The worst-case time complexity of |inc| and |dec| are both $O(\log n)$.
It it worth taking some time musing how the logarithmic complexity is achieved.
Both |inc| and |dec| work \emph{digit-by-digit} ---
in their recurve cases |inc (D2 ∷ n) = D1 ∷ inc n| and |dec (D1 ∷ n) = D2 ∷ dec n|, they both consume a digit, produce a digit, and recurse on the tail.
Each time we descend on the tail, the value the next digit denotes gets \emph{twice} as large --- in the induced container datatype that means each |D1| stands for a |A × A|, then a |(A × A) × (A × A)|..., etc.
Thus the actions in the tail gets twice as efficient.
This is in contrast to |add|, which processes its input \emph{one-by-one} --- the value is decremented by \emph{one} in each recursive call.
This definition of |add| cannot take advantage of the binary representation.

In fact, in repeated applications of |inc|, each call has amortised time complexity $O(1)$.
\todo{explain in one sentence}
The same reasoning applies to |dec|.
Meanwhile, the complexity of |add m n| is still $O(m)$ at best.
One of the objectives of the rest of this article is to come up with an |add| having logarithmic time complexity.

If we mix |inc| and |dec|, however, we lost the amortised $O(1)$ behaviour.
The function |inc| is the most costly when the input is a long sequence of |D2|'s, for which |inc| has to traverse to the end.
The output for this case is a long sequence of |D1|'s, which is the most costly case for |dec|.
In an unlucky scenario, |inc| and |dec| are alternately applied to their worst cases, with each operation taking logarithm time.

\subsection{Redundant binary representation}
\label{sec:redundant-binary}

Surprisingly, amortised $O(1)$ performance of mixed |inc| and |dec| can be achieved by \emph{adding another digit} in our numerical representation:
\begin{spec}
data Digit = D1 | D2 | D3 {-"~~."-}
\end{spec}
A consequence is that the representation of a number is no longer unique.
For example, both |D3 ∷ D1 ∷ []| and |D1 ∷ D2 ∷ []| denote |5|.
We will soon see that such redundancy turns out to be beneficial efficiency-wise.

In |inc|, a carry propagates to the tail in the case for |D3 ∷ n|, in which the least-significant digit |D3| resets to |D2|.
In |dec|, we borrow a one from the tail in the case for |D1 ∷ n|:
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  inc : Binary → Binary
  inc B0        = D1 ∷ B0
  inc (D1 ∷ n)  = D2 ∷ n
  inc (D2 ∷ n)  = D3 ∷ n
  inc (D3 ∷ n)  = D2 ∷ inc n {-"~~,"-}
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  dec : Binary → Binary
  dec B0            = B0
  dec (D1 ∷ B0)     = B0
  dec (D1 ∷ n)      = D2 ∷ dec n
  dec (D2 ∷ n)      = D1 ∷ n
  dec (D3 ∷ n)      = D2 ∷ n {-"~~."-}
\end{code}
\end{minipage}\\
It is important that |inc| and |dec| recurse on different cases.
If the last case of |inc (D3 ∷ n)| is invoked, which triggers a carry, turning a |D3| to |D2| and recurse on the tail, a subsequent |dec| merely decreases |D2| to |D1| without triggering a borrow.
Symmetrically, after |dec (D1 ∷ n)|, which borrows from the tail and returns |D2 ∷ dec n|, a subsequent |inc| increases |D2| to |D3| without carrying.
The extra room in the digit range $\{1, 2, 3\}$ thus acts as a buffer that prevents carries and borrows from cascading in alternation, ensuring that the amortised cost per operation remains $O(1)$ even when |inc| and |dec| are interleaved arbitrarily.
%\todo{do we need a serious analysis?}
% scm: perhaps not, considering the space and style.

Another consequence of the redundancy in representation is that |inc| is no longer surjective (on positive numbers). \todo{Give an example.}

\paragraph{The container type}
Consider the container type induced by |Binary|.
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
  cons : ∀ {A n} → A → BList A n → BList A (inc n)
  cons x nil                  = one x        ∷ nil
  cons x (one y        ∷ xs)  = two x y      ∷ xs
  cons x (two y z      ∷ xs)  = three x y z  ∷ xs
  cons x (three y z w  ∷ xs)  = two x y      ∷ cons (z , w) xs {-"~~."-}
\end{code}

\paragraph{Implementing |tail| and |head|}
What type shall we assign to the function |tail|? There are two possibilities:
\begin{spec}
tail : ∀ {A n} → BList A (inc n) → BList A n {-"~~,"-}
tail : ∀ {A n} → BList A n → BList A (dec n) {-"~~."-}
\end{spec}
The first type induces an implementation resembles |inc|.
The problem is that it cannot be applied to all (non-empty) lists!
As mentioned above, |inc| is not surjective on positive numbers, therefore this |tail| cannot be applied to, say, a list having type |BList A ?| \todo{fill in the number}.
The second type results in a definition that is a direct translation of |dec|:
%format ∷-nonzero = "::\!\mbox{-}\Varid{nonzero}"
\begin{code}
tail : ∀ {A n} → BList A n → BList A (dec n)
tail nil                   =  nil
tail (one x ∷ nil)         =  nil
tail (one x ∷ xs @(_ ∷ _))  =  let  (y , z) = head xs (∷-nonzero xs)
                              in   two y z ∷ tail xs
tail (two x y ∷ xs)        =  one y ∷ xs
tail (three x y z ∷ xs)    =  two y z ∷ xs {-"~~."-}
\end{code}
In the third case of |dec| we borrow a bit from the tail, while in the corresponding case of |tail| we make a call to |head| in order to extract one element from the tail |xs|.
The function |head| takes a proof promising that the given list has a non-zero size:
\begin{code}
head : ∀ {A n} → BList A n → (n ≢ []) → A
head nil                  nz = contradiction refl nz
head (one x        ∷ xs)  nz = x
head (two x y      ∷ xs)  nz = x
head (three x y z  ∷ xs)  nz = x {-"~~."-}
\end{code}
%SCM: removed due to duplication.
%When |cons| and |tail| are interleaved, the redundant digit range prevents cascading carries and borrows, yielding $O(1)$ amortised cost per operation --- a strict improvement over the zeroless system under mixed workloads.

\paragraph{Summary so far}
We now have a list-like data structure that supports $O(1)$ |head| and amortised $O(1)$ |cons| and |tail|.
With this data structure it is not surprising that indexing can be performed in $O(\log n)$ time.
It turns out that there are plenty of details to be concerned, thus we postpone disucssion about indexing to Section~\ref{sec:indexing}.
Addition, which may give us |append|, is still problematic: the ``by-elements'' approach gives us linear-time addition/concatenation at best.
For now, we will turn our attention to another goal: allowing addition to and deletion from the other end of the list, hoping that will eventually lead to a faster implementation of |append|.

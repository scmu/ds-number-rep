\section{Symmetric representation}
\label{sec:sym-binary}

%format df = "{\Var d}_{f}"
%format dr = "{\Var d}_{r}"
For many reasons we want to investigate double-ended queues (deques), by which we mean list-like data structures that allow quick access to both ends.
This ability \emph{might} eventually lead to an efficient |append|, and the deque is useful data structure in itself.

To have immediate access to both ends of the data structure, we conceive a number representation that is \emph{symmetrical}:
\begin{spec}
data Digit    = D1 | D2 | D3 {-"~~,"-}
data SBinary  = B0 | B1 | Digit ⟨ SBinary ⟩ Digit {-"~~."-}
\end{spec}
Having learned the lesson in Section~\ref{sec:redundant-binary}, we use |{ D1{-"\!"-} .. {-"\!"-}D3 }| as digits --- it is therefore a zeroless, redundant representation.
In the middle of an |SBinary| is either |B0| or |B1|, respectively representing |0| and |1|. They are always surrounded by the same number of digits on both sides.
The semantics of |SBinary| is given by:
\begin{spec}
toN : SBinary → ℕ
toN B0             = 0
toN B1             = 1
toN (df ⟨ n ⟩ dr)  = ⟦ df ⟧ + 2 * toN n + ⟦ dr ⟧ {-"~~,"-}
\end{spec}
where |⟦_⟧| converts a |Digit| to a |ℕ|, e.g. |⟦ D2 ⟧ = 2|.
We will refer to positions of digits in an |SBinary| as their \emph{depths}, starting from $0$.
In |D3 ⟨ D2 ⟨ B1 ⟩ D2 ⟩ D1|, for example, the outer |D3| and |D1| have depth $0$,
while the inner |D2|'s have depth $1$. Digits at depth |i| have weight $2^i$,
therefore |D3 ⟨ D2 ⟨ B1 ⟩ D2 ⟩ D1| denotes
$3 + 2\times2^1 + 1\times2^2 + 2\times2^1 + 1 = 16$.
This representation is redundant: |D3 ⟨ D3 ⟨ B0 ⟩ D2 ⟩ D3| also represents |16|.

Increment can be performed to the left or the right of an |SBinary|, defined symmetrically:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{spec}
incL : SBinary → SBinary
incL B0            = B1
incL B1            = D1 ⟨ B0 ⟩ D1
incL (D1 ⟨ b ⟩ d)  = D2 ⟨ b ⟩ d
incL (D2 ⟨ b ⟩ d)  = D3 ⟨ b ⟩ d
incL (D3 ⟨ b ⟩ d)  = D2 ⟨ incL b ⟩ d {-"~~,"-}
\end{spec}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{spec}
incR : SBinary → SBinary
incR B0            = B1
incR B1            = D1 ⟨ B0 ⟩ D1
incR (d ⟨ b ⟩ D1)  = d ⟨ b ⟩ D2
incR (d ⟨ b ⟩ D2)  = d ⟨ b ⟩ D3
incR (d ⟨ b ⟩ D3)  = d ⟨ incR b ⟩ D2 {-"~~."-}
\end{spec}
\end{minipage}\\
Carrying is invoked when the digit at the end is |D3|.
Applying |incL| to |D3 ⟨ D3 ⟨ B1 ⟩ D1 ⟩ D1|, a ``left-saturated'' representation of $16$, for example,
results in |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1|.
Observe that |incL| does not propagate carry to the right half of the number.
Instead, it reaches the middle of the number and go ``deeper'' by turning a |B1| into a |D1 ⟨ B0 ⟩ D1|.
Meanwhile, decrement is defined by (we show the righthand side variant):
\begin{spec}
decR : SBinary → SBinary
decR B0                      = B0
decR B1                      = B0
decR (D1 ⟨ B0 ⟩ D1)          = B1
decR (D2 ⟨ B0 ⟩ D1)          = D1 ⟨ B0 ⟩ D1
decR (D3 ⟨ B0 ⟩ D1)          = D2 ⟨ B0 ⟩ D1
decR (d ⟨ B1 ⟩ D1)           = d ⟨ B0 ⟩ D2
decR (d ⟨ df ⟨ b ⟩ dr ⟩ D1)  = d ⟨ decR (df ⟨ b ⟩ dr) ⟩ D2
decR (d ⟨ b ⟩ D2)            = d ⟨ b ⟩ D1
decR (d ⟨ b ⟩ D3)            = d ⟨ b ⟩ D2 {-"~~."-}
\end{spec}
Borrowing happens when the rightmost digit is |D1|.
Again, |decR| and |incR| recurse on different cases, thereby achieving amortised $O(1)$ complexity when they are mixed.
Performing |decR (D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1)|, for example,
yields |D2 ⟨ D2 ⟨ B1 ⟩ D2 ⟩ D2| --- we initiate borrowing from the right, and stops when |D1 ⟨ B0 ⟩ D1| in the middle reduces to |B1|.
Applying |incR| to the result yields |D2 ⟨ D2 ⟨ B1 ⟩ D2 ⟩ D3|.

One can imagine how we may support |head| in $O(1)$ time, and |cons|, |tail|, |snoc|, |init| in worst-case $O(\log n)$ and amortised $O(1)$ time.

What about |add| and |append|?
Let |m =| |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1| (decimal $17$) and |n =| |D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1| (decimal $7$), consider computing |add m n|.
We may use increment and decrement to add the smaller number |n| to the bigger one |m|.
But that would be a \emph{one-by-one} algorithm, whose running time would be amortised linear at best.
An ideal \emph{digit-by-digit} algorithm might extract the two outermost digits and recurse, such as:
\begin{spec}
  add (D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1) (D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1) = D2 ⟨ {-"\mbox{...adding $15$ and $6$...~}"-}⟩ D1 {-"~~,"-}
\end{spec}
where the leading |D2| in the result is the leftmost digit of $17$, the rear |D1| is the rightmost digit of $7$, and $15$ and $6$ are respectively $17$ and $7$ with their leftmost/rightmost digits removed.
But $15 + 6$ is an odd number, and in our representation there is no way we can store an odd number in the middle part of an |SBinary|.
One might try borrowing a |1| from |m| or |n|, which will result in mass re-structuring of the number and would not be efficient.
And this problem cannot be solved by adding more digits --- the middle of |SBinary|, beyond depth $1$, still has to be an even number.

Which brings us to how Finger Tree dealt with the problem.

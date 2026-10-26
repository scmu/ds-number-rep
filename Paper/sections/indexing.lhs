\section{Indexing}
\label{sec:indexing}

We return to the lookup problem postponed in Section~\ref{sec:redundant-binary}.
A position |i| counts elements from the front, starting at zero.
For a one-sided binary list, lookup has the interface:
\begin{spec}
  lookup : ∀ {A b} → BList A b → Fin (toN b) → A {-"~~."-}
\end{spec}

\subsection{Lookup in one-sided binary lists}
\label{sec:binary-index}

In a zeroless binary list, a |one| digit holds the element at position |0|.
The pair at position |j| in the tail contributes elements at positions |1 + 2 * j| and |1 + 2 * j + 1| in the whole list.
To look up a later position |i|, we therefore subtract one, divide by two to locate the pair, and use parity to select its first or second element.
A |two| digit works the same way, except that its local positions are |0| and |1|, and later positions use the offset |i - 2|:
\begin{spec}
  lookup (one x ∷ xs) 0 = x
  lookup (one _ ∷ xs) i
    | even (i - 1) = proj₁ (lookup xs ((i - 1) div 2))
    | odd  (i - 1) = proj₂ (lookup xs ((i - 1) div 2))
  lookup (two x y ∷ xs) 0 = x
  lookup (two x y ∷ xs) 1 = y
  lookup (two _ _ ∷ xs) i
    | even (i - 2) = proj₁ (lookup xs ((i - 2) div 2))
    | odd  (i - 2) = proj₂ (lookup xs ((i - 2) div 2)) {-"~~."-}
\end{spec}
If the digit holds |d| elements and the tail holds |m| pairs, the list has |d + 2 * m| positions, so every remaining offset is below |2 * m| and its quotient by two is below |m|.

For example, the list
\begin{spec}
  one a ∷ two (b , c) (d , e) ∷ nil
\end{spec}
represents the sequence |[ a , b , c , d , e ]|.
To look up position |4|, subtract one at the front digit, leaving offset |3|.
The recursive lookup at |3 div 2 = 1| returns the pair |(d , e)| from the tail's |two| digit.
Since |3| is odd, |proj₂| selects |e|. \todo{a graph example?}

This halving of positions is the counterpart of the doubling of element types in Section~2: a tail element has type |A × A|, so it accounts for two consecutive positions at the current level.
Selecting a local element or projecting a pair takes constant time, and each recursive call visits a tail with at most half as many positions.
Thus lookup in a list of size |N| takes $O(\log N)$ time in the worst case.

\label{sec:redundant-index}
For the redundant lists of Section~\ref{sec:redundant-binary}, only the clauses for |three| need to be added.
Its three elements occupy positions |0|, |1|, and |2|; later positions have offset |i - 3| into the paired tail:
\begin{spec}
  lookup (three x y z ∷ xs) 0 = x
  lookup (three x y z ∷ xs) 1 = y
  lookup (three x y z ∷ xs) 2 = z
  lookup (three _ _ _ ∷ xs) i
    | even (i - 3) = proj₁ (lookup xs ((i - 3) div 2))
    | odd  (i - 3) = proj₂ (lookup xs ((i - 3) div 2)) {-"~~."-}
\end{spec}
The same bound calculation applies with |d = 3|, and the worst-case cost remains $O(\log N)$.

\subsection{Lookup in double-ended queues}
\label{sec:symmetric-index}

The symmetric representation of Section~\ref{sec:sym-binary} gives a deque with elements at both ends.
We write |nil| for the empty container, |[ x ]| for a singleton, and |f ⟨ xs ⟩ r| for a deep container with front digit |f|, paired middle |xs|, and rear digit |r|.\todo{placeholder, no constructor in section 3}
For an outer digit |f|, |size f| is its number of elements: |1| for |one|, |2| for |two|, or |3| for |three|.
We also match positions from the rear using |opposite|: within a bound |N|, |opposite i| denotes |N - 1 - i|.
Thus |opposite 0| is the last position, |opposite 1| the position before it, and so on.

At a deep container, let |p = size f| and |q = size r| be the front and rear sizes, and let |N| be the total number of elements at the current level.
The middle then contains |m = (N - p - q) div 2| pairs, with |N = p + 2 * m + q|.
Lookup in a deque retains the form of the one-sided definition:
\begin{spec}
  lookup [ x ] 0 = x
  lookup (one x ⟨ xs ⟩ r) 0 = x
  lookup (two x y ⟨ xs ⟩ r) 0 = x
  lookup (two x y ⟨ xs ⟩ r) 1 = y
  lookup (three x y z ⟨ xs ⟩ r) 0 = x
  lookup (three x y z ⟨ xs ⟩ r) 1 = y
  lookup (three x y z ⟨ xs ⟩ r) 2 = z
  lookup (f ⟨ xs ⟩ one x) (opposite 0) = x
  lookup (f ⟨ xs ⟩ two x y) (opposite 0) = y
  lookup (f ⟨ xs ⟩ two x y) (opposite 1) = x
  lookup (f ⟨ xs ⟩ three x y z) (opposite 0) = z
  lookup (f ⟨ xs ⟩ three x y z) (opposite 1) = y
  lookup (f ⟨ xs ⟩ three x y z) (opposite 2) = x
  lookup (f ⟨ xs ⟩ r) i
    | even (i - p) = proj₁ (lookup xs ((i - p) div 2))
    | odd  (i - p) = proj₂ (lookup xs ((i - p) div 2))
    where p = size f {-"~~."-}
\end{spec}
The front clauses match positions |0| through |p - 1|, and the rear clauses match positions |N - q| through |N - 1|.
Only after both sets of local positions have been excluded does the final clause apply, with |p ≤ i < N - q|.
Subtract the front digit's size to obtain |j = i - p|, look up pair |j div 2|, and select its first or second element according to the parity of |j|.

For example,
\begin{spec}
  one a ⟨ [ (b , c) ] ⟩ two d e
\end{spec}
has |p = 1|, |q = 2|, |N = 5|, and |m = 1|.
Its five positions select |a|, |b|, |c|, |d|, and |e| in that order.
Position |1| is the first middle position: subtracting |p| leaves |0|, so the recursive lookup returns the singleton pair and |proj₁| selects |b|; position |2| selects its second element, |c|.
Position |3 = opposite 1| matches the first element of the rear |two| and returns |d|; position |4 = opposite 0| returns |e|.\todo{a graph example?}

Selection in either outer digit takes constant time.
Let |k = min i (N - 1 - i)| be the number of elements between the selected element and the nearer end.
Each recursive step subtracts the outer digits' sizes and halves the remaining distances to both ends, so lookup takes $O(1 + \log(k + 1))$ time, and hence $O(\log N)$ in the worst case.

\subsection{Lookup in Finger Tree}
\todo{finger tree lookup}

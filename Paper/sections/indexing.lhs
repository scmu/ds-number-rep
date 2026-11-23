\section{Indexing}
\label{sec:indexing}

We return to the lookup problem postponed in Section~\ref{sec:redundant-binary}.
A position |i| counts elements from the front, starting at zero.
Writing |toN b| for the number denoted by a numeral |b|, lookup in a one-sided binary list has the interface:
\begin{spec}
  lookup : ∀ {A b} → BList A b → Fin (toN b) → A {-"~~."-}
\end{spec}
In the pseudocode below, clauses are tried in order, |div| denotes integer division, and the proofs that positions stay within bounds are left implicit.
We assume that arithmetic on positions takes constant time.

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
Since |3| is odd, |proj₂| selects |e|.

Selecting a local element or projecting a pair takes constant time, and each recursive call visits a tail with at most half as many positions.
Thus lookup in a list of size |N| takes $O(\log N)$ time in the worst case.

\subsection{Lookup in redundant binary lists}
\label{sec:redundant-index}

For the redundant lists of Section~\ref{sec:redundant-binary}, only the clauses for |three| need to be added.
A |three| digit holds the elements at positions |0|, |1|, and |2|, and later positions have offset |i - 3| into the paired tail:
\begin{spec}
  lookup (three x y z ∷ xs) 0 = x
  lookup (three x y z ∷ xs) 1 = y
  lookup (three x y z ∷ xs) 2 = z
  lookup (three _ _ _ ∷ xs) i
    | even (i - 3) = proj₁ (lookup xs ((i - 3) div 2))
    | odd  (i - 3) = proj₂ (lookup xs ((i - 3) div 2)) {-"~~."-}
\end{spec}
The same bound calculation applies with |d = 3|, and the worst-case cost remains $O(\log N)$.
Redundancy allows the same sequence to be grouped in different ways; lookup simply follows the grouping of the given list.

\subsection{Lookup in double-ended queues}
\label{sec:symmetric-index}

The container induced by the symmetric representation of Section~\ref{sec:sym-binary} mirrors the three constructors of |SBinary|:
it is either empty (|nil|), a singleton (|[ x ]|), or |f ⟨ xs ⟩ r|, with front digit |f|, rear digit |r|, and a middle |xs| of pairs.
For a digit |f|, let |size f| be its number of elements: |1|, |2|, or |3|.
To match positions counted from the rear, we write |opposite k| for position |N - 1 - k|, where |N| is the number of elements in the container.

Lookup retains the form of the one-sided definition.
Let |p = size f| and |q = size r|.
The front clauses below match positions |0| through |p - 1|, and the rear clauses match positions |N - q| through |N - 1|:
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
The final clause applies only when |p ≤ i < N - q|, that is, when |i| falls in the middle, which holds |(N - p - q) div 2| pairs.
As before, we subtract the front digit's size to obtain |j = i - p|, look up pair |j div 2|, and select an element by the parity of |j|.

For example, |one a ⟨ [ (b , c) ] ⟩ two d e| has |p = 1|, |q = 2|, and |N = 5|.
Position |0| selects |a| from the front digit.
Position |1| is the first middle position: subtracting |p| leaves |0|, so the recursive lookup returns the pair |(b , c)| and |proj₁| selects |b|; position |2| similarly selects |c|.
Position |3 = opposite 1| returns |d| from the rear digit, and position |4 = opposite 0| returns |e|.

Selection in either outer digit takes constant time, and each recursive call visits a middle with at most half as many positions.
As in the one-sided case, lookup takes $O(\log N)$ time in the worst case.

\subsection{Lookup in finger trees}
\label{sec:finger-index}

In the containers above, the tail or middle stores pairs, so lookup locates a pair by halving the offset and selects within it by parity.
In a finger tree, the components have varying sizes: a |Tree A n f| holds |sizeS f| elements, as determined by its fraction |f|.
Halving and parity are therefore replaced by comparisons against these sizes.
We extend |size| to trees, digits, and finger trees, counting elements of type |A|; thus |size t = sizeS f| for |t : Tree A n f|.
Within a tree, lookup descends into the child whose range contains the position:
\begin{spec}
  lookupT : ∀ {A n f} → Tree A n f → Fin (sizeS f) → A
  lookupT (leaf x) 0 = x
  lookupT (node2 t u) i
    | i < size t           = lookupT t i
    | otherwise            = lookupT u (i - size t)
  lookupT (node3 t u v) i
    | i < size t           = lookupT t i
    | i < size t + size u  = lookupT u (i - size t)
    | otherwise            = lookupT v (i - size t - size u) {-"~~."-}
\end{spec}
A function |lookupS : ∀ {A n d} → Some A n d → Fin (sizeD d) → A| selects a tree within a digit in the same way and continues with |lookupT|.
Along the spine, the position is compared against the sizes of the front digit and the middle:
\begin{spec}
  lookup : ∀ {A n b} → FingerTree A n b → Fin (sizeB b) → A
  lookup [ t ] i = lookupT t i
  lookup (xf ⟨ xs ⟩ xr) i
    | i < size xf            = lookupS xf i
    | i < size xf + size xs  = lookup xs (i - size xf)
    | otherwise              = lookupS xr (i - size xf - size xs) {-"~~."-}
\end{spec}
Unlike the earlier definitions, the offset into the middle is not halved: the middle holds deeper trees, and its positions still count elements of type |A|.

Computing a size such as |sizeS f| by traversing the fraction |f| takes time linear in the number of elements.
We therefore assume that sizes are available in constant time, for instance by caching the size in every tree node and at every level of the spine, as in the random-access sequences of \citet{HinzePaterson:06:Finger}.
Each step along the spine or down a tree then takes constant time.
A tree at depth |n| holds at least $2^n$ elements, so both the spine and the selected tree have depth $O(\log N)$, and lookup takes $O(\log N)$ time in the worst case.

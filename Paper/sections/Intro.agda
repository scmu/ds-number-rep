
\section{Introduction}

Every introductory course to functional programming should mention that |List|s are closely related to the unary representation of natural numbers, |ℕ|.
Recall their definitions:\\
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data ℕ : Set where
    Zero  : ℕ
    Suc   : ℕ → ℕ {-"~~,"-}
\end{code}
\end{minipage}
\begin{minipage}[t]{0.45\textwidth}
\begin{code}
  data List (a : Set) : Set where
    Nil   : List a
    Cons  : a → List a → List a {-"~~."-}
\end{code}
\end{minipage}\\
The type |List a| is obtained by ornamenting the |Suc| constructor of |ℕ| with a value of type |a|;
by traversing a list, removing the |a| and replacing |Nil| and |Cons| respectively by |Zero| and |Suc|, we get an |ℕ| back, which is also the length of the list.
Many operations on lists have their natural-number counterparts: |tail| is decrementing by one, and list |append| is addition.
By indexing lists by unary natural numbers, we get the type |Vec| --- length-constrained lists, whose |append| operation has only one ``reasonable'' definition enforced by its type.

This correspondence extends to other representations of natural numbers.
As noted by \citet{Okasaki:99:Purely}, data structures resembling numerical representations are surprisingly common, but the connection is not often made explicit.
Okasaki devoted an entire chapter to such data structures and presented several implementations of one-sided random-access lists, based on several representations of binary numbers, that support |cons|, |head|, and |tail| in $O(1)$ worst-case time, and |lookup| in $O(\log n)$ worst-case time.
\citet{KaplanTarjan:99:Purely} presented a deque with concatenation, inspired by a redundant binary representation of numbers. \todo{say more}

The Finger Tree \cite{HinzePaterson:06:Finger} is a very versatile data structure for sequences, supporting \todo{review Finger Tree and its supposed connection to numbers}
``If we trieify a suitable index type based
on this number system, we obtain so-called finger trees. But that’s a story
to be told elsewhere.''

In this article, \todo{what we will cover}

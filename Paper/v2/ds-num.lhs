%% lhs2TeX --agda ds-num.lhs | pdflatex --jobname=ds-num

\documentclass[pearl,fleqn,review]{jfp-epi}

%include preamble.tex

\begin{document}

\author{Wen-Yuan Chan}
\affiliation{
  \institution{National Taiwan University}
  % \department{Computer Science and Information Engineering}
  % \streetaddress{128 Academia Road}
  % \city{Taipei}
  \country{Taiwan}
  % \postcode{115201}
}
\author{Shin-Cheng Mu}
\affiliation{
  \institution{Academia Sinica}
  % \department{Institute of Information Science}
  % \streetaddress{128 Academia Road}
  % \city{Taipei}
  \country{Taiwan}
  % \postcode{115201}
}


\title{From Numerical Representations to Sequences and Finger Trees}

\begin{abstract}
Many container data structures bear close resemblance to some numerical representation of its size. Operations on these data structure can often be derived from corresponding operations on the numbers, and properties of the former can be established by reasoning about the latter.
We present some recipes for designing numerical representations and deriving  corresponding sequence-like data structures that efficiently support operations including adding and removing elements from both ends, indexing, and sequence concatenation.
It turns out that Finger Trees, a versatile data structure for sequences, can be understood as a representation of binary number whose digits are allowed to be fractional.
\end{abstract}

\maketitle

\section{Introduction}
\label{sec:intro}

Every introductory course to functional programming should mention that |List|s are closely related to |ℕ|, the unary representation of natural numbers.
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
To manifest its connection with lists, in this pearl we present binary numbers least-significant digit first.
For example, |D1 ∷ D0 ∷ D1 ∷ D1 ∷ B0| denotes $1 \times 2^0 + 0 \times 2^1 + 1 \times 2^2 + 1 \times 2^3 =$ $1 + 4 + 8 = 13$.
One may already have noticed a potential problem: both |D1 ∷ D1 ∷ B0| and |D1 ∷ D1 ∷ D0 ∷ B0| denote $4$.
We may ensure that our operations do not generate trailing zeros, or enforce so using some clever design in the datatype, but we will keep it simple for now, before moving on to another representation.

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

Incrementing a |Binary| and |cons|ing to a |BList| are respectively defined by:\\
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
cons x (one y ∷ xs)  = zero   ∷ cons (x , y) xs {-"~~."-}
\end{code}
\end{minipage}\\
The definition of |cons| mirrors that of |inc|.
Notice how the carrying in |inc| corresponds to consing |(x,y)| to the tail of the list.
In fact, when coding up |cons| in Agda, guided by |inc| in its type, the programmer is often left with only one reasonable way to fill in each of the right hand side.

One problem with |BList| is that |head| is no longer $O(1)$.
The easy case |head (one x ∷ xs)| yields |x| immediately,
but when encountering |head (zero ∷ xs)|, we have to look into |xs| to find the leftmost element, which may turn out to start with |zero| as well!
It appears that the presence of |D0| has been causing various issues.
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
With this representation we resolved two problems at once: no more trailing zeros, and |head| always sees an element in the first position!

Consider how increment and decrement are defined:\\
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
Increment flips a |D1| to |D2| without carry, and wraps a |D2| to |D1| while carrying to the next position.
Decrement does the reverse.
Note that when decrementing |D1 ∷ n|, we borrow a $1$ from |n|, and the least significant digit becomes |D2|.

Let $n$ be the number represented by some |Binary|.
While |inc| is now $O(\log n)$ worst-case,
in repeated applications of |inc|, each call has amortised time complexity $O(1)$.
\todo{explain in one sentence}
For the same reason the time complexity of |dec| is also $O(\log n)$ worst-case and $O(1)$ amortised.
If we mix |inc| and |dec|, however, we lost the amortised $O(1)$ behaviour --- \todo{explain in one sentence}.

\subsection{Redundant binary representation}

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
The worst-case cost of a single |inc| or |dec| remains $O(\log n)$, while the amortised cost for consecutive calls to |inc| and |dec| are $O(1)$.
The crucial difference emerges under mixed sequences of |inc| and |dec|: after a carry resets a |D3| to |D2|, a subsequent |dec| at that position merely decreases |D2| to |D1| without triggering a borrow.
Symmetrically, after a borrow resets a |D1| to |D2|, a subsequent |inc| increases |D2| to |D3| without carrying.
The extra room in the digit range $\{1, 2, 3\}$ thus acts as a buffer that prevents carries and borrows from cascading in alternation, ensuring that the amortised cost per operation remains $O(1)$ even when |inc| and |dec| are interleaved arbitrarily.
\todo{simplify the explanation done by Chris Okasaki}

Consider the random-access list induced by |Binary|.
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

\todo{We shall talk about indexing now, but this section is a place holder. To be rewritten.}
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

\paragraph{Summary}
With the redundant binary representation we induced a list that offers $O(1)$ |head|,
worst-case $O(\log n)$ and amortised $O(1)$ |cons| and |tail|,
$O(\log n)$ |lookup|, and amortised $O(n)$ |append|.
Asymptote-wise, it appears to be a good improvement over the simple built-in list implemented as left-biased linked-lists,
provided that you only add to and remove from one end of the list, and perform indexing more than |append|.
What, then, if we wish to add to and remove from both ends, or if we want a faster append?

\section{Symmetric representation}



\section{Fractional digits}

\section{Conclusions}

\cite{Claessen:20:Finger}
\cite{HinzeSwierstra:22:Calculating}

\bibliographystyle{ACM-Reference-Format}
\bibliography{ds-num}
\end{document}

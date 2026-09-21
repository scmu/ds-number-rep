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


\title{Finger Trees Have Fractional Sizes}

\begin{abstract}
Many container data structures bear close resemblance to some numerical representation of its size. Operations on these data structure can often be derived from corresponding operations on the numbers, and properties of the former can be established by reasoning about the latter.
We present some recipes for designing numerical representations and deriving  corresponding sequence-like data structures that efficiently support operations including adding and removing elements from both ends, indexing, and sequence concatenation.
It turns out that Finger Trees, a versatile data structure for sequences, can be understood as a representation of binary number whose digits are allowed to be fractional.
\end{abstract}

\maketitle

\section{Introduction}
\label{sec:intro}

Every introductory course to functional programming should mention that (cons)-lists are closely related to the unary representation of natural numbers.
Recall their definitions:\\[-0.8\baselineskip]
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
\end{minipage}
\\
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
tail (one x ∷ xs@(_ ∷ _))  =  let  (y , z) = head xs (∷-nonzero xs)
                              in   two y z ∷ tail xs
tail (two x y ∷ xs)        =  one y ∷ xs
tail (three x y z ∷ xs)    =  two y z ∷ xs {-"~~."-}
\end{code}
In the third case of |dec| we borrow a bit from the tail, while in the corresponding case of |tail| we makes a call to |head| in order to extract one element from the tail |xs|.
The function |head| takes a proof promising that the given list is not empty:
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
What if we want a faster append?

\subsection{Indices as binary numbers}
\label{sec:binary-index}

Just as |Fin n| --- the type of naturals below |n|, with |iz : Fin (inc n)| and |is : Fin n → Fin (inc n)| mirroring |zero| and |suc| --- indexes a length-|n| vector, |Idx n| will index a |RAL A n|.
Our claim is that |Idx| is itself a number system: where |Fin| gives a \emph{unary} account of the naturals below a bound, |Idx| gives a \emph{binary} one, laid out along digits of |n|.
We make the correspondence exact with a pair of conversions between |Idx n| and |Fin (toN n)|.

Consider first the zeroless representation.
An index selects a position within one digit and, if the element it seeks lives further in, descends into the doubled tail.
A |D1| digit stores one element and has two subtrees, giving one base position |ez1| and two recursive branches |_cA1|, |_cB1|; a |D2| digit stores two elements, giving base positions |ez2|, |eo2| and branches |_cA2|, |_cB2|:
\begin{code}
  data Idx : Binary → Set where
    ez1   : ∀ {n} →          Idx (D1 ∷ n)
    _cA1  : ∀ {n} → Idx n →  Idx (D1 ∷ n)
    _cB1  : ∀ {n} → Idx n →  Idx (D1 ∷ n)
    ez2   : ∀ {n} →          Idx (D2 ∷ n)
    eo2   : ∀ {n} →          Idx (D2 ∷ n)
    _cA2  : ∀ {n} → Idx n →  Idx (D2 ∷ n)
    _cB2  : ∀ {n} → Idx n →  Idx (D2 ∷ n) {-"~~."-}
\end{code}
Counting the constructors of a digit recovers its weight: |D1| contributes |1| base position plus |2| branches into the tail, and |D2| contributes |2| plus |2|.
The function |lookup| follows an index through the list in lockstep, projecting from the paired-up elements as it recurses:
\begin{code}
  lookup : ∀ {A n} → RAL A n → Idx n → A
  lookup (one x    ∷ xs)  ez1      = x
  lookup (one x    ∷ xs)  (i cA1)  = proj₁ (lookup xs i)
  lookup (one x    ∷ xs)  (i cB1)  = proj₂ (lookup xs i)
  lookup (two x y  ∷ xs)  ez2      = x
  lookup (two x y  ∷ xs)  eo2      = y
  lookup (two x y  ∷ xs)  (i cA2)  = proj₁ (lookup xs i)
  lookup (two x y  ∷ xs)  (i cB2)  = proj₂ (lookup xs i) {-"~~."-}
\end{code}

To pin down that |Idx n| enumerates the naturals below |toN n|, we convert to |Fin (toN n)|.
Following \citet{HinzeSwierstra:22:Calculating}, reading an index outward as a binary numeral yields |toF : Idx n → Fin (toN n)|, doubling the tail contribution at each digit with |_dblO| and |_dblI|.

The inverse direction is more interesting.
Given a position in |Fin (toN n)|, we peel off the current digit by halving with |_halfF|, which splits a doubled range into a tail position and a remainder:
\begin{code}
  _halfF : ∀ {n} → Fin (2 * n) → (Fin n × Fin 2)
  iz           halfF = iz  , iz
  is iz        halfF = iz  , is iz
  is (is i)    with i halfF
  ... | q , r  = is q , r {-"~~,"-}

  fromF : ∀ {n} → Fin (toN n) → Idx n
  fromF {D1 ∷ n} iz           = ez1
  fromF {D1 ∷ n} (is i)       with i halfF
  ... | j , iz    = (fromF j) cA1
  ... | j , is iz = (fromF j) cB1
  fromF {D2 ∷ n} iz           = ez2
  fromF {D2 ∷ n} (is iz)      = eo2
  fromF {D2 ∷ n} (is (is i))  with i halfF
  ... | j , iz    = (fromF j) cA2
  ... | j , is iz = (fromF j) cB2 {-"~~."-}
\end{code}
Each |with| clause is one digit of binary long division: |_halfF| tells us whether the position falls on the left or right subtree, or on one of the elements stored locally, and |fromF| recurses on the quotient.
Together with |toF|, this exhibits |Idx n| as just another notation for |Fin (toN n)| --- a binary numeral for the same finite range that |Fin| writes in unary.

Because |Idx| is a number system, it carries its own arithmetic.
The zero index |izero| points at the element |cons| has just placed at the front, and |isucc| is the successor on positions:
\begin{code}
  izero : ∀ {n} → Idx (inc n)
  izero {B0}      = ez1
  izero {D1 ∷ n}  = ez2
  izero {D2 ∷ n}  = ez1 {-"~~,"-}

  isucc : ∀ {n} → Idx n → Idx (inc n)
  isucc ez1      = eo2
  isucc (i cA1)  = i cA2
  isucc (i cB1)  = i cB2
  isucc ez2      = izero cA1
  isucc eo2      = izero cB1
  isucc (i cA2)  = (isucc i) cA1
  isucc (i cB2)  = (isucc i) cB1 {-"~~."-}
\end{code}
The last two clauses are the carry: incrementing a position that has run off the end of a |D2| digit forces a successor \emph{one digit up}, exactly as |inc| carries.
These connect to the container through the specification of a one-sided flexible array \citep{HinzeSwierstra:22:Calculating}:
\begin{spec}
  lookup-izero  : ∀ {A n} (x : A) (xs : RAL A n)
                → lookup (cons x xs) izero ≡ x
  lookup-isucc  : ∀ {A n} (x : A) (xs : RAL A n) (i : Idx n)
                → lookup (cons x xs) (isucc i) ≡ lookup xs i
  lookup-head   : ∀ {A n} (xs : RAL A (inc n))
                → head xs ≡ lookup xs izero
  lookup-tail   : ∀ {A n} (xs : RAL A (inc n)) (i : Idx n)
                → lookup (tail xs) i ≡ lookup xs (isucc i) {-"~~."-}
\end{spec}
With the zeroless |tail : RAL A (inc n) → RAL A n|, dropping the head is mirrored on indices by |isucc|.

Moving to the redundant representation of Section~\ref{sec:redundant-binary} changes nothing structural.
We added a digit to the number, so we add constructors to the index; the recipe is unchanged.
A |D3| digit stores three elements and keeps its two subtrees, contributing three base positions |ez3|, |eo3|, |et3| and two branches |_cA3|, |_cB3|:
\begin{code}
    ez3   : ∀ {n} →          Idx (D3 ∷ n)
    eo3   : ∀ {n} →          Idx (D3 ∷ n)
    et3   : ∀ {n} →          Idx (D3 ∷ n)
    _cA3  : ∀ {n} → Idx n →  Idx (D3 ∷ n)
    _cB3  : ∀ {n} → Idx n →  Idx (D3 ∷ n) {-"~~."-}
\end{code}
The clauses of |fromF| and |isucc| for |D3| are filled in by the same pattern; the carry in |isucc| again threads through |izero| on the tail, just as it did for |D2|:
\begin{spec}
  isucc eo3      = izero cA2
  isucc et3      = izero cB2
  isucc (i cA3)  = (isucc i) cA2
  isucc (i cB3)  = (isucc i) cB2 {-"~~."-}
\end{spec}

In Section~\ref{sec:redundant-binary} the redundant |tail| takes a |RAL A n| to a |RAL A (dec n)|, so an index for the shortened list lives in |Idx (dec n)|.
To state how |lookup| behaves under |tail| we must send such an index back into the original number, which is the role of |ishift|:
\begin{spec}
  ishift : ∀ {n} → Idx (dec n) → Idx n
  ishift {D2 ∷ n}  ez1      = eo2
  ishift {D2 ∷ n}  (i cA1)  = i cA2
  ishift {D2 ∷ n}  (i cB1)  = i cB2 {-"~~."-}
\end{spec}
On a digit that has spare room, |ishift| merely relabels a position one digit up.
The interesting clauses are those where |dec| borrowed from the tail (the case |D1 ∷ d ∷ n|): there |ishift| reaches inside with |izero| on the now-nonempty tail, the mirror image of the borrow.
With |ishift| in hand the tail law now phrased with |dec| rather than |inc|:
\begin{spec}
  lookup-tail : ∀ {A n} (xs : RAL A n) (i : Idx (dec n))
              → lookup (tail xs) i ≡ lookup xs (ishift i) {-"~~."-}
\end{spec}

The move that took us from unary lists to binary numbers for \emph{sizes} thus also yields binary numbers for \emph{positions}: |Idx| is the ornament of |Binary| in the index direction, just as |RAL| is its ornament in the data direction, both cut to the same digits.

\section{Symmetric representation}

%format df = "{\Var d}_{f}"
%format dr = "{\Var d}_{r}"
For many reasons we want to investigate double-ended queues (deques), by which we mean list-like data structures that allows quick access to both of its ends.
This property might allow an efficient |append|, and the deque is useful data structure in itself.

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
For example, both |D3 ⟨ D3 ⟨ B1 ⟩ D1 ⟩ D1| and |D3 ⟨ D3 ⟨ B0 ⟩ D2 ⟩ D3| represent |16|.

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
Applying |incL| to |D3 ⟨ D3 ⟨ B1 ⟩ D1 ⟩ D1|, a ``left-saturated'' representation of |16|, for example,
results in |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1|.
Observe that carrying does not propagate to the right half of the number.
Instead, |incL| reaches the middle of the number and go ``deeper'' by turning a |B1| into a |D1 ⟨ B0 ⟩ D1|.
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

One can imagine how we may support |head| in $O(1)$ , and |cons|, |tail|, |snoc|, |init| in worst-case $O(\log n)$ and amortised $O(1)$ time.

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
And this problem cannot be solved by adding more digits --- with more digits we still cannot store an odd number in the middle of |SBinary|.

Which brings us to how the Finger Tree dealt with the problem.

\section{Fractional digits}

What if we allow mixed fractions in digits?

In decimal representation, for example, the digits are integers in $\{0..9\}$, and $987$ denotes $9 \times 10^2 + 8 \times 10 + 7$.
In a decimal number $d_2 d_1 d_0$, the value contained by the $d_2 d_1$ part is always a multiple of $10$.
But if we allow a mixed faction, say $8\frac{3}{10}$, to be a digit, the same number $987$ could be written $9\,8\frac{3}{10}\,4$, denoting $9 \times 10^2 + 8\frac{3}{10} \times 10 + 4$ --- the two most significant digits now represent $983$!
Pushing it a bit further, $9\frac{21}{100}\, 6\frac{3}{10}\,3$ is yet another representation of $987$.

Our view is that Finger Trees arise from allowing mixed fractional digits in a zeroless, redundant representation of binary numbers.
Consider again |m = | $17 =$  |D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1 ⟩ D1|.
Let |k = D2 ⟨ B0 ⟩ D1| (decimal $3$).
The result of |add m k| could be
\begin{spec}
   D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D2{-"\!\frac{1}{2}"-} ⟩ D1 {-"~~."-}
\end{spec}
Let |n = | $7 =$ |D2 ⟨ D1 ⟨ B0 ⟩ D1 ⟩ D1|. The result of |add m n| is
\begin{spec}
 D2 ⟨ D2 ⟨ D1 ⟨ B0 ⟩ D2{-"(\frac{1}{4}+\frac{1}{2})"-} ⟩ D1 ⟩ D1 {-"~~."-}
\end{spec}

\subsection{Fractional digits}

What is a fractional digit?
The intuition above suggests that a digit should be allowed to carry a value that, while not an integer on its own, contributes an integer when multiplied by its positional weight.
In a symmetric binary number, the digits surrounding the middle at depth |n| have weight $2^n$.
We therefore let a digit at depth |n| carry a \emph{fraction} whose denominator is $2^n$:
\begin{code}
  data Frac : ℕ → Set where
    one        : Frac 0
    [_+_]/2    : ∀ {n} → Frac n → Frac n → Frac (suc n)
    [_+_+_]/2  : ∀ {n} → Frac n → Frac n → Frac n → Frac (suc n) {-"~~."-}
\end{code}
A |Frac n| is a non-empty tree whose internal nodes have two or three children and whose every leaf sits at depth |n|.
The constructors record how a fraction is built: |one| is the whole $1$, while |[ f + g ]/2| and |[ f + g + h ]/2| average the (equal-depth) fractions they contain, halving the denominator's exponent by one at each level.
Counting the leaves gives the numerator:
\begin{code}
  sizeF : ∀ {n} → Frac n → ℕ
  sizeF one              = 1
  sizeF [ f + g ]/2      = sizeF f + sizeF g
  sizeF [ f + g + h ]/2  = sizeF f + (sizeF g + sizeF h) {-"~~."-}
\end{code}
A fraction |f : Frac n| denotes the dyadic rational $\mathit{sizeF}\;f / 2^{n}$.
For example, |one : Frac 0| denotes $1/2^0 = 1$; |[ one + one ]/2 : Frac 1| denotes $2/2^1 = 1$; and |[ one + one + one ]/2 : Frac 1| denotes $3/2^1 = 1\frac12$ --- a genuinely fractional digit.
At depth |n|, where the positional weight is $2^n$, such a digit contributes exactly $\mathit{sizeF}\;f$ to the represented number.

\subsection{The symmetric fractional binary}

We now decorate each digit of the symmetric, zeroless, redundant representation of Section~\ref{sec:redundant-binary} with a fraction of the appropriate depth\todo{elaborate on Digit}:
\begin{code}
  data Digit : ℕ → Set where
    D1 : ∀ {n} → Frac n                    → Digit n
    D2 : ∀ {n} → Frac n → Frac n           → Digit n
    D3 : ∀ {n} → Frac n → Frac n → Frac n  → Digit n {-"~~,"-}
  data Binary : ℕ → Set where
    B0     : ∀ {n} → Binary n
    B1     : ∀ {n} → Frac n → Binary n
    _⟨_⟩_  : ∀ {n} → Digit n → Binary (suc n) → Digit n → Binary n {-"~~."-}
\end{code}
The depth index increases by one as we descend towards the middle, mirroring the doubling of weights.
A number is a |Binary 0|.
Its value is obtained by summing the fractional contributions:
\begin{code}
  sizeB : ∀ {n} → Binary n → ℕ
  sizeB B0            = 0
  sizeB (B1 f)        = sizeF f
  sizeB (df ⟨ b ⟩ dr) = sizeD df + (sizeB b + sizeD dr) {-"~~,"-}

  toN : Binary 0 → ℕ
  toN = sizeB {-"~~,"-}
\end{code}
where |sizeD| sums the fractions of a digit.
Adding an element amounts to carrying a fraction inward.
More generally than incrementing, |addFL| adds an arbitrary fraction |f| at the left end:
\begin{code}
  addFL : ∀ {n} → Frac n → Binary n → Binary n
  addFL f B0                  = B1 f
  addFL f (B1 g)              = D1 f ⟨ B0 ⟩ D1 g
  addFL f (D1 g ⟨ b ⟩ dr)     = D2 f g ⟨ b ⟩ dr
  addFL f (D2 g h ⟨ b ⟩ dr)   = D3 f g h ⟨ b ⟩ dr
  addFL f (D3 g h i ⟨ b ⟩ dr) = D2 f g ⟨ addFL [ h + i ]/2 b ⟩ dr {-"~~."-}
\end{code}
The last case is the crucial part.
When the leftmost digit is saturated (|D3 g h i|), we keep |D2 f g|, pair up the overflowing |h| and |i| into the single next-depth fraction |[ h + i ]/2|, and carry \emph{that} inward with a recursive |addFL|.
Adding a fraction at the right end, |addFR|, is defined symmetrically.
The ordinary increments are now simply the addition of the whole unit |one| at either end:
\begin{code}
  incL : Binary 0 → Binary 0
  incL b = addFL one b {-"~~,"-}

  incR : Binary 0 → Binary 0
  incR b = addFR one b {-"~~."-}
\end{code}
Decrement is subtler, because a leading |D1| has nothing to spare. To borrow, we must reach inward and split a next-depth fraction back into two --- the exact mirror of the |D3| carry in |addFL|.
Removing an element from the left is |decL|:
\begin{code}
  decL : ∀ {n} → Binary n → Binary n
  decL B0                            = B0
  decL (B1 f)                        = B0
  decL (D2 f g ⟨ b ⟩ dr)             = D1 g ⟨ b ⟩ dr
  decL (D3 f g h ⟨ b ⟩ dr)           = D2 g h ⟨ b ⟩ dr
  decL (D1 f ⟨ B0 ⟩ D1 g)            = B1 g
  decL (D1 f ⟨ B1 [ g + h ]/2 ⟩ dr)  = D2 g h ⟨ B0 ⟩ dr
  decL (D1 f ⟨ m@(D1 [ g + h ]/2 ⟨ b ⟩ dr') ⟩ dr) = D2 g h ⟨ decL m ⟩ dr {-"~~,"-}
\end{code}
with the remaining cases analogous; the right-end |decR| is symmetric and omitted.
These operations respect the semantics at every depth: |addFL f| adds a whole tree of |sizeF f| elements, and |decL| removes the leftmost such tree.
\begin{code}
  addFL-correct : ∀ {n} (f : Frac n) (b : Binary n)
                → sizeB (addFL f b) ≡ sizeF f + sizeB b {-"~~."-}
\end{code}
The genuine increment and decrement are the special case at depth |0|, where |one| --- and hence the leftmost tree --- is a single leaf of size |1|.
They therefore change the element count by exactly one:
\begin{code}
  incL-correct : ∀ (b : Binary 0) → toN (incL b) ≡ suc (toN b) {-"~~,"-}
  decL-correct : ∀ (b : Binary 0) → toN (decL b) ≡ pred (toN b) {-"~~."-}
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

\subsection{Indexing}
\todo{FingerTree indexing}

\section{Conclusions}

\cite{Claessen:20:Finger}
\cite{HinzeSwierstra:22:Calculating}

\bibliographystyle{ACM-Reference-Format}
\bibliography{ds-num}
\end{document}

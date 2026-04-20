
%% lhs2TeX --agda ds-num.lhs | pdflatex --jobname=ds-num

\documentclass[pearl,fleqn,review]{jfp-epi}

%\usepackage[capitalise,noabbrev]{cleveref}
\citestyle{acmauthoryear}

\usepackage{mathtools}
\usepackage{pifont}

\usepackage{mdframed}
\newenvironment{temp}{\begin{mdframed}[backgroundcolor=red!7, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]\setlength{\abovedisplayskip}{0ex}\raisebox{-\height-3pt}[0pt][0pt]{\hspace{.965\textwidth}\color{red}\huge\ding{56}}}{\end{mdframed}}

\usepackage{wrapfig}
\usepackage{xifthen}

\usepackage[inline]{enumitem} % for environment enumerate*
\newlist{inlineenum}{enumerate*}{1}
\setlist[inlineenum]{label=(\arabic*)}

\DeclareMathAlphabet{\mathsf}{OT1}{cmss}{m}{n}
\DeclareMathAlphabet{\mathsfb}{OT1}{cmss}{bx}{n}

\newcommand{\todo}[1]{{\color{orange}(TODO: #1)}}
\newcommand{\todonote}[1]{\footnote{\color{blue}Shin: #1}}

\newenvironment{aha}{\medskip}{\unskip\medskip} % for one-line paragraphs
\makeatletter
\newcommand{\pause}{\medskip\centerline{$\ast\quad\ast\quad\ast$}\medskip\@@afterindentfalse\@@afterheading} % for a mid-section pause
\newcommand{\bigpause}{\medskip\centerline{$\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast$}\medskip\@@afterindentfalse\@@afterheading} % to set off the Afterword
\makeatother

\newcommand{\csp}{\hspace{.5em minus .1em}}
\newcommand{\equals}{\enskip=\enskip}


\let\Bbbk\relax
%include agda.fmt
%include agdaMacros.fmt

\begin{document}

\setlength{\mathindent}{2\parindent}

\author{Wen-Yuan Chan}
\affiliation{
  \institution{National Taiwan University}
  % \department{Computer Science and Information Engineering}
  % \streetaddress{128 Academia Road}
  % \city{Taipei}
  % \country{Taiwan}
  % \postcode{115201}
}
\author{Shin-Cheng Mu}
\affiliation{
  \institution{Academia Sinica}
  % \department{Institute of Information Science}
  % \streetaddress{128 Academia Road}
  % \city{Taipei}
  % \country{Taiwan}
  % \postcode{115201}
}


\title{From Numerical Representations to Sequences and Finger Trees}

\begin{abstract}
Many container data structures bear close resemblance to some numerical representation of its size. Operations on these data structure can often be derived from corresponding operations on the numbers, and properties of the former can be established by reasoning about the latter.
We present some recipes for designing numerical representations and deriving  corresponding sequence-like data structures that efficiently support operations including adding and removing elements from both ends, indexing, and sequence concatenation.
It turns out that Finger Trees, a versatile data structure for sequences, can be understood as a representation of binary number whose digits are allowed to be fractional.
\end{abstract}


\maketitle

\section{} % why doesn't this show up?

\section{Introduction}

Every introductory course to functional programming should mention that |List|s are closely related to the unary representation of natural numbers.
Recall their definitions:
\begin{code}
  data Nat : Set where
    Zero  : Nat
    Suc   : Nat → Nat {-"~~,"-}
  data List (a : Set) : Set where
    Nil   : List a
    Cons  : a → List a → List a {-"~~."-}
\end{code}
The |List| datatype is obtained by ornamenting the |Suc| constructor with a value.
Many operations on lists have their natural-number counterparts: |tail| is decrementing by one, and list |append| is addition.
By indexing lists by unary natural numbers, we get the type |Vec| --- length-constrained lists, whose |append| operation has only one ``reasonable'' definition enforced by its type.

This correspondence extend to other representations of natural numbers.
As noted by \citet{Okasaki:99:Purely}, data structures resembling numerical representations are surprisingly common, but the connection is not often made explicit.
Okasaki devoted an entire chapter to such data structures and presented several implementations of one-sided random-access lists, based several representations of binary numbers, that support |cons|, |head|, and |tail| in $O(1)$ worst-case time, and |lookup| in $O(\log n)$ worst-case time.
\citet{KaplanTarjan:99:Purely} presented a deque with concatenation, inspired by a redundant binary representation of numbers. \todo{say more}

The Finger Tree \cite{HinzePaterson:06:Finger} is a very versatile data structure for sequences, supporting \todo{review Finger Tree and its supposed connection to numbers}
``If we trieify a suitable index type based
on this number system, we obtain so-called finger trees. But that’s a story
to be told elsewhere.''

In this article, \todo{what we will cover}

\section{Lists, Unary, and Binary Numbers}

Following \citet{HinzeSwierstra:22:Calculating}, we adopt a uniform framework in which every number system is defined by a type of \emph{digits}, a recursive number type built from those digits, and a \emph{semantic function} |toN| mapping numbers to their natural-number value.
Operations such as increment and decrement are defined on the number type, and their correctness is established by showing that they commute with~|toN|.
Data structures are then obtained by \emph{indexing} a container type by the number type: each digit is ornamented with data, and structural operations on the container mirror arithmetic operations on the index.

\subsection{Unary Numbers}

The simplest instance of this framework uses a single digit.
A unary natural number is either zero or a digit prepended to a smaller number:
\begin{code}
  data Digit : Set where
    D1 : Digit {-"~~,"-}
  data Nat : Set where
    N0    : Nat
    _⟨_⟩  : Digit → Nat → Nat {-"~~."-}
\end{code}
The semantic function sums the digit values along the spine:
\begin{code}
  toN : Nat → ℕ
  toN N0        = 0
  toN (d ⟨ n ⟩)  = DtoN d + toN n {-"~~,"-}
\end{code}
where |DtoN D1 = 1|.
Since the only available digit is |D1|, we recover the standard Peano representation: the number $k$ is represented by $k$ copies of |D1| prepended to |N0|.

Increment and decrement are both $O(1)$:
\begin{code}
  inc : Nat → Nat
  inc n = D1 ⟨ n ⟩ {-"~~,"-}

  dec : Nat → Nat
  dec N0         = N0
  dec (D1 ⟨ n ⟩)  = n {-"~~."-}
\end{code}
Correctness follows immediately --- all proofs reduce to |refl|:
\begin{code}
  inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
  inc-correct n = refl {-"~~."-}
\end{code}
Moreover, |toN| and |fromN| (defined by iterating |inc|) constitute a bijection between |Nat| and |ℕ|, verified in both directions:
\begin{code}
  toN-fromN  : ∀ n → toN (fromN n) ≡ n  {-"~~,"-}
  fromN-toN  : ∀ n → fromN (toN n) ≡ n  {-"~~."-}
\end{code}

\subsection{Random-Access Lists from Unary Numbers}

The corresponding data structure is a \emph{random-access list} (RAL) indexed by |Nat|.
Each digit |D1| is ornamented to carry one element of type |A|:
\begin{code}
  data Some (A : Set) : Digit → Set where
    one : A → Some A D1 {-"~~,"-}

  data RAL (A : Set) : Nat → Set where
    nil   : RAL A N0
    more  : ∀ {d n} → Some A d → RAL A n → RAL A (d ⟨ n ⟩) {-"~~."-}
\end{code}
This is precisely the type of length-indexed vectors: |cons| prepends an element in $O(1)$, and |lookup| traverses the spine in $O(n)$ time.
The index type |Idx| has two constructors corresponding to the two ways of selecting an element: the head element, or a recursive position in the tail.

While conceptually clean, the unary representation suffers from the fact that all operations that traverse the entire structure --- such as |lookup| and |append| --- are $O(n)$.

\subsection{Binary Numbers}

To obtain logarithmic-time operations, we switch to binary numbers by extending the digit set to include zero:
\begin{code}
  data Digit : Set where
    D0  : Digit
    D1  : Digit {-"~~,"-}
  data Binary : Set where
    B0    : Binary
    _⟨_⟩  : Digit → Binary → Binary {-"~~."-}
\end{code}
The digits are stored least-significant first, and the semantic function is:
\begin{code}
  toN : Binary → ℕ
  toN B0        = 0
  toN (d ⟨ b ⟩)  = DtoN d + 2 * toN b {-"~~."-}
\end{code}
Increment propagates a carry when the least-significant digit is |D1|:
\begin{code}
  inc : Binary → Binary
  inc B0          = D1 ⟨ B0 ⟩
  inc (D0 ⟨ b ⟩)  = D1 ⟨ b ⟩
  inc (D1 ⟨ b ⟩)  = D0 ⟨ inc b ⟩ {-"~~."-}
\end{code}
The worst-case cost is $O(\log n)$, since a carry may propagate through every digit; the amortised cost is $O(1)$.
Correctness is verified by induction, with the carry case appealing to the correctness of doubling:
\begin{code}
  inc-correct : ∀ b → toN (inc b) ≡ suc (toN b) {-"~~."-}
\end{code}
We also verify |toN-fromN : ∀ n → toN (fromN n) ≡ n|, establishing that |toN| is a left inverse of |fromN|.

\paragraph{The redundancy problem.}
Standard binary numbers admit \emph{leading zeros}: |B0|, |D0 ⟨ B0 ⟩|, |D0 ⟨ D0 ⟨ B0 ⟩ ⟩|, \ldots\ all denote zero.
More generally, distinct representations can map to the same natural number:
\begin{code}
  redundant : ∃ (λ x → ∃ (λ y → (x ≢ y) × (toN x ≡ toN y))) {-"~~,"-}
\end{code}
witnessed by |B0| and |D0 ⟨ B0 ⟩|.
As a consequence, the converse direction |fromN-toN : ∀ b → fromN (toN b) ≡ b| does \emph{not} hold: the round-trip through |ℕ| normalises away leading zeros.

\subsection{Random-Access Lists from Binary Numbers}

A binary RAL decorates each digit with data.
A |D0| digit carries nothing; a |D1| digit carries one element.
Crucially, at each successive position the element type \emph{doubles} to |A × A|, capturing a complete binary tree of increasing depth:
\begin{code}
  data Some (A : Set) : Digit → Set where
    zero  :          Some A D0
    one   : A →      Some A D1 {-"~~,"-}

  data RAL (A : Set) : Binary → Set where
    nil   : RAL A B0
    more  : ∀ {d b} → Some A d → RAL (A × A) b → RAL A (d ⟨ b ⟩) {-"~~."-}
\end{code}
The |cons| operation mirrors |inc|: when the least-significant digit is |D1|, the new element is paired with the existing one and carried to the next level:
\begin{code}
  cons : ∀ {A b} → A → RAL A b → RAL A (inc b)
  cons x nil                = more (one x) nil
  cons x (more zero xs)     = more (one x) xs
  cons x (more (one y) xs)  = more zero (cons (x , y) xs) {-"~~."-}
\end{code}
The index type |Idx| for binary RALs branches on the digit: a |D0| digit contributes two recursive directions (left and right child of the implicit complete binary tree at that level), while a |D1| digit adds a base index for the element it stores plus two recursive branches.
Lookup runs in $O(\log n)$ time.

\todo{expand on head and taill}

\section{Zeroless Representation}

The redundancy of standard binary numbers arises because the digit |D0| allows empty positions in the representation.
A natural remedy is to eliminate zero from the digit set entirely, restricting to the digits $\{1, 2\}$.
This yields what \citet{HinzeSwierstra:22:Calculating} term \emph{Leibniz numerals}.

\subsection{Zeroless Binary Numbers}

\begin{code}
  data Digit : Set where
    D1  : Digit
    D2  : Digit {-"~~,"-}
  data ZBinary : Set where
    B0    : ZBinary
    _⟨_⟩  : Digit → ZBinary → ZBinary {-"~~."-}
\end{code}
The semantic function assigns weight $2^k$ to the digit at position~$k$:
\begin{code}
  toN : ZBinary → ℕ
  toN B0        = 0
  toN (d ⟨ n ⟩)  = DtoN d + 2 * toN n {-"~~,"-}
\end{code}
where |DtoN D1 = 1| and |DtoN D2 = 2|.
Since every digit is at least~$1$, any representation other than |B0| necessarily denotes a positive number.

Increment flips a |D1| to |D2| without carry, and wraps a |D2| to |D1| while carrying to the next position:
\begin{code}
  inc : ZBinary → ZBinary
  inc B0          = D1 ⟨ B0 ⟩
  inc (D1 ⟨ n ⟩)  = D2 ⟨ n ⟩
  inc (D2 ⟨ n ⟩)  = D1 ⟨ inc n ⟩ {-"~~."-}
\end{code}
The worst case is still $O(\log n)$ when a chain of |D2| digits forces successive carries.
Decrement is symmetric, borrowing from the next position when a |D1| is encountered:
\begin{code}
  dec : ZBinary → ZBinary
  dec B0               = B0
  dec (D1 ⟨ B0 ⟩)      = B0
  dec (D1 ⟨ d ⟨ n ⟩ ⟩)  = D2 ⟨ dec (d ⟨ n ⟩) ⟩
  dec (D2 ⟨ n ⟩)        = D1 ⟨ n ⟩ {-"~~."-}
\end{code}
Correctness of both operations is verified, along with the property |dec-inc≡id : ∀ n → dec (inc n) ≡ n|, showing that decrement is a left inverse of increment at the representation level.

\subsection{Unique Representation}

The central advantage of the zeroless system is that every natural number has a \emph{unique} representation.
We formalise this as injectivity of~|toN|:
\begin{code}
  nonRedundant : ∀ x y → toN x ≡ toN y → x ≡ y {-"~~."-}
\end{code}

Together with |toN-fromN|, injectivity yields a full bijection:
\begin{code}
  fromN-toN : ∀ n → fromN (toN n) ≡ n {-"~~."-}
\end{code}
This is strictly stronger than what standard binary affords, where leading zeros prevent the round-trip from holding.

\subsection{Random-Access Lists}

As before, each digit is ornamented with data.
The digit |D1| carries one element; |D2| carries two:
\begin{code}
  data Some (A : Set) : Digit → Set where
    one  : A → Some A D1
    two  : A → A → Some A D2 {-"~~."-}
\end{code}
The |cons| operation mirrors |inc|: adding to a |D1| position produces a |D2|, while adding to a |D2| position wraps back to |D1| and carries a pair upward:
\begin{code}
  cons : ∀ {A n} → A → RAL A n → RAL A (inc n)
  cons x nil                  = more (one x) nil
  cons x (more (one y) xs)    = more (two x y) xs
  cons x (more (two y z) xs)  = more (one x) (cons (y , z) xs) {-"~~."-}
\end{code}
Since |inc| recurses only upon encountering |D2|, the operation is $O(1)$ amortised.
The |head| and |tail| functions can be typed to accept |RAL A (inc n)|, leveraging the Peano view to ensure the list is non-empty:
\begin{code}
  head : ∀ {A n} → RAL A (inc n) → A {-"~~,"-}
  tail : ∀ {A n} → RAL A (inc n) → RAL A n {-"~~."-}
\end{code}

\subsection{Index Types and Interface Laws}

The index type |Idx| mirrors the digit decomposition.
For a |D1| digit there is one base index (the element stored at that position) and two recursive branches (left and right children in the implicit tree); for |D2|, there are two base indices and two recursive branches.
We establish that |Idx| is isomorphic to |Fin ∘ toN| via mutually inverse maps |toF| and |fromF|, verified by:
\begin{code}
  toF-fromF : ∀ {n} (i : Fin (toN n)) → toF (fromF i) ≡ i {-"~~."-}
\end{code}

The index operations |izero| and |isucc| mirror the natural-number constructors at the index level.
Their correctness is expressed by:
\begin{code}
  izero-correct : ∀ {n} → toF (izero {n}) ≡ iz
  isucc-correct : ∀ {n} (i : Idx n) → toF (isucc i) ≡ is (toF i) {-"~~."-}
\end{code}
These enable verification of the full interface specification for one-sided flexible arrays \cite{HinzeSwierstra:22:Calculating}:
\begin{code}
  lookup-izero  : ∀ {A n} (x : A) (xs : RAL A n)
                    → lookup (cons x xs) izero ≡ x
  lookup-isucc  : ∀ {A n} (x : A) (xs : RAL A n) (i : Idx n)
                    → lookup (cons x xs) (isucc i) ≡ lookup xs i
  lookup-head   : ∀ {A n} (xs : RAL A (inc n))
                    → head xs ≡ lookup xs izero
  lookup-tail   : ∀ {A n} (xs : RAL A (inc n)) (i : Idx n)
                    → lookup (tail xs) i ≡ lookup xs (isucc i) {-"~~."-}
\end{code}
\todo{expand the arithmetic operations on Idx}


\section{Adding Redundancy}

The zeroless binary system of the previous section provides unique representations and a clean interface.
When only |inc| is used, the amortised cost per operation is $O(1)$.
However, when |inc| and |dec| are \emph{interleaved}, it can force repeated carry and borrow chains that degrade the amortised bound.
In this section we explore how \emph{adding redundancy} to the digit set restores good amortised performance under arbitrary sequences of increments and decrements, at the expense of uniqueness of representation.

\subsection{Redundant Binary Numbers}

We extend the digit set to $\{1, 2, 3\}$:
\begin{code}
  data Digit : Set where
    D1  : Digit
    D2  : Digit
    D3  : Digit {-"~~,"-}
  data RBinary : Set where
    B0    : RBinary
    _⟨_⟩  : Digit → RBinary → RBinary {-"~~."-}
\end{code}
The semantic function retains its uniform shape:
\begin{code}
  toN : RBinary → ℕ
  toN B0        = 0
  toN (d ⟨ n ⟩)  = DtoN d + 2 * toN n {-"~~."-}
\end{code}
Increment absorbs a carry locally whenever the digit is below its maximum:
\begin{code}
  inc : RBinary → RBinary
  inc B0          = D1 ⟨ B0 ⟩
  inc (D1 ⟨ n ⟩)  = D2 ⟨ n ⟩
  inc (D2 ⟨ n ⟩)  = D3 ⟨ n ⟩
  inc (D3 ⟨ n ⟩)  = D2 ⟨ inc n ⟩ {-"~~."-}
\end{code}
A carry propagates only when the digit is already |D3|, and the digit then resets to |D2| rather than |D1|.
The worst-case cost of a single |inc| remains $O(\log n)$, since a chain of |D3| digits forces successive carries just as a chain of |D2| digits does in the zeroless system.
The crucial difference emerges under mixed sequences of |inc| and |dec|: after a carry resets a |D3| to |D2|, a subsequent |dec| at that position merely decreases |D2| to |D1| without triggering a borrow.
Symmetrically, after a borrow resets a |D1| to |D2|, a subsequent |inc| increases |D2| to |D3| without carrying.
The extra room in the digit range $\{1, 2, 3\}$ thus acts as a buffer that prevents carries and borrows from cascading in alternation, ensuring that the amortised cost per operation remains $O(1)$ even when |inc| and |dec| are interleaved arbitrarily.
\todo{simplify the explanation done by Chris Okasaki}

Decrement is defined symmetrically, borrowing when the digit is |D1|:
\begin{code}
  dec : RBinary → RBinary
  dec B0               = B0
  dec (D1 ⟨ B0 ⟩)      = B0
  dec (D1 ⟨ d ⟨ n ⟩ ⟩)  = D2 ⟨ dec (d ⟨ n ⟩) ⟩
  dec (D2 ⟨ n ⟩)        = D1 ⟨ n ⟩
  dec (D3 ⟨ n ⟩)        = D2 ⟨ n ⟩ {-"~~."-}
\end{code}
Correctness of both operations is verified:
\begin{code}
  inc-correct : ∀ n → toN (inc n) ≡ suc (toN n)
  dec-correct : ∀ n → toN (dec n) ≡ pred (toN n) {-"~~."-}
\end{code}

\subsection{Consequences of Redundancy}

The enlarged digit set introduces three complications absent from the zeroless system.

\paragraph{Non-unique representation.}
Multiple representations can denote the same value.
For example, both |D3 ⟨ B0 ⟩| and |D1 ⟨ D1 ⟨ B0 ⟩ ⟩| represent the number~$3$:
\begin{code}
  redundant : ∃ (λ x → ∃ (λ y → (x ≢ y) × (toN x ≡ toN y))) {-"~~."-}
\end{code}

\paragraph{Decrement does not invert increment.}
Since multiple representations coexist, |dec (inc n)| need not return |n| itself:
\begin{code}
  dec-inc≢id : ∃ (λ n → n ≢ dec (inc n)) {-"~~."-}
\end{code}
For instance, |inc| maps |D3 ⟨ B0 ⟩| to |D2 ⟨ D1 ⟨ B0 ⟩ ⟩|, and |dec| then yields |D1 ⟨ D1 ⟨ B0 ⟩ ⟩|, a different representation of the same number~$3$.

\paragraph{Gaps in the image of increment.}
Not every non-zero |RBinary| is of the form |inc y| for some~|y|:
\begin{code}
  inc-gap : ∃ (λ x → (toN x ≢ 0) × (∀ y → x ≢ inc y)) {-"~~."-}
\end{code}
The witness is |D1 ⟨ D1 ⟨ B0 ⟩ ⟩|: no |y| satisfies |inc y ≡ D1 ⟨ D1 ⟨ B0 ⟩ ⟩|, because |inc| always produces an initial |D1| only at the base case |B0|, never as a result of carrying.
This directly affects the type of |head|: the signature |head : RAL A (inc n) → A| used in the zeroless system cannot accept all non-empty RALs.
We must instead require an explicit non-emptiness proof:
\begin{code}
  head : ∀ {A n} → RAL A n → (toN n ≢ 0) → A {-"~~."-}
\end{code}

\subsection{Random-Access Lists}

Each digit carries a number of elements equal to its value:
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
  cons x nil                          = more (one x) nil
  cons x (more (one y) xs)            = more (two x y) xs
  cons x (more (two y z) xs)          = more (three x y z) xs
  cons x (more (three y z w) xs)      = more (two x y) (cons (z , w) xs) {-"~~."-}
\end{code}
The worst-case cost of |cons| mirrors that of |inc| and is $O(\log n)$.
However, when |cons| and |tail| are interleaved, the redundant digit range prevents cascading carries and borrows, yielding $O(1)$ amortised cost per operation --- a strict improvement over the zeroless system under mixed workloads.

The |tail| operation is defined via |dec|.
When the leading digit is |D1| and the remaining number is non-empty, |tail| borrows from the next level, splitting a pair and increasing the local digit to |D2|.

\subsection{Index Types}

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

\section{Symmetric Representation}

\section{Fractional Digits}

\section{Conclusions}

\cite{Claessen:20:Finger}
\cite{HinzeSwierstra:22:Calculating}

\bibliographystyle{ACM-Reference-Format}
\bibliography{ds-num}
\end{document}

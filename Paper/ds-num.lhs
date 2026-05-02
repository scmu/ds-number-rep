
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

%include sections/Intro.agda
%include sections/Unary.agda
%include sections/Binary.agda
%include sections/ZerolessBinary.agda
%include sections/RedundantBinary.agda

\section{Symmetric Representation}

\section{Fractional Digits}

\section{Conclusions}

\cite{Claessen:20:Finger}
\cite{HinzeSwierstra:22:Calculating}

\bibliographystyle{ACM-Reference-Format}
\bibliography{ds-num}
\end{document}

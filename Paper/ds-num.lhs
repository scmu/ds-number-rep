%let anonymous = False
%let draft = False

%% lhs2TeX --agda ds-num.lhs | pdflatex --jobname=ds-num

\documentclass[acmsmall,fleqn,screen,nonacm]{acmart}
\settopmatter{printccs=false, printacmref=false}
\setcopyright{none}

\usepackage[capitalise,noabbrev]{cleveref}
\citestyle{acmauthoryear}
\crefformat{equation}{#2#1#3}

\usepackage{mathtools}
\usepackage{varwidth}
\usepackage{pifont}

\usepackage{mdframed}
\newenvironment{temp}{\begin{mdframed}[backgroundcolor=red!7, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]\setlength{\abovedisplayskip}{0ex}\raisebox{-\height-3pt}[0pt][0pt]{\hspace{.965\textwidth}\color{red}\huge\ding{56}}}{\end{mdframed}}
%\definecolor{SkyBlue}{HTML}{D9F6FF}
%\newenvironment{final}{\begin{mdframed}[backgroundcolor=SkyBlue, linewidth=0, skipabove=1ex, leftmargin=1ex, rightmargin=0, innerleftmargin=0, innerrightmargin=0, innertopmargin=0, innerbottommargin=0]}{\end{mdframed}}

\usepackage{wrapfig}
\usepackage{xifthen}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\usepackage[inline]{enumitem} % for environment enumerate*
\newlist{inlineenum}{enumerate*}{1}
\setlist[inlineenum]{label=(\arabic*)}

\setlength{\marginparwidth}{1.25cm}
\usepackage[obeyFinal,color=yellow,textsize=scriptsize%
%if not draft
,disable%
%endif
]{todonotes}

\newcommand{\Shin}[1]{\footnote{\color{blue}Shin: #1}}
\newcommand{\Jeremy}[1]{\footnote{\color{blue}Jeremy: #1}}

\newenvironment{aha}{\medskip}{\unskip\medskip} % for one-line paragraphs
\makeatletter
\newcommand{\pause}{\medskip\centerline{$\ast\quad\ast\quad\ast$}\medskip\@@afterindentfalse\@@afterheading} % for a mid-section pause
\newcommand{\bigpause}{\medskip\centerline{$\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast\quad\ast$}\medskip\@@afterindentfalse\@@afterheading} % to set off the Afterword
\makeatother

\newcommand{\csp}{\hspace{.5em minus .1em}}
\newcommand{\equals}{\enskip=\enskip}

\usepackage{tikzit}
\input{string.tikzstyles}

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


\section{Introduction}

\section{Lists, Unary, and Binary Numbers}

\section{Zeroless Representation}

\section{Adding Redundancy}

\section{Symmetric Representation}

\section{Fractional Digits}

\section{Conclusions}

\citet{HinzePaterson:06:Finger}
\cite{Claessen:20:Finger}
\cite{Okasaki:99:Purely}
\cite{HinzeSwierstra:22:Calculating}

\bibliographystyle{ACM-Reference-Format}
\bibliography{ds-num}
\end{document}

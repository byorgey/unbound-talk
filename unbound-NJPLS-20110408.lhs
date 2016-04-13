%% -*- LaTeX -*-
\documentclass[xcolor=svgnames,12pt, mathserif]{beamer}

%include polycode.fmt

%format Name   = "\comb{Name}"
%format Bind   = "\comb{Bind}"
%format Embed  = "\comb{Embed}"
%format Rec    = "\comb{Rec}"
%format Shift  = "\comb{Shift}"
%format Rebind = "\comb{Rebind}"

%format Fresh  = "\cons{Fresh}"
%format unbind = "\cons{unbind}"
%format bind   = "\cons{bind}"
%format fv     = "\cons{fv}"
%format subst  = "\cons{subst}"

%format e1
%format e2
%format e1'
%format e2'

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

  \setbeamertemplate{footline}[frame number]

  % \AtBeginSection[]
  % {
  %   \begin{frame}<beamer>
  %     \frametitle{Outline}
  %     \tableofcontents[currentsection,currentsubsection]
  %   \end{frame}
  % }
}

% \setbeameroption{show notes}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}
\usepackage{xspace}

\newcommand{\bay}[1]{\textcolor{blue}{\bf #1 --BAY}}

\newcommand{\unbound}{\textsc{Unbound}\xspace}

\newcommand{\cons}[1]{\textsf{#1}}
\newcommand{\comb}[1]{\textbf{#1}}

\graphicspath{{images/}}

\title{Binders Unbound}
\date{NJPLS \\ Princeton University \\ April 8, 2011}
\author[Weirich, Yorgey, Sheard]
  {Stephanie Weirich\inst{1} \and \textcolor{blue}{Brent Yorgey}\inst{1} \and Tim
    Sheard\inst{2}}
\institute{\inst{1}University of Pennsylvania \and \inst{2}Portland
  State University}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

  \begin{frame}{}
   \titlepage

   \begin{center}
     \includegraphics[width=0.47in]{images/plclub.png}     
   \end{center}
  \end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Introduction}

  \begin{frame}{Lambda calculus}
Let's implement the lambda calculus:
\[ t ::= x \mid t\ t \mid \lambda x. t \]
in Haskell. \bigskip

\onslide<2->
First try:
\begin{spec}
data E  =  Var String
        |  App E E
        |  Lam String E
    \end{spec}
\onslide<3->
\vspace{-2em}
\begin{spec}
subst :: String -> E -> E -> E
subst x u t = ... ?
\end{spec}

\note{
  \begin{itemize}
    \item Standard syntax of the untyped lambda calculus.
    \item We can directly translate it into Haskell like this.
    \item But writing functions like capture-avoiding substitution is
      tricky and annoying! (Explain a bit more)
    \item Problem is that there is some structure (relationship
      between Strings) not encoded in the type.
  \end{itemize}

\bay{Do we need more introduction here?  How much background
  can/should we assume?}
}
  \end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  \begin{frame}{\dots with \unbound}
\[ t ::= x \mid t\ t \mid \lambda x. t \]
    \begin{spec}
type N  =  Name E
data E  =  Var N
        |  App E E
        |  Lam (Bind N E)
    \end{spec}
\onslide<2>
\dots and now we get these for free!
\begin{spec}
subst  :: N -> E -> E -> E
fv     :: E -> [N]
...
\end{spec}
\note{
\unbound to the rescue!  Encode our type like this, using special |Name|
and |Bind|\dots and (with a tiny bit of boilerplate I'll talk about later) we get
correct implementations of subst (and also fv and other things) for free!
}
  \end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  \begin{frame}{Example (parallel reduction)}
\begin{overprint}
\only<1>{
\begin{spec}
red :: Fresh m => E -> m E 
red (Var x) = return (Var x)
red (Lam b) = do
  (x, e)  <- unbind b
  e'      <- red e
  case e' of
    App e'' (Var y) 
      | x == y && not (x `elem` fv e'') 
        -> return e''
    _   -> return (Lam (bind x e'))
\end{spec}
}
\only<2>{
\begin{spec}
red (App e1 e2) = do 
  e1' <- red e1
  case e1' of
    Lam b -> do
      (x, e')  <- unbind b
      e2'      <- red e2
      return (subst x e2' e')
    _ -> do 
      e2' <- red e2
      return (App e1' e2')
\end{spec}
}
\end{overprint}
\note{Explain the code.  Note how unbind generates fresh names, use of
  fv and subst.}
  \end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Examples of binding structure}
\label{sec:zoo}

\begin{frame}
  \unbound provides a set of \emph{type combinators} for expressing
  binding structure. \bigskip

  What other sorts of binding structure can we encode?
\end{frame}

\begin{frame}{Binding multiple names}
Instead of $\lambda x.\ \lambda y.\ \lambda z.\ t$,
  \[ \lambda\ x\ y\ z.\ t \]
\onslide<2>
  \begin{spec}
data E  =  ...
        |  Lam (Bind [N] E)
  \end{spec}
  
\note{What other sorts of binding structure might we want to express?
  One of the keys to \unbound's expressivity is that we are not
  restricted to binding a single var at once.  For example\dots}
\end{frame}

  \begin{frame}{Let}
    \begin{center}
      \[ \cons{let}\ x = e_1\ \cons{in}\ e_2 \] ($x$ bound in $e_2$)
    \end{center}
\begin{overprint}
\only<1>{}
\only<2>{
First try:
    \begin{spec}
data E  =  ...
        |  Let E (Bind N E)
    \end{spec}
}\only<3>{
Better:
\begin{spec}
data E  =  ...
        |  Let (Bind (N, Embed E) E)
\end{spec}
}
\end{overprint}
\note{How about adding let-binding?  First try, has the right behavior
  but is annoying.  Better solution.  Embed lets us embed terms that
  don't bind names along with the rest of a pattern.
}
  \end{frame}

  \begin{frame}{Multi-let}
    \begin{center}
      \[ \cons{let}\ x_1 = e_1,\ \dots,\ x_n = e_n\ \cons{in}\ e \]
      ($x_i$ bound in $e$)
    \end{center}
    \begin{spec}
data E  =  ...
        |  Let (Bind [(N, Embed E)] E)
    \end{spec}

    \note{The real payoff is that we can easily extend this to let
      with multiple bindings!}
  \end{frame}

  \begin{frame}{Recursive binding}
How about%
\vspace{-3em}%
\begin{center}%
  \[ \cons{letrec}\ x_1 = e_1,\ \dots,\ x_n = e_n\ \cons{in}\ e \]
  ($x_i$ bound in $e$ and all $e_j$)?
\end{center}
\onslide<2>
Recursive binding:
\begin{spec}
data E  =  ...
        |  Letrec (Bind (Rec [(N, Embed E)]) E)
\end{spec}
  \end{frame}

  \begin{frame}{\cons{let*}}
What about%
\begin{center}%
\vspace{-3em}
\[ \cons{let*}\ x_1 = e_1,\ \dots,\ x_n = e_n\ \cons{in}\ e \]
($x_i$ bound in $e$ and $e_j$ for $j > i$)?
\end{center}
\onslide<2>
Working but suboptimal:
\begin{spec}
data LetList  =  Body E
              |  Binding (Bind  (N, Embed E) 
                                LetList)
data E        =  ...
              |  LetStar LetList
\end{spec}
\note{Here each of the $x_i$ is bound in all \emph{subsequent} $e_j$
  ($j > i$).  One way to encode this is by iterating the let
  encoding. However, can we do it pairing the body with the sequence
  of lets?}
  \end{frame}

  \begin{frame}{Nested binding?}
\[ \cons{let*}\ x_1 = e_1, \dots, x_n = e_n\ \cons{in}\ e \]

\begin{overprint}
\only<1>{
First try:
    \begin{spec}
data LetList  =  Nil
              |  Binding (Bind   (N, Embed E) 
                                 LetList)
data E        =  ...
              |  LetStar (Bind LetList E)
    \end{spec}
}
\only<2>{
Better:
    \begin{spec}
data LetList  =  Nil
              |  Binding (Rebind  (N, Embed E) 
                                  LetList)
data E        =  ...
              |  LetStar (Bind LetList E)
    \end{spec}
}
\end{overprint}
\note{Explain why the first try is not allowed: because Bind would
  have to have two different (context-sensitive!) semantics. Our
  semantics would no longer be compositional.}
  \end{frame}

\begin{frame}
  \begin{center}
    Want to know more? Read our paper!
    \bigskip

    On Hackage: \url{http://hackage.haskell.org/package/unbound/}
    \bigskip

    \texttt{cabal install unbound}
  \end{center}
  
\end{frame}

% \section{Semantics}

% \begin{frame}{Locally nameless}
% We specify the library's behavior by a \emph{locally nameless}
% semantics:
% \begin{itemize}
% \item Free variables are names
% \item Bound variables are de Bruijn indices
% \end{itemize}
% \end{frame}

%% show open, close, bind, rebind.

%% show unbind, freshen

%% show unrebind and talk about not freshening.

% \section{Implementation}

%% Alpha class

%% Freshness monads

\end{document}


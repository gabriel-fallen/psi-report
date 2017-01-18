\documentclass[runningheads,a4paper]{llncs}

\usepackage{amssymb}
\setcounter{tocdepth}{3}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage[references]{agda} 
\usepackage{url}
\newcommand{\keywords}[1]{\par\addvspace\baselineskip
\noindent\keywordname\enspace\ignorespaces#1}

\begin{document}

\mainmatter  % start of an individual contribution

% first the title is needed
\title{Verified type checker for Jolie programming language}

% a short form should be given in case it is too long for the running head
\titlerunning{Verified type checker for Jolie programming language}

% the name(s) of the author(s) follow(s) next
%
% NB: Chinese authors should write their first names(s) in front of
% their surnames. This ensures that the names appear correctly in
% the running heads and the author index.
%
\author{Eugene Akentyev}
%
\authorrunning{Verified type checker for Jolie programming language}
% (feature abused for this document to repeat the title also on left hand pages)

% the affiliations are given next; don't give your e-mail address
% unless you accept that it will be published
\institute{Innopolis University}

%
% NB: a more complex sample for affiliations and the mapping to the
% corresponding authors can be found in the file "llncs.dem"
% (search for the string "\mainmatter" where a contribution starts).
% "llncs.dem" accompanies the document class "llncs.cls".
%

\toctitle{Lecture Notes in Computer Science}
\tocauthor{Authors' Instructions}
\maketitle


\begin{abstract}

\keywords{formal verification, type checker, Agda, Jolie}
\end{abstract}


\section{Introduction}

Jolie is a service-oriented programming language ~\cite{mon10}. Its programs are constructed in three layers: the behavioural layer deals with the internal actions of a process and the communication it performs seen from the process’s point if view, the service layer deals with the underlying architectural instructions and the network layer deals with connecting communicating services.

This paper is literate Agda and uses standard library ~\cite{agdastdlib}.

\section{Behavioural layer}

\if{False}
\begin{code}
-- Imports
open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List.All using (All)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec using (Vec; _∈_; []; _++_; _∷_; here; there)
open import Data.Product using (_,_; _×_)
\end{code}
\fi

Jolie was created for microservices, which communicate with each other with messages. A variable in Jolie is a path in a message which is structured as a tree. For example:

\begin{center}
  amount = 12\\
  amount.fruit.apple = 2\\
  amount.fruit.description = "Apple"\\
\end{center}

To simplify the construction, I want to propose the enumeration of variables. Let $ J - $ a Jolie program, let $ V = vars(J) - $ variables in $ J $, then $ V_i = i$ where $i \in \mathbb{N} $. Then the example above will look like:

\begin{center}
  0 = 12\\
  1 = 2\\
  2 = "Apple"\\
\end{center}

Let's define the type of variables, since they are natural numbers:

\begin{code}
Variable : Set
Variable = ℕ
\end{code}

\begin{code}
data Value : Set where
  string : String → Value
  int : ℤ → Value
  bool : Bool → Value
  double : ℤ × ℤ → Value
  long : ℤ → Value
  void : Value
\end{code}

\begin{code}
data BinOp : Set where
  -- Arithmetics
  plus minus mult div power : BinOp
  -- Logical operations
  and or : BinOp

data Expr : Set where
  var : Variable → Expr
  binary : BinOp → Expr → Expr → Expr
  constant : Value → Expr
\end{code}

\begin{code}
data Operation : Set where
data Location : Set where
data Channel : Set where
\end{code}

\begin{code}
-- Output
data η̂ : Set where
  -- o@l(e) -- Notification
  _at_[_] : Operation → Location → Expr → η̂

  -- o@l(e)(x) -- Solicit-response
  _at_[_][_] : Operation → Location → Expr → Variable → η̂

data Behaviour : Set

-- Input
data η : Set where
  -- o(x) -- One-way
  _[_] : Operation → Variable → η

  -- o(x)(x'){B} -- Request-response
  _[_][_]_ : Operation → Variable → Variable → Behaviour → η

data Behaviour where
  input : η → Behaviour
  output : η̂  → Behaviour
  if_then_else_ : Expr → Behaviour → Behaviour → Behaviour
  while[_]_ : Expr → Behaviour → Behaviour
  
  -- Sequence
  _∶_ : Behaviour → Behaviour → Behaviour

  -- Parallel
  _∥_ : Behaviour → Behaviour → Behaviour

  -- Assign
  _≃_ : Variable → Expr → Behaviour

  nil : Behaviour

  -- [η₁]{B₁}⋯[ηₐ]{Bₐ} -- Input choice
  inputchoice : List (η × Behaviour) → Behaviour

  wait : Channel → Operation → Location → Variable → Behaviour
  exec : Channel → Operation → Variable → Behaviour → Behaviour
\end{code}

\begin{code}
data Type : Set where
  bool int double long string raw void : Type

data TypeDecl : Set where
  outNotify : Operation → Location → Type → TypeDecl
  outSolRes : Operation → Location → Type → Type → TypeDecl
  inOneWay : Operation → Type → TypeDecl
  inReqRes : Operation → Type → Type → TypeDecl
  var : Variable → Type → TypeDecl

data _⊆_ : Type → Type → Set where
  sub : {T₁ T₂ : Type} → T₁ ⊆ T₂

Ctx : ℕ → Set
Ctx = Vec TypeDecl

data Context : Set where
  ◆ : ∀ {n} → Ctx n → Context
  ■ : ∀ {n m} → Ctx n → Ctx m → Context
\end{code}

\begin{thebibliography}{4}

\bibitem{typesystemjolie} J. M. Nielsen. A Type System for the Jolie Language. 2013.

\bibitem{mon10} Fabrizio Montesi. Jolie: a service-oriented programming language. Master’s thesis, University of Bologna, Department of Computer Science, 2010.

\bibitem{agdastdlib} \url{https://github.com/agda/agda-stdlib}

\end{thebibliography}

\end{document}

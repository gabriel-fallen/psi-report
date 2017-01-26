\documentclass[runningheads,a4paper]{llncs}

\usepackage{ucs}
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[english]{babel}
\usepackage{unicode-math}
\setcounter{tocdepth}{3}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage{authblk}
\usepackage[references]{agda}
\usepackage{url}
\newcommand{\keywords}[1]{\par\addvspace\baselineskip
\noindent\keywordname\enspace\ignorespaces#1}

% set font
\setmainfont{XITS}
\setmathfont{XITS Math}
\setsansfont[Scale=MatchLowercase]{DejaVuSansMono.ttf}

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
\author[1]{Evgenii Akentev}
\author[2]{Alexander Tchitchigin}
\author[1,3]{Larisa Safina}
\author[1]{Manuel Mazzara}

\affil[1]{Innopolis University}
\affil[$\relax$]{\email{ak3ntev@gmail.com}, \email{\{l.safina, m.mazzara\}@innopolis.ru}}
\affil[2]{Kazan Federal University}
\affil[$\relax$]{\email{sad.ronin@gmail.com}}
\affil[3]{University of Southern Denmark}
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

\toctitle{Verified type checker for Jolie programming language}
\tocauthor{Authors' Instructions}
\maketitle

\begin{abstract}
Jolie is a service-oriented programming language which comes with the formal specification of its type system defined on paper.
However, there is no tool to ensure that programs in Jolie are well-typed. In this paper we provide the results
of building a type checker for Jolie as a part of its syntax and semantics formal model. We express
the type checker as a program with dependent types in Agda proof assistant which helps to ascertain that the type checker is correct.

\keywords{formal verification, type checker, dependent types, Agda, Jolie, type systems, microservices}
\end{abstract}

\if{False}
\begin{code}
-- Imports
open import Data.String using (String)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List.All using (All)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec using (Vec; []; _++_; _∷_; here; there)
open import Data.Product using (_,_; _×_)
open import Function using (_$_)
\end{code}
\fi

\section{Introduction}

Microservices are a new trend in software architecture ~\cite{DBLP:journals/corr/DragoniGLMMMS16}

Jolie is a service-oriented programming language ~\cite{montesi2010jolie}. Jolie programs are constructed
in three layers. Behavioural layer deals with internal actions of a process and communication
it performs as seen from the process’ point of view. Service layer deals with underlying
architectural instructions and network layer deals with connecting communicating services.



\section{Syntax of the behavioural layer}

Jolie was created for microservices which communicate with each other via messages.
A variable in Jolie represents a path in a message which is structured as a tree. For example:

\begin{center}
  amount = 12\\
  amount.fruit.apple = 2\\
  amount.fruit.description = "Apple"\\
\end{center}

To simplify the construction, we propose an enumeration of variables. Let $ J $ be a Jolie program,
$ V = vars(J) $ -- variables in $ J $, then $ V_i = i$ where $i \in \mathbb{N} $.
Then the example above will look like:

\begin{center}
  0 = 12\\
  1 = 2\\
  2 = "Apple"\\
\end{center}

After this simplification the type of variables can be defined. The type of natural numbers
is located in standard library of Agda~\cite{agdastdlib}.

\begin{code}
Variable : Set
Variable = ℕ
\end{code}

Complete syntax of behavioural layer can be found in~\cite{nielsen2013type} (page 2).
We do not need to consider expressions' structure to prove desired theorems
therefore type $Expr$ is left empty.

\begin{code}
data Expr : Set where
\end{code}

Operation names, channel names and locations are represented by strings.

\begin{code}
Operation Location Channel : Set
Operation = String
Location = String
Channel = String
\end{code}

\if{False}
\begin{code}
data η : Set
data η^ : Set
\end{code}
\fi

The behavioural layer has both ordinary control--flow statements ('if-then-else', 'while', 'assign')
and special statements to control parallelism and communication ('inputchoice', 'parallel', 'input', 'output', etc).

\begin{code}
data Behaviour : Set where
  if_then_else_ : Expr → Behaviour → Behaviour → Behaviour
  while[_]_ : Expr → Behaviour → Behaviour

  -- Sequence
  _∶_ : Behaviour → Behaviour → Behaviour

  -- Parallel
  _∥_ : Behaviour → Behaviour → Behaviour

  -- Assign
  _≃_ : Variable → Expr → Behaviour

  nil : Behaviour

  -- Input choice -- [η₁]{B₁}⋯[ηₐ]{Bₐ}
  inputchoice : List (η × Behaviour) → Behaviour

  wait : Channel → Operation → Location → Variable → Behaviour
  exec : Channel → Operation → Variable → Behaviour → Behaviour

  input : η → Behaviour
  output : η^  → Behaviour

-- Input
data η where
  -- o(x) -- One-way
  _[_] : Operation → Variable → η

  -- o(x)(x'){B} -- Request-response
  _[_][_]_ : Operation → Variable → Variable → Behaviour → η

-- Output
data η^ where
  -- o@l(e) -- Notification
  _at_[_] : Operation → Location → Expr → η^

  -- o@l(e)(x) -- Solicit-response
  _at_[_][_] : Operation → Location → Expr → Variable → η^
\end{code}

\section{Type system}

\begin{code}
data Type : Set where
  bool int double long string raw void : Type

data TypeDecl : Set where
  outNotify : Operation → Location → Type → TypeDecl
  outSolRes : Operation → Location → Type → Type → TypeDecl
  inOneWay : Operation → Type → TypeDecl
  inReqRes : Operation → Type → Type → TypeDecl
  var : Variable → Type → TypeDecl

Ctx : ℕ → Set
Ctx = Vec TypeDecl

data Context : Set where
  ⋆ : ∀ {n} → Ctx n → Context
  & : Context → Context → Context

infix 4 _∈_

data _∈_ : TypeDecl → Context → Set where
  here-⋆ : ∀ {n} {x} {xs : Ctx n}
         → x ∈ ⋆ (x ∷ xs)

  there-⋆ : ∀ {n} {x y} {xs : Ctx n}
            (x∈xs : x ∈ ⋆ xs)
          → x ∈ ⋆ (y ∷ xs)

  here-left-& : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
              → x ∈ &  (⋆ (x ∷ xs)) (⋆ ys)

  here-right-& : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
               → x ∈ & (⋆ xs) (⋆ (x ∷ ys))

  there-left-& : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
                 (x∈xs : x ∈ & (⋆ xs) (⋆ ys))
               → x ∈ & (⋆ (x ∷ xs)) (⋆ ys)

  there-right-& : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
                (x∈xs : x ∈ & (⋆ xs) (⋆ ys))
                → x ∈ & (⋆ xs) (⋆ (x ∷ ys))
\end{code}

Typing rules.

\begin{code}
data _⊢ₑ_∶_ (Γ : Context) : Expr → Type → Set where
  expr : {s : Expr} {b : Type}
       → Γ ⊢ₑ s ∶ b

data _⊢B_▹_ : Context → Behaviour → Context → Set where
  t-nil : {Γ : Context}
        → Γ ⊢B nil ▹ Γ

  t-if : {Γ Γ₁ : Context} {b₁ b₂ : Behaviour} {e : Expr}
       → Γ ⊢ₑ e ∶ bool
       → Γ ⊢B b₁ ▹ Γ₁
       → Γ ⊢B b₂ ▹ Γ₁
       → Γ ⊢B if e then b₁ else b₂ ▹ Γ₁

  t-while : {Γ : Context} {b : Behaviour} {e : Expr}
          → Γ ⊢ₑ e ∶ bool
          → Γ ⊢B b ▹ Γ
          → Γ ⊢B while[ e ] b ▹ Γ

  t-par : {Γ₁ Γ₂ Γ₁' Γ₂' : Context} {b1 b2 : Behaviour}
        → Γ₁ ⊢B b1 ▹ Γ₁'
        → Γ₂ ⊢B b2 ▹ Γ₂'
        → (& Γ₁ Γ₂) ⊢B b1 ∥ b2 ▹ (& Γ₁' Γ₂')

  t-seq : {Γ Γ₁ Γ₂ : Context} {b₁ b₂ : Behaviour}
        → Γ ⊢B b₁ ▹ Γ₁
        → Γ₁ ⊢B b₂ ▹ Γ₂
        → Γ ⊢B b₁ ∶ b₂ ▹ Γ₂
\end{code}

\subsection{Structural Congruence for Behaviours}

According to the Curry-Howard correspondence, types of the programs are propostions and terms are proofs. For example, the type $ A \rightarrow B $ correspond to the implication from $ A $ to $ B $ and such function $ f $ that takes an element of type $ A $ and returns an element of type $ B $ will be a proof of this theorem.

To demonstrate the correctness of the typing rules given above, we will prove the lemma called "Structural Congruence for Behaviours"~\cite{nielsen2013type} (page 42):

\begin{center}
\textit{Let} $ \Gamma \vdash B_1 \rhd \Gamma' $ \\
\textit{If} $ B_1 \equiv B_2 $ \\
\textit{then} $ \Gamma \vdash B_2 \rhd \Gamma' $
\end{center}

The proof is the case analysis of all possible $ B_1 $ and $ B_2 $.

\begin{itemize}

\item \textit{Case} $ B_1 \equiv B_2 $

In this case the proof is done by Agda's pattern matching.

\begin{code}
struct-cong-b₁≡b₂ : {Γ Γ₁ : Context} {b₁ b₂ : Behaviour}
                  → Γ ⊢B b₁ ▹ Γ₁
                  → b₁ ≡ b₂
                  → Γ ⊢B b₂ ▹ Γ₁
struct-cong-b₁≡b₂ t refl = t
\end{code}

\item \textit{Case} $ 0; B \equiv B $

\begin{code}
struct-cong-nil∶b→b : {Γ Γ₁ : Context} {b : Behaviour}
                    → Γ ⊢B nil ∶ b ▹ Γ₁
                    → Γ ⊢B b ▹ Γ₁
struct-cong-nil∶b→b (t-seq t-nil x) = x
\end{code}

\item \textit{Case} $ B \equiv 0 ; B $

\begin{code}
struct-cong-b→nil∶b : {Γ Γ₁ : Context} {b : Behaviour}
                    → Γ ⊢B b ▹ Γ₁
                    → Γ ⊢B nil ∶ b ▹ Γ₁
struct-cong-b→nil∶b x = t-seq t-nil x
\end{code}

\item \textit{Case} $ B \parallel 0 \equiv B $
\begin{code}
struct-cong-b∥nil→b : {Γ₁ Γ₂ Γ₁' Γ₂' : Context} {b : Behaviour}
                    → & Γ₁ Γ₂ ⊢B (b ∥ nil) ▹ & Γ₁' Γ₂'
                    → Γ₁ ⊢B b ▹ Γ₁'
struct-cong-b∥nil→b (t-par x _) = x
\end{code}

\item \textit{Case} $ B \equiv B \parallel 0 $

\begin{code}
struct-cong-b→b∥nil : {Γ₁ Γ₂ Γ₃ : Context} {b : Behaviour}
                    → Γ₁ ⊢B b ▹ Γ₂
                    → & Γ₁ Γ₃ ⊢B (b ∥ nil) ▹ & Γ₂ Γ₃
struct-cong-b→b∥nil x = t-par x t-nil
\end{code}

\item \textit{Case} $ B_1 \parallel B_2 \equiv B_2 \parallel B_1 $

\begin{code}
struct-cong-par-sym : {Γ₁ Γ₂ Γ₁' Γ₂' : Context} {b₁ b₂ : Behaviour}
                    → & Γ₁ Γ₂ ⊢B (b₁ ∥ b₂) ▹ & Γ₁' Γ₂'
                    → & Γ₂ Γ₁ ⊢B (b₂ ∥ b₁) ▹ & Γ₂' Γ₁'
struct-cong-par-sym (t-par t₁ t₂) = t-par t₂ t₁
\end{code}

\item \textit{Case} $ (B_1 \parallel B_2) \parallel B_3 \equiv B_1 \parallel (B_2 \parallel B_3) $

\begin{code}
struct-cong-par-assoc : {Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' : Context} {b₁ b₂ b₃ : Behaviour}
                    → & (& Γ₁ Γ₂) Γ₃ ⊢B (b₁ ∥ b₂) ∥ b₃ ▹ & (& Γ₁' Γ₂') Γ₃'
                    → & Γ₁ (& Γ₂ Γ₃) ⊢B b₁ ∥ (b₂ ∥ b₃) ▹ & Γ₁' (& Γ₂' Γ₃')
struct-cong-par-assoc (t-par (t-par t1 t2) t3) = t-par t1 (t-par t2 t3)
\end{code}

The proof for $ B_1 \parallel (B_2 \parallel B_3) \equiv (B_1 \parallel B_2) \parallel B_3 $ is similar.

\end{itemize}

\section{Conclusions}

\section{Related and future work}

\bibliographystyle{unsrt}
\bibliography{report}

\end{document}

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
open import Data.Vec using (Vec; []; _++_; _∷_; here; there)
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

Jolie have different types of values, which form the expressions. We use types from the standard library ~\cite{agdastdlib} to represent them.

\begin{code}
data Value : Set where
  string : String → Value
  int : ℤ → Value
  bool : Bool → Value
  double : ℤ × ℤ → Value
  long : ℤ → Value
  void : Value
\end{code}

The expressions have usual form: $ 2 + 2 $, $ 2 != x $ and so on.

\begin{code}
data BinaryOp : Set where
  -- Arithmetical
  plus minus mult div power : BinaryOp
  -- Logical operations
  equal and or : BinaryOp

data UnaryOp : Set where
  not : UnaryOp

data Expr : Set where
  var : Variable → Expr
  binary : BinaryOp → Expr → Expr → Expr
  unary : UnaryOp → Expr → Expr
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
  ⋆ : ∀ {n} → Ctx n → Context
  ⅋ : Context → Context → Context

infix 4 _∈_

data _∈_ : TypeDecl → Context → Set where
  here-⋆ : ∀ {n} {x} {xs : Ctx n}
         → x ∈ ⋆ (x Vec.∷ xs)

  there-⋆ : ∀ {n} {x y} {xs : Ctx n}
            (x∈xs : x ∈ ⋆ xs)
          → x ∈ ⋆ (y Vec.∷ xs)

  here-left-⅋ : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
              → x ∈ ⅋  (⋆ (x Vec.∷ xs)) (⋆ ys)

  here-right-⅋ : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
               → x ∈ ⅋ (⋆ xs) (⋆ (x Vec.∷ ys))

  there-left-⅋ : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
                 (x∈xs : x ∈ ⅋ (⋆ xs) (⋆ ys))
               → x ∈ ⅋ (⋆ (x Vec.∷ xs)) (⋆ ys)
  
  there-right-⅋ : ∀ {n m} {x} {xs : Ctx n} {ys : Ctx m}
                  (x∈xs : x ∈ ⅋ (⋆ xs) (⋆ ys))
                → x ∈ ⅋ (⋆ xs) (⋆ (x Vec.∷ ys))
\end{code}

\begin{code}
data _⊢ₑ_∶_ (Γ : Context) : Expr → Type → Set where
  expr-t : {s : Expr} {b : Type}
         → Γ ⊢ₑ s ∶ b

data _⊢B_▹_ : Context → Behaviour → Context → Set where
  t-nil : {Γ : Context}
        --------------
        → Γ ⊢B nil ▹ Γ
          
  t-if : {Γ Γ₁ : Context} {b₁ b₂ : Behaviour} {e : Expr}
       → Γ ⊢ₑ e ∶ bool -- Γ ⊢ e : bool
       → Γ ⊢B b₁ ▹ Γ₁
       → Γ ⊢B b₂ ▹ Γ₁
       --------------------------------
       → Γ ⊢B if e then b₁ else b₂ ▹ Γ₁
          
  t-while : {Γ : Context} {b : Behaviour} {e : Expr} 
          → Γ ⊢ₑ e ∶ bool
          → Γ ⊢B b ▹ Γ
          -----------------------
          → Γ ⊢B while[ e ] b ▹ Γ

  t-par : {Γ₁ Γ₂ Γ₁' Γ₂' : Context} {b1 b2 : Behaviour}
        → Γ₁ ⊢B b1 ▹ Γ₁'
        → Γ₂ ⊢B b2 ▹ Γ₂'
        ------------------------------------
        → (⅋ Γ₁ Γ₂) ⊢B b1 ∥ b2 ▹ (⅋ Γ₁' Γ₂')

  t-seq : {Γ Γ₁ Γ₂ : Context} {b₁ b₂ : Behaviour}
        → Γ ⊢B b₁ ▹ Γ₁
        → Γ₁ ⊢B b₂ ▹ Γ₂
        -------------------
        → Γ ⊢B b₁ ∶ b₂ ▹ Γ₂
\end{code}

\begin{code}
struct-congruence : {Γ Γ₁ : Context} {b₁ b₂ : Behaviour}
                  → Γ ⊢B b₁ ▹ Γ₁
                  → b₁ ≡ b₂
                  → Γ ⊢B b₂ ▹ Γ₁
struct-congruence t refl = t

struct-cong-par-nil : {Γ₁ Γ₂ Γ₁' Γ₂' : Context} {b : Behaviour}
                    → ⅋ Γ₁ Γ₂ ⊢B (b ∥ nil) ▹ ⅋ Γ₁' Γ₂'
                    → Γ₁ ⊢B b ▹ Γ₁'
struct-cong-par-nil (t-par x _) = x

struct-cong-par-sym : {Γ₁ Γ₂ Γ₁' Γ₂' : Context} {b₁ b₂ : Behaviour}
                    → ⅋ Γ₁ Γ₂ ⊢B (b₁ ∥ b₂) ▹ ⅋ Γ₁' Γ₂'
                    → ⅋ Γ₂ Γ₁ ⊢B (b₂ ∥ b₁) ▹ ⅋ Γ₂' Γ₁'
struct-cong-par-sym (t-par t₁ t₂) = t-par t₂ t₁
\end{code}

\section{Conclusions}

\section{Future work}

\begin{thebibliography}{4}

\bibitem{typesystemjolie} J. M. Nielsen. A Type System for the Jolie Language. 2013.

\bibitem{mon10} Fabrizio Montesi. Jolie: a service-oriented programming language. Master’s thesis, University of Bologna, Department of Computer Science, 2010.

\bibitem{agdastdlib} \url{https://github.com/agda/agda-stdlib}

\end{thebibliography}

\end{document}

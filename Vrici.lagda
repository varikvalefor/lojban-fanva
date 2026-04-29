\include{msx.tex}

\title{le vrici je fancu pe le me'oi .Agda.\ velcki be le fanva be fi le glibau bei fo la .lojban.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\begin{code}
module Vrici where
\end{code}

\begin{code}
open import Function
  using (
    _∘_;
    _$_
  )
open import Data.List
  as 𝕃
  using (
    List
  )
open import Data.Unit
  using (
    tt
  )
open import Data.Maybe
  as ⁇
  using (
    Is-just;
    nothing;
    Maybe;
    just
  )
open import Data.Product
  using (
    uncurry;
    ∃
  )
open import Relation.Unary
  using (
    Decidable
  )
open import Relation.Nullary
  using (
    yes;
    no
  )
open import Data.Maybe.Relation.Unary.Any
  as DMRU∃
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )
\end{code}

\begin{code}
¯1↓ : ∀ {a} → {A : Set a} → List A → List A
¯1↓ = 𝕃.reverse ∘ 𝕃.drop 1 ∘ 𝕃.reverse
\end{code}

\begin{code}
Is-just? : ∀ {a} → {A : Set a} → Decidable $ Is-just {A = A}
Is-just? (just _) = yes $ DMRU∃.just tt
Is-just? nothing = no $ λ ()
\end{code}

\begin{code}
Porkle : ∀ {a} → {A : Set a} → List A → List A → Set a
Porkle x z = ∃ $ uncurry Td
  where
  Td : _ → _ → Set _
  Td m n = x ≡_ $ 𝕃.take m $ 𝕃.drop n z
\end{code}
\end{document}

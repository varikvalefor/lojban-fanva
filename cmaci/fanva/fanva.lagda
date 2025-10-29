\begin{code}
open import Truthbrary.Record.SR
  using (
    Show;
    Read;
    SR
  )

record TB : Set₁
  where
  field
    T : Set
    R : Read T
    S : Show T

record Fanva (t₁ t₂ : TB) : Set₁
  where
  field
    fanva : TB.T t₁ → TB.T t₂
\end{code}

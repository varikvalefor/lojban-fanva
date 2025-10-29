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
\end{code}

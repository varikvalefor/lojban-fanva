\begin{code}
open import Data.Sum
  using (
    _⊎_
  )
open import Function
  using (
    _$_
  )
open import Data.List
  using (
    List
  )
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

module lojban where
  module T where
    mutual
      data NIhO : Set
        where
          ValsiNi'o : NIhO

      data I : Set
        where
          ValsiI : I

      INI'O : Set
      INI'O = I ⊎ NIhO

      LE : Set
      LE = {!!}

      data Sumti : Set
        where
        LeSelbri : LE → Selbri → Sumti

      Cnima'oCo'e : Set
      Cnima'oCo'e = {!!}

      data Selbri : Set
        where
        selbriUI : Selbri → Cnima'oCo'e → Selbri

      record Bridi : Set
        where
        field
          selbri : Selbri
          terbri : List $ Sumti

      data Jufra : Set
        where
        cnima'o-co'e : Cnima'oCo'e → Jufra
        jufra : Bridi → Jufra

    T : Set
    T = List $ INI'O ⊎ Jufra

  lojban : TB
  lojban = record {
    T = T.T;
    R = {!!};
    S = {!!}
    }

open lojban using (lojban)

glibau : TB
glibau = {!!}

l→g : Fanva lojban glibau
l→g = {!!}
\end{code}

\begin{code}
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Fin
  as 𝔽
  using (
  )
open import Data.Sum
  using (
    inj₂;
    inj₁;
    _⊎_
  )
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
open import Data.Product
  as Σ
  using (
    Σ
  )
open import Truthbrary.Record.SR
  using (
    Show;
    Read;
    SR
  )
open import Data.List.Relation.Unary.All
  as LUA
  using (
    All
  )
open import Relation.Binary.PropositionalEquality
  as _≡_
  using (
    _≡_
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
    module Lerfu where
      -- | ni'o le cmene be le ctaipe
      -- cu na jai frili
      -- .i la'e di'u xajmi la .varik.
      y : Set
      y = {!!}

      a : Set
      a = {!!}

      e : Set
      e = {!!}

      i : Set
      i = {!!}

      o : Set
      o = {!!}

      u : Set
      u = {!!}

      b : Set
      b = {!!}

      c : Set
      c = {!!}

      d : Set
      d = {!!}

    data NIhO : Set
    data I : Set

    INI'O : Set

    LE : Set

    BAI  : Set

    data Sumti : Set
    Cnima'oCo'e : Set
    Cmevla : Set
    Gismu : Set
    Selbri : Set
    record Bridi : Set
    data Jufra : Set
    
    data NIhO
      where
        ValsiNi'o : NIhO

    data I
      where
        ValsiI : I

    INI'O = I ⊎ NIhO

    LE = {!!}

    BAI = {!!}

    data Sumti
      where
      LeSelbri : LE → Selbri → Sumti

    Cnima'oCo'e = {!!}

    Cmevla = {!!}

    Gismu = {!!}

    module Selbri
      where
      data Selbri' : Set
        where
        GismuC : Gismu → Selbri'
        CmevlaC : Cmevla → Selbri'
        UIC : Selbri' → Cnima'oCo'e → Selbri'

    Selbri = Selbri.Selbri'

    record Bridi
      where
      field
        selbri : Selbri
        terbri : List $ Sumti
        bais : List $ BAI Σ.× Sumti

    data Jufra
      where
      cnima'o-co'e : Cnima'oCo'e → Jufra
      jufra : Bridi → Jufra

    record T : Set
      where
      Is-inj₁ : ∀ {a b} → {A : Set a} → {B : Set b}
              → A ⊎ B
              → Set _
      Is-inj₁ x = Σ _ $ (x ≡_) ∘ inj₁

      Is-inj₂ : ∀ {a b} → {A : Set a} → {B : Set b}
              → A ⊎ B
              → Set _
      Is-inj₂ x = Σ _ $ (x ≡_) ∘ inj₂

      field
        liste : List $ INI'O ⊎ Jufra
        -- | .i ctaipe lo su'u bitmu lo jufra
        bitmu : (i₁ i₂ : 𝔽.Fin _)
              → 𝔽.toℕ i₁ ≡ ℕ.suc (𝔽.toℕ i₂)
              → Is-inj₂ (𝕃.lookup liste i₁)
              → Is-inj₁ (𝕃.lookup liste i₂)
              

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

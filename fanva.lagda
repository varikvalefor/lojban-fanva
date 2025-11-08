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
open import Data.Unit
  as ⊤
  using (
    ⊤
  )
open import Data.Maybe
  as ⁇
  using (
    Maybe
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

      f : Set
      f = {!!}

      g : Set
      g = {!!}

      j : Set
      j = {!!}

      k : Set
      k = {!!}

      l : Set
      l = {!!}

      m : Set
      m = {!!}

      n : Set
      n = {!!}

      p : Set
      p = {!!}

      r : Set
      r = {!!}

      s : Set
      s = {!!}

      t : Set
      t = {!!}

      v : Set
      v = {!!}

      x : Set
      x = {!!}

      z : Set
      z = {!!}

    data NIhO : Set
    I : Set
    FAhO : Set

    INI'O : Set

    LE : Set

    BAI  : Set

    KOhA : Set

    POI : Set

    NA : Set
    Na : Set

    Nai : Set

    Sumti : Set
    Cmevla : Set
    Gismu : Set
    Selbri : Set
    record Bridi : Set
    Jek : Set
    Jufra : Set

    module Cnima'o where
      Cnima'oCo'e : Set
      Cnima'oCo'e = {!!}

      record CniTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set

      Term : {A : Set} → ⦃ CniTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = CniTerm.Term T

      data Cni (Selma'o : Set) ⦃ _ : CniTerm Selma'o ⦄ : Set
        where
        CniX : (x : Selma'o)
             → Term x
             → Cnima'oCo'e
             → Cni Selma'o

    Cnima'oCo'e : Set
    Cnima'oCo'e = Cnima'o.Cnima'oCo'e

    module Bri
      where
      record BriTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set

      Term : {A : Set} → ⦃ BriTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = BriTerm.Term T
    
    data NIhO
      where
        ValsiNi'o : NIhO

    module I
      where
      data I' : Set

      instance
        cniTerm : Cnima'o.CniTerm I'

      data I'
        where
        IC : Lerfu.i → I'
        UIC : Cnima'o.Cni I' → I'

      instance
        cniTerm = record {
          Term = Term
          }
          where
          Term : I' → Set
          Term (IC i) = ⊤
          Term (UIC u) = {!!}

    I = I.I'

    FAhO = {!!}

    INI'O = I ⊎ NIhO

    module LE
      where
      data LE' : Set

      instance
        cniTerm : Cnima'o.CniTerm LE'

      data LE'
        where
        leC : Lerfu.l Σ.× Lerfu.e → LE'
        loC : Lerfu.l Σ.× Lerfu.o → LE'
        UIC : Cnima'o.Cni LE' → LE'

      instance
        cniTerm = {!!}

    LE = LE.LE'

    BAI = {!!}

    KOhA = {!!}

    module POI
      where
      record PoiTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set
        
      Term : {A : Set} → ⦃ PoiTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = PoiTerm.Term T

      data POI' : Set

      data POI'
        where

    POI = POI.POI'

    module Na where
      NA' : Set
      Na' : Set

      NA' = {!!}
      Na' = {!!}

    NA = Na.NA'
    Na = Na.Na'

    Nai = {!!}

    module Jek
      where

      record JekTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set

      Term : {A : Set} → ⦃ JekTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = JekTerm.Term T

      Jek' : Set
      Jek' = Maybe Na Σ.× {!!} Σ.× Maybe Nai

    Jek = Jek.Jek'

    module Sumti
      where
      data Sumti' : Set

      instance
        cniTerm : Cnima'o.CniTerm Sumti'
        briTerm : Bri.BriTerm Sumti'
        poiTerm : POI.PoiTerm Sumti'
        jekTerm : Jek.JekTerm Sumti'

      data Sumti'
        where
        KOhAC : KOhA → Sumti'
        LeSelbriC : LE → Selbri → Sumti'
        POIC : (x : Sumti')
             → POI.Term x
             → POI
             → Jufra
             → Sumti'
        JekC : (x : Sumti')
             → Jek.Term x
             → Jek
             → Sumti'
             → Sumti'

      instance
        cniTerm = {!!}
        briTerm = {!!}
        poiTerm = {!!}
        jekTerm = {!!}

    Sumti = Sumti.Sumti'

    Cmevla = {!!}

    Gismu = {!!}

    module Selbri
      where
      data Selbri' : Set
      
      instance cniTerm : Cnima'o.CniTerm Selbri'
      
      data Selbri'
        where
        GismuC : Gismu → Selbri'
        CmevlaC : Cmevla → Selbri'
        UIC : Cnima'o.Cni Selbri' → Selbri'

      instance cniTerm = {!!}

    Selbri = Selbri.Selbri'

    record Bridi
      where
      inductive

      ¯1↓ : ∀ {a} → {A : Set a} → List A → List A
      ¯1↓ = 𝕃.reverse ∘ 𝕃.drop 1 ∘ 𝕃.reverse

      private
        T = Bri.BriTerm.Term $ Sumti.briTerm

      instance
        cniTerm⊎ : Bri.BriTerm $ Sumti ⊎ BAI Σ.× Sumti
        cniTerm⊎ = record {
          Term = λ {(inj₁ s) → T s; (inj₂ (b Σ., s)) → T s}
          }

      field
        selbri : Selbri
        terbri : List $ Sumti ⊎ (BAI Σ.× Sumti)
        term : All Bri.Term $ ¯1↓ terbri

    module Jufra
      where
      data Jufra' : Set

      instance
        cniTerm : Cnima'o.CniTerm Jufra'

      data Jufra'
        where
        BridiC : Bridi → Jufra'
        UIC : Cnima'o.Cni Jufra' → Jufra'

      instance
        cniTerm = {!!}

    Jufra = Jufra.Jufra'

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
        famo : Maybe FAhO
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

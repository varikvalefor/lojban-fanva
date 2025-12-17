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
open import Data.Char
  as 𝕃
  using (
    Char
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
open import Data.Empty
  using (
    ⊥-elim;
    ⊥
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  as Σ
  using (
    _×_;
    _,_;
    Σ
  )
open import Relation.Nullary
  using (
    yes;
    no;
    ¬_
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
open import Data.Maybe.Relation.Unary.Any
  as ⁇∀
  using (
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
      record tLerfu (c : Char) : Set
        where
        field
          s : String
          nC : ℕ

        ,s = Data.String.fromList $ 𝕃.replicate nC ','
        c' = Data.String.fromChar c

        field
          d : s ≡ (,s Data.String.++ c')

      -- | ni'o le cmene be le ctaipe
      -- cu na jai frili
      -- .i la'e di'u xajmi la .varik.
      y : Set
      y = tLerfu 'y'

      a : Set
      a = tLerfu 'a'

      e : Set
      e = tLerfu 'e'

      i : Set
      i = tLerfu 'i'

      o : Set
      o = tLerfu 'o'

      u : Set
      u = tLerfu 'u'

      b : Set
      b = tLerfu 'b'

      c : Set
      c = tLerfu 'c'

      d : Set
      d = tLerfu 'd'

      f : Set
      f = tLerfu 'f'

      g : Set
      g = tLerfu 'g'

      j : Set
      j = tLerfu 'j'

      k : Set
      k = tLerfu 'k'

      l : Set
      l = tLerfu 'l'

      m : Set
      m = tLerfu 'm'

      n : Set
      n = tLerfu 'n'

      p : Set
      p = tLerfu 'p'

      r : Set
      r = tLerfu 'r'

      s : Set
      s = tLerfu 's'

      t : Set
      t = tLerfu 't'

      v : Set
      v = tLerfu 'v'

      x : Set
      x = tLerfu 'x'

      z : Set
      z = tLerfu 'z'

      y'y : Set
      y'y = tLerfu '\''

      karsna : Set
      karsna = a ⊎ e ⊎ i ⊎ o ⊎ u

      zunsna : Set
      zunsna = b ⊎ c ⊎ d ⊎ f ⊎ g ⊎
               j ⊎ k ⊎ l ⊎ m ⊎ n ⊎ p ⊎
               r ⊎ s ⊎ t ⊎ v ⊎ x ⊎ z

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

    -- | ni'o filri'a tu'a lo valsi bitmu lerfu
    Vlapoi : List Set → Set
    Vlapoi 𝕃.[] = ⊥
    Vlapoi (x 𝕃.∷ 𝕃.[]) = x
    Vlapoi (x 𝕃.∷ xs) = x × ValsiBitmuLerfuCo'e × Vlapoi xs
      where
      ValsiBitmuLerfuCo'e = {!!}

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

      -- instance
      --   -- | ni'o filri'a zo'e je tu'a zo toi'e
      --   cniTerm : CniTerm Cnima'oCo'e
      --   cniTerm = {!!}

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
        leC : Lerfu.l × Lerfu.e → LE'
        loC : Lerfu.l × Lerfu.o → LE'
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
        poiC : Lerfu.p → Lerfu.o → Lerfu.i → POI'
        noiC : Lerfu.n → Lerfu.o → Lerfu.i → POI'

      JePoiTerm : POI → Jufra → Set
      JePoiTerm = {!!}

      record PoiCl (Selma'o : Set) : Set
        where
        inductive

        ¯1↓ : ∀ {a} → {A : Set a} → List A → List A
        ¯1↓ = 𝕃.reverse ∘ 𝕃.drop 1 ∘ 𝕃.reverse

        T : Set
        T = POI × Jufra
        
        field
          s : Selma'o
          cl₀ : T
          clx : List $ Jek × T
          term : All (Σ.uncurry JePoiTerm) $ cl₀ 𝕃.∷ 𝕃.map Σ.proj₂ (¯1↓ clx)

        cl : List T
        cl = cl₀ 𝕃.∷ 𝕃.map Σ.proj₂ clx

      instance
        poiTermPoiCl : {s : Set}
                     → ⦃ _ : PoiTerm s ⦄
                     → PoiTerm (PoiCl s)
        poiTermPoiCl = {!!}
          
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

      module JE
        where
        JE : Set
        JE = Lerfu.j × Lerfu.karsna

        instance
          cniTerm : Cnima'o.CniTerm JE
          cniTerm = record {Term = λ _ → ⊤}

      JE = JE.JE

      record JekTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set

      Term : {A : Set} → ⦃ JekTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = JekTerm.Term T

      Jek' : Set
      Jek' = Maybe Na × Cnima'o.Cni JE × Maybe Nai

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
        POIC : POI.PoiCl Sumti'
             → Sumti'
        JekC : (x : Sumti')
             → Jek.Term x
             → Jek
             → Sumti'
             → Sumti'
        UIC : Cnima'o.Cni Sumti' → Sumti'

      instance
        cniTerm = record {
          Term = T
          }
          where
          T : Sumti' → Set
          T (KOhAC k) = T k
          T (POIC c) = {!!}
          T (LeSelbriC l s) = {!!}
          T (JekC x t j x₂) = {!!}
          T (UIC (Cnima'o.CniX s t c)) = {!!}
        briTerm = {!!}
        poiTerm = record {
          Term = T
          }
          where
          T : Sumti' → Set
          T (KOhAC x) = {!!}
          T (LeSelbriC x x₁) = {!!}
          T (POIC x) with 𝕃.last (POI.PoiCl.cl x)
          ... | ⁇.just x2 = Σ.uncurry POI.JePoiTerm x2
          ... | ⁇.nothing = {!!}
          T (JekC x x₁ x₂ x₃) = {!!}
          T (UIC x) = {!!}
        jekTerm = {!!}

    Sumti = Sumti.Sumti'

    Cmevla = {!!}

    Gismu = (Z × Z × K × Z × K) ⊎ (Z × K × Z × Z × K)
      where
      Z = Lerfu.zunsna
      K = Lerfu.karsna

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
        cniTerm⊎ : Bri.BriTerm $ Sumti ⊎ BAI × Sumti
        cniTerm⊎ = record {
          Term = λ {(inj₁ s) → T s; (inj₂ (_ , s)) → T s}
          }

      field
        selbri : Selbri
        terbri : List $ Sumti ⊎ (BAI × Sumti)
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
        fanmo : Maybe FAhO
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

module glibau where

  -- | ni'o sucta gerna le glibau be la .varik.
  module T where
    record Encl (Selma'oPe'a : Set) : Set₁
      where
      field
        isEncl : Selma'oPe'a → Set

    module Punkt where
      data Punkt : Set
        where
        Excl : Punkt
        FStop : Punkt
        Preti : Punkt

    Punkt = Punkt.Punkt

    module Conjunction where
      data Conjunction : Set
        where
        And : Conjunction
        And-Not : Conjunction
        Or : Conjunction
        Iff : Conjunction

    Conjunction = Conjunction.Conjunction

    Article : Set
    Article = {!!}

    NounValsi : Set
    NounValsi = {!!}

    mutual
      Adjective : Set
      Adjective = {!!}

      data Sumti : Set
        where
        sumtiNVla : Maybe Article → Maybe Adjective → NounValsi → Sumti
        sumtiArAdj : Article → Adjective → Sumti
        sumtiPrep : Sumti → PrepPh → Sumti

      Brivla : Sumti → Set
      Brivla = {!!}

      PrepPh : Set
      PrepPh = {!!}

      Adverb : Set
      Adverb = {!!}

      record Jufra : Set
        where
        field
          x₁ : Sumti
          adv₁ : List Adverb
          brivla : Brivla x₁
          adv₂ : List Adverb
          x₂ : Maybe Sumti
          fanmo-punkt : Punkt

    T : Set
    T = {!!}

  glibau : TB
  glibau = record {
    T = T.T;
    R = {!!};
    S = {!!}
    }

open glibau using (glibau)

l→g : Fanva lojban glibau
l→g = {!!}
\end{code}

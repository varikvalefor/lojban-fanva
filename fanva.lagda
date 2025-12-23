\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝕍}{\ensuremath{\mathnormal{\mathbb V}}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb M}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{𝔹}{\ensuremath{\mathnormal{\mathbb B}}}
\newunicodechar{ν}{\ensuremath{\mathnormal\nu}}
\newunicodechar{μ}{\ensuremath{\mathnormal\mu}}
\newunicodechar{τ}{\ensuremath{\mathnormal\tau}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ˡ}{\ensuremath{\mathnormal{^\AgdaFontStyle{l}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{≥}{\ensuremath{\mathnormal\geq}}
\newunicodechar{≮}{\ensuremath{\mathnormal\nless}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\phi}}
\newunicodechar{∧}{\ensuremath{\mathnormal\wedge}}
\newunicodechar{∣}{\ensuremath{\mathnormal |}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{σ}{\ensuremath{\mathnormal\sigma}}
\newunicodechar{π}{\ensuremath{\mathnormal\pi}}
\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₓ}{\ensuremath{\mathnormal{_\AgdaFontStyle{x}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_\AgdaFontStyle{m}}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_\AgdaFontStyle{p}}}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{⍉}{\ensuremath{\mathnormal{∘\hspace{-0.455em}\backslash}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{δ}{\ensuremath{\mathnormal\delta}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{↔}{\ensuremath{\mathnormal\leftrightarrow}}
\newunicodechar{≰}{\ensuremath{\mathnormal\nleq}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{⍨}{\ensuremath{\raisebox{-0.25ex}{\ddot\sim}}}
\newunicodechar{⁇}{\ensuremath{\mathnormal{?\hspace{-0.3em}?}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{⊥}{\ensuremath{\mathnormal{\bot}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\title{la fanva}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

\tableofcontents

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
open import Data.Bool
  as 𝔹
  using (
    Bool
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
\end{code}

\part{le vrici}

\chapter{la'oi .\AgdaRecord{TB}.}
ni'o ro da poi ke'a me'oi .Unicode.\ bangu zo'u ro de poi ke'a ctaipe la'oi .\D{TB}.\ zo'u ga jo de mapti da gi lo mu'oi glibau.\ \AgdaField{TB.T}\ .zoi.\ be de cu ctaipe lo ro te gerna be da

\begin{code}
record TB : Set₁
  where
  field
    T : Set
    R : Read T
    S : Show T
\end{code}

\chapter{la'oi .\AgdaRecord{Fanva}.}
ni'o ro da xi pa poi ke'a bangu zo'u ro da xi re poi ke'a bangu zo'u ro de xi pa poi ke'a ctaipe la'oi .\AgdaRecord{TB}.\ je cu mapti da xi pa zo'u ro de xi re poi ke'a ctaipe la'oi .\AgdaRecord{TB}.\ je cu mapti da xi re zo'u ro di poi ke'a ctaipe lo me'oi .\AgdaRecord{Fanva}.\ be de xi pa bei de xi re zo'u di zabna le ka ce'u mapti kei naja cu ckaji le ka ro cy poi gerna da xi pa ke'a zo'u lo mu'oi glibau.\ \AgdaField{Fanva.fanva}\ .glibau.\ be di bei cy je cu te gerna da xi re

.i la .varik.\ na birti lo du'u ma kau zabna le ka ce'u filri'a lo nu ciksi lo ctaipe be lo su'u mapti  .i lakne fa lo nu pluja fa lo smuni se ctaipe

\begin{code}
record Fanva (t₁ t₂ : TB) : Set₁
  where
  field
    fanva : TB.T t₁ → TB.T t₂
\end{code}

\part{le bangu se ctaipe}

\chapter{le sinxa be la .lojban.}

\begin{code}
module lojban where
\end{code}

\section{le gerna}
ni'o la .varik.\ cu troci lo nu la'oi .\AgdaFunction{T}.\ cu co'e ja velcki le gerna be le jbobau be vo'a

\begin{code}
  module T where
\end{code}

\begin{code}
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
\end{code}

\begin{code}
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
\end{code}

\begin{code}
    data NIhO : Set
    I : Set
    FAhO : Set

    INI'O : Set

    LE : Set
    KU : Set

    BAI  : Set

    KOhA : Set

    POI : Set

    NA : Set
    Na : Set

    Sumti : Set
    Cmevla : Set
    Gismu : Set
    Selbri : Set
    record Bridi : Set
    Jek : Set
    Jufra : Set
\end{code}

\begin{code}
    module Vlapoi where
      record ValsiBitmu (b : Bool) : Set
        where

      Vlapoi : List $ Set × Bool → Set → Set
      Vlapoi 𝕃.[] b = b
      Vlapoi ((x , d) 𝕃.∷ xs) b = x × ValsiBitmu d × Vlapoi xs b

    Vlapoi = Vlapoi.Vlapoi
\end{code}

\begin{code}
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
\end{code}

\begin{code}
    module Bri
      where
      record BriTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set

      Term : {A : Set} → ⦃ BriTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = BriTerm.Term T
\end{code}

\begin{code}
    data NIhO
      where
        ValsiNi'o : NIhO
\end{code}

\begin{code}
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
\end{code}

\begin{code}
    INI'O = I ⊎ NIhO
\end{code}

\begin{code}
    module KU where
      data KU' : Set
        where
          KUC : KU'

    KU = KU.KU'
\end{code}

\begin{code}
    FAhO = {!!}
\end{code}

\begin{code}
    module LE
      where
      data LE' : Set

      instance
        cniTerm : Cnima'o.CniTerm LE'

      data LE'
        where
        laC : Lerfu.l → Lerfu.a → LE'
        leC : Lerfu.l → Lerfu.e → LE'
        loC : Lerfu.l → Lerfu.o → LE'
        UIC : Cnima'o.Cni LE' → LE'

      instance
        cniTerm = {!!}

    LE = LE.LE'
\end{code}

\begin{code}
    BAI = {!!}
\end{code}

\begin{code}
    KOhA = {!!}
\end{code}

\begin{code}
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
\begin{code}

\end{code}
    module Na where
      NA' : Set
      Na' : Set

      NA' = {!!}
      Na' = {!!}

    NA = Na.NA'
    Na = Na.Na'
\begin{code}

\end{code}
    module JE
      where
      JE : Set
      JE = Lerfu.j × Lerfu.karsna

      instance
        cniTerm : Cnima'o.CniTerm JE
        cniTerm = record {Term = λ _ → ⊤}

    JE = JE.JE
\begin{code}

\end{code}
    module Jek
      where
      record JekTerm (Selma'o : Set) : Set₁
        where
        field
          Term : Selma'o → Set

      Term : {A : Set} → ⦃ JekTerm A ⦄ → A → Set
      Term ⦃ T ⦄ = JekTerm.Term T

      Jek' : Set
      Jek' = Vlapoi 𝕃.[ Na , 𝔹.false ] $ Cnima'o.Cni JE

    Jek = Jek.Jek'
\begin{code}

\end{code}
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
\begin{code}

\end{code}
    Cmevla = {!!}
\begin{code}

\end{code}
    Gismu = (Z × Z × K × Z × K) ⊎ (Z × K × Z × Z × K)
      where
      Z = Lerfu.zunsna
      K = Lerfu.karsna
\begin{code}

\end{code}
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
\begin{code}

\end{code}
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

      ST : Set
      ST = Sumti ⊎ (BAI × Sumti)

      field
        selbri : Selbri
        terbri : List $ ST
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
\end{code}

\section{le sinxa be le te tcidu bangu}
ni'o la .varik.\ cu troci lo nu la'oi .\F{lojban}.\ co'e ja velcki le jbobau be vo'a\sds  .i ku'i la'oi .\F{lojban}.\ na mulno pe'a

\begin{code}
  lojban : TB
  lojban = record {
    T = T.T;
    R = {!!};
    S = {!!}
    }
\end{code}

\begin{code}
lojban = lojban.lojban
\end{code}

\chapter{le sinxa be le glibau}

\begin{code}
module glibau where
\end{code}

\section{le gerna}
ni'o la .varik.\ cu troci lo nu ko'a goi la'oi .\AgdaFunction{T}.\ cu co'e ja velcki le gerna be le glibau be vo'a  .i ku'i ko'a na mulno pe'a

\begin{code}
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

    module Preposition where
      data Preposition : Set
        where

    Preposition = Preposition.Preposition

    module Article where
      data Article : Set
        where
        A : Article
        The : Article

    Article = Article.Article

    module Selbrivla0 where
      P : Set
      P = {!!}

      S : Set
      S = {!!}

    module NounValsi where
      module P where
        data P : Set
          where
          Causes : P
          Things : P
          Proofs : P
          Types : P
          Jbovla : String → P

      module S where
        data S : Set
          where
          Cause : S
          Thing : S
          Proof : S
          Type : S
          Jbovla : String → S

      data NounValsi : Set
        where
        P : P.P → NounValsi
        S : S.S → NounValsi

    NounValsi = NounValsi.NounValsi

    module Adverbivla where
      Adverbivla : Set
      Adverbivla = {!!}

    Adverbivla = Adverbivla.Adverbivla

    mutual
      Variable : Set
      Variable = {!!}

      Adjective : Set
      Adjective = {!!}

      data Sumti : Set
        where
        sumtiQuote : String → Sumti
        sumtiNVla : Maybe Article → Maybe Adjective → NounValsi → Sumti
        sumtiArAdj : Article → Adjective → Sumti
        sumtiPrep : Sumti → PrepPh → Sumti
        sumtiListe : (x : List Sumti) → 𝕃.length x ℕ.> 0 → Sumti
        -- | ni'o mapti zoi glibau. ((A THING $s$) $v$) $z$ .glibau.
        -- .i toldji la'e di'u
        sumtiVarDecl : Sumti → Variable → Sumti

      Selbrivla : Sumti → Set
      Selbrivla (sumtiQuote x) = {!!}
      Selbrivla (sumtiNVla _ _ (NounValsi.P _)) = Selbrivla0.P
      Selbrivla (sumtiNVla _ _ (NounValsi.S _)) = Selbrivla0.S
      Selbrivla (sumtiArAdj _ _) = Selbrivla0.P × Selbrivla0.S -- "is/are"
      Selbrivla (sumtiPrep x _) = Selbrivla x
      Selbrivla (sumtiVarDecl s _) = Selbrivla s
      Selbrivla (sumtiListe x _) with 𝕃.length x ℕ.>? 1
      ... | yes _ = Selbrivla0.P
      ... | no _ = Selbrivla0.S

      record RelPh (s : Sumti) : Set
        where
        inductive
        field
          restrictive : Bool
          bt : BridiTail s

      record Selbri (s : Sumti) : Set
        where
        field
          adv₁ : Adverb
          sbv : Selbrivla s
          adv₂ : Adverb

      record PrepPhSampu : Set
        where
        inductive
        field
          adv : Adverb
          pv : Preposition
          x₁ : Sumti

      data PrepPh : Set
        where
        PrepPhL : (x : List PrepPhSampu)
                → 𝕃.length x ℕ.> 0
                → PrepPh

      data Adverb : Set
        where
        AdverbAdverbivla : Adverbivla → Adverb
        AdverbP : PrepPh → Adverb

      data IntroPh : Set
        where
        Adv : Adverb → IntroPh
        IPP : PrepPh → IntroPh

      record BridiTail (x₁ : Sumti) : Set
        where
        field
          brivla : Selbri x₁
          x₂ : Maybe Sumti

      record Jufra : Set
        where
        field
          intro : IntroPh
          x₁ : Sumti
          bt : BridiTail x₁
          punkt : Punkt

    module JufraBitmu where
      data JufraBitmu : Set
        where
        SSep : JufraBitmu -- "  "
        Ni'oCu'iCai : JufraBitmu -- "\n"
        Ni'oCu'i : JufraBitmu -- "\n\n"

    JufraBitmu = JufraBitmu.JufraBitmu

    Emoticon : Set
    Emoticon = {!!}

    Pluja-Jufra : Set
    Pluja-Jufra = Jufra × List (JufraBitmu × Jufra)

    T : Set
    T = {!!}
\end{code}

\section{le sinxa be le te tcidu bangu}
ni'o la .varik.\ cu troci lo nu ko'a goi la'oi .\F{glibau}.\ co'e ja velcki le glibau be vo'a\sds  .i ku'i ko'a na mulno pe'a

\begin{code}
  glibau : TB
  glibau = record {
    T = T.T;
    R = {!!};
    S = {!!}
    }
\end{code}

\begin{code}
glibau = glibau.glibau
\end{code}

\part{le fanva co'e}

\begin{code}
l→g : Fanva lojban glibau
l→g = {!!}
\end{code}
\end{document}

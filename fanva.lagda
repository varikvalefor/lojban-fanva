\include{msx.tex}

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
    const;
    _∘_;
    _$_;
    id
  )
  renaming (
    _|>_ to _▹_
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

import Bangu.Lojban
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

\section{le sinxa be le te tcidu bangu}
ni'o la .varik.\ cu troci lo nu la'oi .\F{lojban}.\ co'e ja velcki le jbobau be vo'a\sds  .i ku'i la'oi .\F{lojban}.\ na mulno pe'a

\begin{code}
lojban : TB
lojban = record {
  T = Bangu.Lojban.T.T;
  R = {!!};
  S = {!!}
  }
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
\end{code}

\begin{code}
    module Punkt where
      data Punkt : Set
        where
        Excl : Punkt
        FStop : Punkt
        Preti : Punkt

    Punkt = Punkt.Punkt
\end{code}

\begin{code}
    module Conjunction where
      data Conjunction : Set
        where
        And : Conjunction
        And-Not : Conjunction
        Or : Conjunction
        Iff : Conjunction

    Conjunction = Conjunction.Conjunction
\end{code}

\begin{code}
    module Preposition where
      data Preposition : Set
        where

    Preposition = Preposition.Preposition
\end{code}

\begin{code}
    module Article where
      data Article : Set
        where
        A : Article
        The : Article

    Article = Article.Article
\end{code}

\begin{code}
    module Selbrivla0 where
      P : Set
      P = {!!}

      S : Set
      S = {!!}
\end{code}

\begin{code}
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
\end{code}

\begin{code}
    module Adverbivla where
      Adverbivla : Set
      Adverbivla = {!!}

    Adverbivla = Adverbivla.Adverbivla
\end{code}

\begin{code}
    mutual
\end{code}

\begin{code}
      Variable : Set
      Variable = {!!}
\end{code}

\begin{code}
      Adjective : Set
      Adjective = {!!}
\end{code}

\begin{code}
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
\end{code}

\begin{code}
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
\end{code}

\subsection{ko'a goi la'oi .\AgdaRecord{RelCl}.}
ni'o ko'a se ctaipe zo'e ja lo ro mu'oi glibau.\ relative clause .glibau.\ be bau le glibau be la .varik.

.i sa'u nai ru'e ro da poi ke'a ctaipe ko'a zo'u ga je\ldots

\begin{itemize}
	\item lo mu'oi zoi.\ \AgdaField{AgdaRecord.restrictive}\ .zoi.\ be da cu srana lo du'u xu kau mu'oi glibau.\ restrictive clause .glibau.\ gi
	\item lo mu'oi zoi.\ \AgdaField{AgdaRecord.bt}\ .zoi.\ be da cu velski lo sumti je ke co'e ja se velski be da
\end{itemize}

\begin{code}
      record RelCl (s : Sumti) : Set
        where
        inductive
        field
          restrictive : Bool
          bt : Clause s
\end{code}

\begin{code}
      record Selbri (s : Sumti) : Set
        where
        field
          adv₁ : Adverb
          sbv : Selbrivla s
          adv₂ : Adverb
\end{code}

\begin{code}
      record PrepPhSampu : Set
        where
        inductive
        field
          adv : Maybe Adverb
          pv : Preposition
          x₁ : Sumti
\end{code}

\begin{code}
      data PrepPh : Set
        where
        PrepPhPx : PrepPh → PrepPhSampu → PrepPh
        PrepPhJe : PrepPh → PrepPhSampu → PrepPh
\end{code}

\begin{code}
      data Adverb : Set
        where
        AdverbAdverbivla : Adverbivla → Adverb
        AdverbP : PrepPh → Adverb
\end{code}

\begin{code}
      data IntroPh : Set
        where
        Adv : Adverb → IntroPh
        IPP : PrepPh → IntroPh
\end{code}

\begin{code}
      record Clause (x₁ : Sumti) : Set
        where
        field
          brivla : Selbri x₁
          x₂ : Maybe Sumti
\end{code}

\begin{code}
      record Jufra : Set
        where
        field
          intro : IntroPh
          x₁ : Sumti
          bt : Clause x₁
          punkt : Punkt
\end{code}

\begin{code}
    module JufraBitmu where
      data JufraBitmu : Set
        where
        SSep : JufraBitmu -- "  "
        Ni'oCu'iCai : JufraBitmu -- "\n"
        Ni'oCu'i : JufraBitmu -- "\n\n"

    JufraBitmu = JufraBitmu.JufraBitmu
\end{code}

\begin{code}
    Emoticon : Set
    Emoticon = {!!}
\end{code}

\begin{code}
    Pluja-Jufra : Set
    Pluja-Jufra = Jufra × List (JufraBitmu × Jufra)
\end{code}

\begin{code}
    mutual
      data T : Set
        where
        NILC : T
        JufraC : (t : T) → JBT t → Jufra → T

      jufraBitmuSarcu : T → Bool
      jufraBitmuSarcu NILC = 𝔹.false
      jufraBitmuSarcu (JufraC _ _ _) = 𝔹.true

      JBT : T → Set
      JBT = λ t → JufraBitmu ▹_ $ 𝔹.if jufraBitmuSarcu t then Maybe else id
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

\include{msx.tex}

\title{le me'oi .Agda.\ velcki be le co'e be le glibau be la .varik.\ .VALefor.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

ni'o zu'edji lo ka ce'u vimcu pe'a\sds  .i ku'i lo nu vasru pe'a cu filri'a lo nu jmina pe'a fi zo'e ja la .fanva.

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\begin{code}
module Bangu.Glibau where
\end{code}

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
    _$_;
    id
  )
  renaming (
    constᵣ to _⊢_;
    const to _⊣_;
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
\end{code}

\begin{code}
module _ where
\end{code}

\part{le gerna}
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

\section{le valsi}

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

\subsection{la'oi .\F{Preposition}.}
ni'o ro da poi ke'a ctaipe la'oi .\F{Preposition}.\ zo'u da sinxa lo valsi be fi le glibau be'o je se cmene be da

\begin{code}
    module Preposition where
      data Preposition : Set
        where
        In : _
        Out : _
        Within : _
        At : _
        To : _
        With : _
        Of : _
        From : _
        Into : _
        On : _

    Preposition = Preposition.Preposition
\end{code}

\subsection{ko'a goi la'oi .\D{Article}.}
ni'o ro da poi ke'a ctaipe ko'a zo'u ga je da sinxa lo me'oi .article.\ be bau le glibau gi ga jonai\ldots

\begin{itemize}
	\item da du la'oi .\IC{A}.\ je cu sinxa zo'oi .A.\ ja zo'oi .AN.\ gi
	\item da sinxa lo valsi je ke co'e ja cmene be da
\end{itemize}

\begin{code}
    module Article where
      data Article : Set
        where
        A : Article
        The : Article

    Article = Article.Article
\end{code}

\begin{code}
    module VerbWord0 where
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
          ProperName : String → P
          Jbovla : String → P

      module S where
        data S : Set
          where
          Cause : S
          Thing : S
          Proof : S
          Type : S
          ProperName : String → S
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
    module Gerund where
      Gerund : Set
      Gerund = {!!}

    Gerund = Gerund.Gerund
\end{code}

\begin{code}
    module RelativeClauseWord where
      data RelativeClauseWord' : Set
        where
        Which : _
        What : _

    RelativeClauseWord = RelativeClauseWord.RelativeClauseWord'
\end{code}

\chapter{le zmadu be fi le ka ce'u pluja}

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

\section{la'oi .\D{Noun}.}

\begin{code}
      data Noun : Set
        where
        nounQuote : String → Noun
        nounNVla : Maybe Article → Maybe Adjective → NounValsi → Noun
        nounArAdj : Article → Adjective → Noun
        nounPrep : Noun → PrepPh → Noun
        nounListe : (x : List Noun) → 𝕃.length x ℕ.> 0 → Noun
        nounVarDecl : (n : Noun) → Variable → ¬ NounIsVarDecl n → Noun
        nounGerund : Maybe Adverb → Gerund → Maybe Adverb → Noun → Noun

      NounIsVarDecl : Noun → Set
      NounIsVarDecl (nounVarDecl _ _ _) = ⊤
      NounIsVarDecl _ = ⊥
\end{code}

\begin{code}
      VerbWord : Noun → Set
      VerbWord (nounQuote x) = {!!}
      VerbWord (nounNVla _ _ (NounValsi.P _)) = VerbWord0.P
      VerbWord (nounNVla _ _ (NounValsi.S _)) = VerbWord0.S
      VerbWord (nounArAdj _ _) = VerbWord0.P × VerbWord0.S -- "is/are"
      VerbWord (nounPrep x _) = VerbWord x
      VerbWord (nounVarDecl s _ _) = VerbWord s
      VerbWord (nounGerund a₁ g a₂ n) = {!!}
      VerbWord (nounListe x _) with 𝕃.length x ℕ.>? 1
      ... | yes _ = VerbWord0.P
      ... | no _ = VerbWord0.S
\end{code}

\section{ko'a goi la'oi .\AgdaRecord{RelCl}.}
ni'o ko'a se ctaipe zo'e ja lo ro mu'oi glibau.\ relative clause .glibau.\ be bau le glibau be la .varik.

.i sa'u nai ru'e ro da poi ke'a ctaipe ko'a zo'u ga je\ldots

\begin{itemize}
	\item lo mu'oi zoi.\ \AgdaField{AgdaRecord.restrictive}\ .zoi.\ be da cu srana lo du'u xu kau mu'oi glibau.\ restrictive clause .glibau.\ gi
	\item lo mu'oi zoi.\ \AgdaField{AgdaRecord.bt}\ .zoi.\ be da cu velski lo sumti je ke co'e ja se velski be da
\end{itemize}

\begin{code}
      record RelCl (s : Noun) : Set
        where
        inductive
        field
          word : RelativeClauseWord
          restrictive : Bool
          bt : Clause s
\end{code}

\section{ko'a goi la'oi .\AgdaRecord{Verb}.}
ni'o ro da poi ke'a ctaipe ko'a zo'u ga je da sinxa lo pluja selbri co'e be bau le glibau be la .varik.\ gi\ldots

\begin{itemize}
	\item ko'e goi lo mu'oi zoi.\ \AgdaField{Verb.verb}\ .zoi.\ be da cu sinxa lo selbri valsi be da gi ga je
	\item lo mu'oi zoi.\ \AgdaField{Verb.adv₁}\ .zoi.\ be da cu du la'oi .\IC{nothing}.\ jonai cu me'oi .\IC{just}.\ lo sinxa lo me'oi .adverb.\ co'e poi ke'a lidne lo se sinxa be ko'e gi
	\item lo mu'oi zoi.\ \AgdaField{Verb.adv₂}\ .zoi.\ be da cu du la'oi .\IC{nothing}.\ jonai cu me'oi .\IC{just}.\ lo sinxa be lo me'oi .adverb.\ co'e poi ke'a se lidne lo se sinxa be ko'e
\end{itemize}

\begin{code}
      record Verb (s : Noun) : Set
        where
        field
          adv₁ : Maybe Adverb
          verb : VerbWord s
          adv₂ : Maybe Adverb
\end{code}

\begin{code}
      record PrepPhSampu : Set
        where
        inductive
        field
          adv : Maybe Adverb
          pv : Preposition
          x₁ : Noun
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
        AdverbListe :  List Adverb → Adverb
\end{code}

\begin{code}
      data IntroPh : Set
        where
        Adv : Adverb → IntroPh
        Prep : PrepPh → IntroPh
\end{code}

\begin{code}
      record Clause (x₁ : Noun) : Set
        where
        field
          verb : Verb x₁
          x₂ : Maybe Noun
\end{code}

\begin{code}
      record Jufra : Set
        where
        field
          intro : IntroPh
          x₁ : Noun
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
\end{document}

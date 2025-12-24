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
import Bangu.Glibau
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

\chapter{le sinxa be la .lojban.}
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
ni'o la .varik.\ cu troci lo nu ko'a goi la'oi .\F{glibau}.\ co'e ja velcki le glibau be vo'a\sds  .i ku'i ko'a na mulno pe'a

\begin{code}
glibau : TB
glibau = record {
  T = Bangu.Glibau.T.T;
  R = {!!};
  S = {!!}
  }
\end{code}

\part{le fanva co'e}

\begin{code}
l→g : Fanva lojban glibau
l→g = {!!}
\end{code}
\end{document}

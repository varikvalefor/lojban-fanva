\include{msx.tex}

\title{le me'oi .Agda.\ velcki be le co'e be le jbobau be la .varik.\ .VALefor.}
\author{la .varik.\ .VALefor.}

\begin{document}

\maketitle

ni'o zu'edji lo ka ce'u vimcu pe'a\sds  .i ku'i lo nu vasru pe'a cu filri'a lo nu jmina pe'a fi zo'e ja la .fanva.

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
\end{code}

\begin{code}
module Bangu.Lojban where
\end{code}

\begin{code}
open import Vrici
  using (
    Porkle
  )

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
    _on_;
    _∘_;
    _$_;
    id
  )
  renaming (
    _|>_ to _▹_;
    flip to _⍨
  )
open import Data.Bool
  as 𝔹
  using (
    Bool
  )
open import Data.Char
  as Chr
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
  as 𝕊₀
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
open import Relation.Unary
  using (
    Decidable
  )
open import Relation.Binary
  as R₂
  using (
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
open import Data.Char.Properties
  as DCP
  using (
  )
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Truthbrary.Record.LLC
  using (
    _∈_
  )
open import Truthbrary.Data.Strong
  as 𝕊
  using (
    Strong
  )
open import Relation.Nullary.Decidable
  using (
    isYes
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

\part{le sucta gerna}
ni'o la .varik.\ cu troci lo nu la'oi .\F{ST}.\ cu co'e ja velcki le sucta gerna be le jbobau be vo'a

\begin{code}
module ST where
\end{code}

\chapter{le lerfu co'e\ldots noi ke'a se vasru pe'a la'oi .\AgdaModule{Lerfu}.}

\begin{code}
  module Lerfu where
    record tLerfu (c : Char) : Set
      where
\end{code}

\begin{code}
    Lerfu : Set
    Lerfu = Σ.∃ tLerfu
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
\end{code}

\begin{code}
    Karsna : Lerfu → Set
    Karsna (x , _) = x ∈ 𝕊₀.toList "aeiou"

    Karsna? : Decidable Karsna
    Karsna? _ = _ ≟ _
\end{code}

\begin{code}
    karsna : Set
    karsna = Σ.∃ Karsna
\end{code}

\begin{code}
    Zunsna : Lerfu → Set
    Zunsna (x , _) = x ∈ 𝕊₀.toList "bcdfgjklmnprstvxz"

    Zunsna? : Decidable Zunsna
    Zunsna? _ = _ ≟ _
\end{code}

\begin{code}
    zunsna : Set
    zunsna = Σ.∃ Zunsna
\end{code}

\begin{code}
    record Deconstructible {a} (A : Set a) : Set a
      where
      field
        selvau : A → Lerfu

    deconstruct : ∀ {a} → {A : Set a}
                → ⦃ Deconstructible A ⦄
                → A
                → Lerfu
    deconstruct ⦃ D ⦄ = Deconstructible.selvau D

    instance
      deconstructibleZunsna : Deconstructible zunsna
      deconstructibleZunsna = record {selvau = Σ.proj₁}

      deconstructibleKarsna : Deconstructible karsna
      deconstructibleKarsna = record {selvau = Σ.proj₁}
\end{code}

\begin{code}
    Voksa : {c : Char} → tLerfu c → Set
    Voksa {c} t = c ∈ 𝕊₀.toList "abdegijlmnoruvyz"

    Voksa? : {c : Char} → Decidable $ Voksa {c}
    Voksa? _ = _ ≟ _

    isVoksa : {c : Char} → tLerfu c → Bool
    isVoksa = isYes ∘ Voksa?
\end{code}

\begin{code}
    valsiBitmu : Set
    valsiBitmu = {!!}
\end{code}

\chapter{zo'e ja le se ctaipe be lo jbovla je zo'e}

\begin{code}
  module Jbovla where
\end{code}

\section{ko'a goi la'oi .\AgdaRecord{Jbovla}.}
ni'o ro da poi ke'a ctaipe ko'a zo'u ga je da sinxa lo valsi be fi le jbobau be la .varik.\ gi ga je\ldots
\begin{itemize}
	\item ko'e goi lo mu'oi zoi.\ \AgdaField{Jbovla.valsi}\ .zoi.\ be da cu du le se sinxa be da gi ga je
	\item lo mu'oi zoi.\ \AgdaField{Jbovla.mapti}\ .zoi.\ be da cu ctaipe lo su'u ko'a valsi fi le jbobau be la .varik.\ gi
	\item ga jonai ga je su'o de poi ke'a valsi le jbobau be la .varik.\ zo'u lo konkatena be ko'e bei de cu simlu lo ka ce'u du lo pa valsi gi la'o zoi.\ \IC{𝔹.true}\ .zoi.\ du ko'e goi lo mu'oi zoi.\ \AgdaField{Jbovla.valsiBitmuSarcu}\ .zoi.\ gi ko'e du la'o zoi.\ \IC{𝔹.false}\ .zoi.
\end{itemize}

\begin{code}
    record Jbovla : Set
      where
      field
        valsi : List Lerfu.Lerfu
        mapti : {!!}

      valsiBitmuSarcu : Bool
      valsiBitmuSarcu = {!!}

      pShow : Strong
      pShow = 𝕃.map Σ.proj₁ valsi

    Dunli : Jbovla → Jbovla → Set
    Dunli = _≡_ on (𝕃.map Σ.proj₁ ∘ Jbovla.valsi)

    Dunli? : R₂.Decidable Dunli
    Dunli? _ _ = _≟_ ⦃ Truthbrary.Record.Eq.EqList ⦃ eqChar ⦄ ⦄ _ _
      where
      instance
        eqChar : Truthbrary.Record.Eq.Eq Char
        eqChar = record {_≟_ = DCP._≟_}

    record IsJbovla {a} (A : Set a) : Set a
      where
      field
        t : A → Jbovla
        dun : (_≡_ on t) R₂.⇒ _≡_

  Jbovla = Jbovla.Jbovla
\end{code}

\begin{code}
  ValsiD : String → Set
  ValsiD s = Σ Jbovla $ (_≡ 𝕊₀.toList s) ∘ Jbovla.Jbovla.pShow
\end{code}

\chapter{la'oi .\AgdaRecord{Gismu}.}

\begin{code}
  module Gismu where
    record Gismu : Set
      where
      Z = Lerfu.zunsna
      K = Lerfu.karsna

      field
        v : (Z × Z × K × Z × K) ⊎ (Z × K × Z × Z × K)

      rez : Lerfu.zunsna × Lerfu.zunsna
      rez = (Data.Sum.[_,_]
              (λ (x , z , _) →  x , z)
              (λ (_ , _ , x , z , _) → x , z)
              v)

      private
        rez₁ : Lerfu.zunsna
        rez₁ = Σ.proj₁ rez

        rez₂ : Lerfu.zunsna
        rez₂ = Σ.proj₂ rez

        iv : Lerfu.zunsna → Bool
        iv = Lerfu.isVoksa ∘ Σ.proj₂ ∘ Lerfu.deconstruct

      field
        noraplis : ¬_ $ rez₁ ≡ rez₂
        vd : iv rez₁ ≡ iv rez₂

    instance
      jbovla : Jbovla.IsJbovla Gismu
      jbovla = record {
        t = λ x → record {
          valsi = v $ Gismu.v x;
          mapti = {!!}
          };
        dun = {!!}
        }
        where
        v : _ → List Lerfu.Lerfu
        v (inj₁ (z₁ , z₂ , k₁ , z₃ , k₂)) = l
          where
          l : List $ Lerfu.Lerfu
          l = Σ.proj₁ z₁ 𝕃.∷
              Σ.proj₁ z₂ 𝕃.∷
              Σ.proj₁ k₁ 𝕃.∷
              Σ.proj₁ z₃ 𝕃.∷
              Σ.proj₁ k₂ 𝕃.∷
              𝕃.[]
        v (inj₂ (z₁ , k₁ , z₂ , z₃ , k₂)) = l
          where
          l : List $ Lerfu.Lerfu
          l = Σ.proj₁ z₁ 𝕃.∷
              Σ.proj₁ k₁ 𝕃.∷
              Σ.proj₁ z₂ 𝕃.∷
              Σ.proj₁ z₃ 𝕃.∷
              Σ.proj₁ k₂ 𝕃.∷
              𝕃.[]

  Gismu = Gismu.Gismu
\end{code}

\chapter{le cnima'o co'e}

\begin{code}
  module Cnima'o where
    mutual
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

\chapter{le sampu je selma'o co'e}

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
  module NIhO where
    data NIhO' : Set

    instance
      cniTerm : Cnima'o.CniTerm NIhO'
      jbovla : Jbovla.IsJbovla NIhO'

    data NIhO'
      where
        Ni'oC : NIhO'
        UIC : Cnima'o.Cni NIhO' → NIhO'

    instance
      cniTerm = {!!}
      jbovla = record {
        t = {!!};
        dun = {!!}
        }

  NIhO = NIhO.NIhO'
\end{code}

\begin{code}
  INI'O : Set
  INI'O = I ⊎ NIhO
\end{code}

\begin{code}
  module LE
    where
    data LE' : Set

    instance
      cniTerm : Cnima'o.CniTerm LE'

    data LE'
      where
      laC : ValsiD "la" → LE'
      leC : ValsiD "le" → LE'
      loC : ValsiD "lo" → LE'
      UIC : Cnima'o.Cni LE' → LE'

    instance
      cniTerm = {!!}

  LE = LE.LE'
\end{code}

\begin{code}
  module DOI
    where

    data DOI' : Set

    instance
      cniTerm : Cnima'o.CniTerm DOI'

    data DOI'
      where
      doiC : ValsiD "doi" → DOI'
      UIC : Cnima'o.Cni DOI' → DOI'

    instance
      cniTerm = {!!}

  DOI = DOI.DOI'
\end{code}

\begin{code}
  FAhO : Set
  FAhO = {!!}
\end{code}

\begin{code}
  module KU where
    data KU' : Set
      where
        KUC : KU'

  KU = KU.KU'
\end{code}

\begin{code}
  module KUhO where
    data KUhO' : Set
      where
      KU'OC : KUhO'

  KUhO = KUhO.KUhO'
\end{code}

\begin{code}
  module FA where
    data FA : Set
      where
      FAC : Lerfu.f → Lerfu.karsna → FA

  FA = FA.FA
\end{code}

\begin{code}
  BAI  : Set
  BAI = {!!}
\end{code}

\begin{code}
  module KOhA where
    data KOhA : Set

    instance
      cniTerm : Cnima'o.CniTerm KOhA

    data KOhA
      where
      KOhA1C : Lerfu.k ⊎ Lerfu.f → Lerfu.karsna → KOhA
      KOhARC : Lerfu.a ⊎ Lerfu.i ⊎ Lerfu.u → KOhA

    instance
      cniTerm = {!!}

  KOhA = KOhA.KOhA
\end{code}

\begin{code}
  module ZOI where
    data ZOI : Set
      where
      zoiC : ValsiD "zoi" → ZOI
      la'oC : ValsiD "la'o" → ZOI

  ZOI = ZOI.ZOI
\end{code}

\begin{code}
  Cmevla : Set
  Cmevla = {!!}
\end{code}

\begin{code}
  module ZOhU where
    data ZOhU : Set
      where
      Zo'u : ZOhU

  ZOhU = ZOhU.ZOhU
\end{code}

\section{zo'e je la'oi .\F{NU}.}
ni'o ro da poi ke'a ctaipe la'oi .\F{NU}.\ zo'u ga je da sinxa lo su'o cmavo be la'oi .NU.\ldots be'o no'u lo co'e poi da ctaipe lo fancu be lo me'oi .\F{ValsiD}.\ be ke'a be'o bei la'oi .\F{NU}.

\begin{code}
  module NU where
    mutual
      data NU' : Set
        where
        NuC : NU'
        NiC : NU'
        KaC : NU'
        Pu'uC : NU'
        Du'uC : NU'
        Su'uC : NU'
        Li'iC : NU'
        Si'oC : NU'

      instance
        cniTerm : Cnima'o.CniTerm NU'
        cniTerm = {!!}

      valsiBitmuSarcu : NU' → Bool
      valsiBitmuSarcu = {!!}

  NU = NU.NU'
\end{code}

\begin{code}
  module KEI where
    mutual
      data KEI' : Set
        where

      instance
        cniTerm : Cnima'o.CniTerm KEI'
        cniTerm = {!!}

  KEI = KEI.KEI'
\end{code}

\begin{code}
  module NA where
    mutual
      data NA' : Set
        where
        NAC : NA'
        UIC : Cnima'o.Cni NA' → NA'

      instance
        cniTerm : Cnima'o.CniTerm NA'
        cniTerm = {!!}

  NA = NA.NA'
\end{code}

\begin{code}
  module POI where
    data POI' : Set
      where
      poiC : POI'
      noiC : POI'

  POI = POI.POI'
\end{code}

\chapter{le se sitsku se ctaipe}
ni'o ro da poi ke'a ctaipe la'oi .\AgdaRecord{ZoiX}\. zo'u ga je sa'u da sinxa lo me zo zoi vlapoi pe la .lojban. gi sa'u nai ru'e ga je\ldots
\begin{itemize}
	\item da me lo konkatena be lo mu'oi zoi.\ \AgdaField{ZoiX.z}\ .zoi.\ be da be'o bei ko'a goi lo mu'oi zoi.\ \AgdaField{ZoiX.v}\ .zoi.\ be da be'o bei ko'e goi lo mu'oi zoi.\ \AgdaField{ZoiX.s}\ .zoi.\ be da ge'u bei ko'a gi
	\item lo mu'oi zoi.\ \AgdaField{ZoiX.NIИ}\ .zoi.\ be da cu ctaipe lo su'u ko'a na poiklo fi ko'e
\end{itemize}

\begin{code}
  record ZoiX : Set
    where
    field
      z : ZOI
      v : Jbovla
      s : Strong
      NIИ : let v' = 𝕃.map Σ.proj₁ $ Jbovla.Jbovla.valsi v in
            ¬ Porkle v' s
\end{code}

\chapter{le zmadu be fi le ka ce'u pluja}

\begin{code}
  Na : Set

  Sumti : Set
  Selbri : Set
  record Bridi : Set
  Jek : Set
  Jufra : Set
  Prenex : Set
  DoiCl : Set
\end{code}

\chapter{zo'e je le fanmo se ctaipe pe lo bridi}

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
  module Prenex where
    mutual
      data Prenex' : Set
        where
        SumtiZo'u : Sumti → ZOhU → Prenex'
        Cons : Prenex' → Prenex' → Prenex'

      valsiBitmuSarcu : Prenex' → Bool
      valsiBitmuSarcu = {!!}

  Prenex = Prenex.Prenex'
\end{code}

\begin{code}
  module Poi
    where
    record PoiTerm (Selma'o : Set) : Set₁
      where
      field
        Term : Selma'o → Set
      
    Term : {A : Set} → ⦃ PoiTerm A ⦄ → A → Set
    Term ⦃ T ⦄ = PoiTerm.Term T

    JePoiTerm : POI → Jufra → Set
    JePoiTerm = {!!}

    KUhOTerm : POI → Jufra → Set
    KUhOTerm = {!!}

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

      clₙ : T
      clₙ = ⁇.maybe Σ.proj₂ cl₀ $ 𝕃.last clx

      field
        ku'o : Maybe $ KUhO × Σ.uncurry KUhOTerm clₙ

    instance
      poiTermPoiCl : {s : Set} → ⦃ PoiTerm s ⦄ → PoiTerm $ PoiCl s
      poiTermPoiCl = {!!}
\end{code}

\begin{code}
  module Na where
    Na' : Set
    Na' = {!!}

  Na = Na.Na'
\end{code}

\begin{code}
  module JE
    where
    JE : Set
    JE = Lerfu.j × Lerfu.karsna

    instance
      cniTerm : Cnima'o.CniTerm JE
      cniTerm = record {Term = λ _ → ⊤}

      jbovla : Jbovla.IsJbovla JE
      jbovla = record {
        t = λ {(j , (x , _)) → record {
          valsi = (_ , j) 𝕃.∷ x 𝕃.∷ 𝕃.[];
          mapti = {!!}
          }};
        dun = {!!}
        }

  JE = JE.JE
\end{code}

\begin{code}
  module Jek
    where
    record JekTerm (Selma'o : Set) : Set₁
      where
      field
        Term : Selma'o → Set

    Term : {A : Set} → ⦃ JekTerm A ⦄ → A → Set
    Term ⦃ T ⦄ = JekTerm.Term T

    data Jek' : Set
      where
      SC : Cnima'o.Cni JE → Jek'
      NaC : Na → Jek' → Jek'

    instance
      jbovla : Jbovla.IsJbovla Jek
      jbovla = {!!}

  Jek = Jek.Jek'
\end{code}

\begin{code}
  module Sumti
    where
    data Sumti' : Set

    instance
      cniTerm : Cnima'o.CniTerm Sumti'
      briTerm : Bri.BriTerm Sumti'
      poiTerm : Poi.PoiTerm Sumti'
      jekTerm : Jek.JekTerm Sumti'

    data Sumti'
      where
      KOhAC : KOhA → Sumti'
      LeSelbriC : LE → Selbri → Sumti'
      POIC : Poi.PoiCl Sumti'
           → Sumti'
      JekC : (x : Sumti')
           → Jek.Term x
           → Jek
           → Sumti'
           → Sumti'
      UIC : Cnima'o.Cni Sumti' → Sumti'
      DoiC : Sumti' → DoiCl → Sumti'

    instance
      cniTerm = record {
        Term = T
        }
        where
        T : Sumti' → Set
        T (KOhAC k) = Cnima'o.CniTerm.Term KOhA.cniTerm k
        T (POIC c) = {!!}
        T (LeSelbriC x k) = {!!}
        T (JekC x t j x₂) = {!!}
        T (UIC (Cnima'o.CniX s t c)) = {!!}
        T (DoiC s d) = {!!}
      briTerm = {!!}
      poiTerm = record {
        Term = T
        }
        where
        T : Sumti' → Set
        T (KOhAC x) = {!!}
        T (LeSelbriC x k) = {!!}
        T (POIC x) with 𝕃.last (Poi.PoiCl.cl x)
        ... | ⁇.just x2 = Σ.uncurry Poi.JePoiTerm x2
        ... | ⁇.nothing = {!!}
        T (JekC x x₁ x₂ x₃) = {!!}
        T (UIC x) = {!!}
        T (DoiC s d) = {!!}
      jekTerm = record {Term = T}
        where
        T : Sumti' → Set
        T (KOhAC x) = ⊤
        T (LeSelbriC x x₁) = {!!}
        T (POIC x) = {!!}
        T (JekC x x₁ x₂ x₃) = T x₃
        T (UIC (Cnima'o.CniX x x₁ x₂)) = T x × {!!}
        T (DoiC x x₁) = {!!}

  Sumti = Sumti.Sumti'
\end{code}

\chapter{zo'e je la'oi .\F{DoiCl}.}

\begin{code}
  module Doi where
    Cl : Set
    Cl = {!!}

  DoiCl = Doi.Cl
\end{code}

\chapter{zo'e je la'oi .\F{Selbri}.}
ni'o sa'u la'oi .\F{Selbri}.\ se ctaipe zo'e ja lo selbri co'e be bau le jbobau be la .varik.

\begin{code}
  module Selbri where
    mutual
      data Selbri' : Set
        where
        NUC : NU → Jufra → Maybe KEI → Selbri'
        GismuC : Gismu → Selbri'
        CmevlaC : Cmevla → Selbri'
        UIC : Cnima'o.Cni Selbri' → Selbri'
        DoiC : Selbri' → {!!} → Selbri'

      instance
        cniTerm : Cnima'o.CniTerm Selbri'
        cniTerm = {!!}

  Selbri = Selbri.Selbri'
\end{code}

\chapter{zo'e je la'oi .\AgdaRecord{Bridi}.}
ni'o la'oi .\AgdaRecord{Bridi}.\ se ctaipe zo'e ja lo ro bridi be bau le jbobau be la .varik.

.i sa'u nai ru'e ro da poi ke'a ctaipe la'oi .\AgdaRecord{Bridi}.\ zo'u ga je\ldots

\begin{itemize}
	\item co'e gi ga je
	\item lo mu'oi zoi.\ \AgdaField{Bridi.selbri}\ .zoi.\ be da cu selbri lo co'e be da gi ga je
	\item lo mu'oi zoi.\ \AgdaField{Bridi.terbri₁}\ .zoi.\ be da cu liste lo'i ro co'e joi ke lidne je terbri be lo co'e be da
	\item lo mu'oi zoi.\ \AgdaField{Bridi.terbri₂}\ .zoi.\ be da cu liste lo'i ro co'e joi ke se lidne je terbri be lo co'e be da
\end{itemize}

\begin{code}
  record Bridi
    where
    inductive

    ¯1↓ : ∀ {a} → {A : Set a} → List A → List A
    ¯1↓ = 𝕃.reverse ∘ 𝕃.drop 1 ∘ 𝕃.reverse

    ST : Set
    ST = Maybe (FA ⊎ BAI) × Sumti

    instance
      cniTerm⊎ : Bri.BriTerm ST
      cniTerm⊎ = record {
        Term = Bri.BriTerm.Term Sumti.briTerm ∘ Σ.proj₂
        }

    field
      selbri : Selbri
      terbri₁ terbri₂ : List $ ST
      term : All Bri.Term $ ¯1↓ terbri₁
\end{code}

\chapter{zo'e je la'oi .\F{Jufra}.}
ni'o la'oi .\F{Jufra}.\ se ctaipe zo'e ja lo ro jufra be fi le jbobau be la .varik.

.i sa'u nai ru'e ro da poi ke'a ctaipe la'oi .\F{Jufra}.\ zo'u\ldots

\begin{itemize}
	\item da du la'o zoi.\ \IC{BridiC} \B{b}\ .zoi.\ gi da sinxa lo se sinxa be la'oi .\B{b}.
\end{itemize}

\begin{code}
  module Jufra where
    mutual
      data Jufra' : Set
        where
        BridiC : Bridi → Jufra'

      valsiBitmuSarcu : Jufra' → Bool
      valsiBitmuSarcu = {!!}

      instance
        cniTerm : Cnima'o.CniTerm Jufra'
        cniTerm = {!!}

  Jufra = Jufra.Jufra'
\end{code}

\chapter{zo'e je la'oi .\D{T}.\ noi ke'a se ctaipe lo ro te gerna be le jbobau be la .varik.}

\begin{code}
  mutual
\end{code}

\section{la'oi .\D{T}.}
ni'o la .varik.\ cu co'e ja troci lo nu la'oi .\D{T}.\ se ctaipe lo ro te gerna be le jbobau be la .varik.

.i ro da poi ke'a ctaipe la'oi .\D{T}.\ zo'u ga jonai ga je\ldots

\begin{itemize}
	\item da du la'oi .\IC{NILC}.\ gi da sinxa lo kunti gi ga jonai ga je
	\item da du la'o zoi. \IC{INI'OC} \B{t} \B{n}\ .zoi.\ gi da sinxa lo konkatena be lo se sinxa be la'oi .\B{t}.\ be'o bei lo se sinxa be la'oi .\B{n}.\ gi ga jonai ga je
	\item da du la'o zoi. \IC{FA'OC} \B t \B f\ .zoi.\ gi da sinxa lo konkatena be lo se sinxa be la'oi .\B{t}.\ be'o bei lo se sinxa be la'oi .\B{f}.\ be'o bei la'oi .\B{s}.\ gi ga je
	\item da du la'o zoi. \IC{JufraC} \B t \B j \B m\ gi da sinxa lo konkatena be lo se sinxa be la'oi .\B{t}.\ be'o bei lo se sinxa be la'oi .\B{j}.
\end{itemize}

\begin{code}
    data T : Set
      where
      NILC : T
      INI'OC : T → INI'O → T
      JufraC : (t : T) → Jufra → JufraMapti t → T
      FA'OC : T → FAhO → Strong → T
\end{code}

\section{la'oi .\F{JufraMapti}.}
ni'o ro da poi ke'a ctaipe la'oi .\D{T}.\ zo'u ga jo ctaipe lo me'oi .\F{JufraMapti}.\ be da gi gerna fi lo konkatena be lo se sinxa be da be'o bei lo jufra

\begin{code}
    JufraMapti : T → Set
    JufraMapti NILC = ⊤
    JufraMapti (JufraC _ _ _) = ⊥
    JufraMapti (INI'OC _ _) = ⊤
    JufraMapti (FA'OC _ _ _) = ⊥
\end{code}

\section{la'oi .\F{valsiBitmuSarcu}.}
ni'o ro da poi ke'a ctaipe la'oi .\D{T}.\ zo'u ga jo la'o zoi.\ \IC{𝔹.true}\ .zoi.\ me'oi .\F{valsiBitmuSarcu}.\ da gi sarcu va'o zo'e fa lo nu zo'e ja lo valsi bitmu lerfu cu bitmu lo se sinxa be da be'o bei lo jufra

\begin{code}
    valsiBitmuSarcu : T → Bool
    valsiBitmuSarcu NILC = 𝔹.false
    valsiBitmuSarcu (INI'OC _ (inj₁ (I.IC x₁))) = 𝔹.false
    valsiBitmuSarcu (INI'OC _ (inj₁ (I.UIC (Cnima'o.CniX _ _ c)))) = C
      where
      C = Cnima'o.valsiBitmuSarcu c
    valsiBitmuSarcu (INI'OC _ (inj₂ NIhO.Ni'oC)) = 𝔹.false
    valsiBitmuSarcu (INI'OC _ (inj₂ (NIhO.UIC x₁))) = {!!}
    valsiBitmuSarcu (JufraC _ j _) = Jufra.valsiBitmuSarcu j
    valsiBitmuSarcu (FA'OC _ _ _) = {!!}
\end{code}

\chapter{ko'a goi le vlapoi se ctaipe no'u la'oi .\F{Vlapoi}.}
ni'o lo ro co'e se ctaipe cu ctaipe la'oi .\F{Vlapoi}. lo co'e ja sinxa be lo vlapoi be bau la .lojban.

.i ko'a jai filri'a lo nu sucta cusku tu'a zo'e je lo vlapoi

\begin{code}
  module Vlapoi where
    data Vlapoi : Set
      where
      TC : T → Vlapoi
      NUC : NU → Vlapoi
      KUhOC : KUhO → Vlapoi
      INI'OC : INI'O → Vlapoi

  Vlapoi = Vlapoi.Vlapoi
\end{code}

\part{le te tcidu gerna}

\begin{code}
module TT where
\end{code}

\begin{code}
  IsWord : String → Strong → Set
  IsWord v = (𝕊₀.toList v ≡_) ∘ 𝕃.filter (_≟_ 𝔹.false ∘ Chr._==_ ',')
\end{code}

\begin{code}
  IsWord? : R₂.Decidable IsWord
  IsWord? _ _ = _ ≟ _
\end{code}

\begin{code}
  MF : ST.Vlapoi → Strong → Set
  MF (ST.Vlapoi.TC ST.NILC) = _≡ 𝕃.[]
  MF (ST.Vlapoi.TC (ST.INI'OC t x)) = λ s → {!!} × MF (ST.Vlapoi.INI'OC x) {!!}
  MF (ST.Vlapoi.TC (ST.JufraC t x x₁)) = {!!}
  MF (ST.Vlapoi.TC (ST.FA'OC t x x₁)) = {!!}
  MF (ST.Vlapoi.KUhOC k) = {!!}
  MF (ST.Vlapoi.NUC n) = {!!}
  MF (ST.Vlapoi.INI'OC n) = {!!}
\end{code}

\begin{code}
  tolsucta : Strong → Set
  tolsucta = Σ.∃ ∘ _⍨ MF
\end{code}

\begin{code}
  tolsucta? : Decidable tolsucta
  tolsucta? = {!!}
\end{code}

\chapter{le te tcidu gerna se ctaipe}

\begin{code}
  record T : Set
    where
    field
      t : ST.T
      s : Strong
      mf : MF (ST.Vlapoi.TC t) s
\end{code}

\begin{code}
  toSucta : T → ST.T
  toSucta = {!!}
\end{code}

\chapter{le me'oi .\AgdaRecord{Read}. co'e}

\begin{code}
  R : Read T
  R = {!!}
\end{code}

\chapter{le ctaipe be le su'u mapti}

\begin{code}
  module Veritas where
    rol : ST.T → T
    rol = {!!}

    rd : (s : String)
       → (j : ⁇.Is-just $ Read.readMaybe R s)
       → 𝕊₀.toList s ≡ T.s (⁇.to-witness j)
    rd = {!!}
\end{code}
\end{document}

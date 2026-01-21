
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
  as 𝕊
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
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Truthbrary.Record.LLC
  using (
    _∈_
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

\part{le gerna}
ni'o la .varik.\ cu troci lo nu la'oi .\AgdaFunction{T}.\ cu co'e ja velcki le gerna be le jbobau be vo'a

\begin{code}
module T where
\end{code}

\chapter{le lerfu co'e\ldots noi ke'a se vasru pe'a la'oi .\AgdaModule{Lerfu}.}

\begin{code}
  module Lerfu where
    record tLerfu (c : Char) : Set
      where
      field
        nC : ℕ

      ,s = 𝕊.fromList $ 𝕃.replicate nC ','
      c' = 𝕊.fromChar c
      s = ,s 𝕊.++ c'
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
    Karsna (x , _) = x ∈ 𝕊.toList "aeiou"

    Karsna? : Decidable Karsna
    Karsna? _ = _ ≟ _
\end{code}

\begin{code}
    karsna : Set
    karsna = Σ.∃ Karsna
\end{code}

\begin{code}
    Zunsna : Lerfu → Set
    Zunsna (x , _) = x ∈ 𝕊.toList "bcdfgjklmnprstvxz"

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
        selvau : A → Σ Char tLerfu

    deconstruct : ∀ {a} → {A : Set a}
                → ⦃ Deconstructible A ⦄
                → A
                → Σ Char tLerfu
    deconstruct ⦃ D ⦄ = Deconstructible.selvau D

    instance
      deconstructibleZunsna : Deconstructible zunsna
      deconstructibleZunsna = record {selvau = Σ.proj₁}

      deconstructibleKarsna : Deconstructible karsna
      deconstructibleKarsna = record {selvau = Σ.proj₁}
\end{code}

\begin{code}
    Voksa : {c : Char} → tLerfu c → Set
    Voksa {c} t = c ∈ 𝕊.toList "abdegijlmnoruvyz"

    Voksa? : {c : Char} → Decidable $ Voksa {c}
    Voksa? {c} l = _ ≟ _

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
    record Jbovla : Set
      where
      field
        valsi : List Lerfu.Lerfu
        mapti : {!!}

    Dunli : Jbovla → Jbovla → Set
    Dunli = _≡_ Function.on (𝕃.map Σ.proj₁ ∘ Jbovla.valsi)

    Dunli? : R₂.Decidable Dunli
    Dunli? = λ _ _ → _≟_ ⦃ Truthbrary.Record.Eq.EqList ⦃ eqChar ⦄ ⦄ _ _
      where
      instance
        eqChar : Truthbrary.Record.Eq.Eq Char
        eqChar = {!!}

    pShow : Jbovla → String
    pShow = 𝕊.fromList ∘ 𝕃.map Σ.proj₁ ∘ Jbovla.valsi

    record IsJbovla {a} (A : Set a) : Set a
      where
      field
        t : A → Jbovla

  Jbovla = Jbovla.Jbovla
\end{code}

\begin{code}
  ValsiD : String → Set
  ValsiD s = Σ Jbovla $ λ v → Jbovla.pShow v ≡ s
\end{code}

\chapter{la'oi .\AgdaRecord{Gismu}.}

\begin{code}
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
\end{code}

\chapter{le cnima'o co'e}

\begin{code}
  module Cnima'o where
    mutual
      Cnima'oCo'e : Set
      Cnima'oCo'e = {!!}

      valsiBitmuSarcu : Cnima'oCo'e → Bool
      valsiBitmuSarcu = {!!}

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

    data NIhO'
      where
        Ni'oC : Lerfu.n → Lerfu.i → Lerfu.y'y → Lerfu.o → NIhO'
        UIC : Cnima'o.Cni NIhO' → NIhO'

    instance
      cniTerm = {!!}

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
      laC : Lerfu.l → Lerfu.a → LE'
      leC : Lerfu.l → Lerfu.e → LE'
      loC : Lerfu.l → Lerfu.o → LE'
      UIC : Cnima'o.Cni LE' → LE'

    instance
      cniTerm = {!!}

  LE = LE.LE'
\end{code}

\begin{code}
  FAhO : Set
  FAhO = {!!}
\end{code}

\begin{code}
  module KU where
    data KU' : Set
      where
        KUC : ValsiD "ku" → KU'

  KU = KU.KU'
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

    instance
      cniTerm = {!!}

  KOhA = KOhA.KOhA
\end{code}

\begin{code}
  module ZOI where
    ZOI : Set
    ZOI = {!!}

    valsiBitmuSarcu : ZOI → Bool
    valsiBitmuSarcu = {!!}

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

\begin{code}
  module NU where
    mutual
      data NU' : Set
        where
        NuC : ValsiD "nu" → NU'
        NiC : ValsiD "ni" → NU'
        Pu'uC : ValsiD "pu'u" → NU'
        Du'uC : ValsiD "du'u" → NU'
        Su'uC : ValsiD "su'u" → NU'
        Li'iC : ValsiD "li'i" → NU'
        Si'oC : ValsiD "si'o" → NU'

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
      poiC : Lerfu.p → Lerfu.o → Lerfu.i → POI'
      noiC : Lerfu.n → Lerfu.o → Lerfu.i → POI'

  POI = POI.POI'
\end{code}

\chapter{zo'e je le vlapoi se ctaipe}

\begin{code}
  module Vlapoi where
    record ValsiBitmu (b : Bool) : Set
      where
      field
        vl : List Lerfu.valsiBitmu
        zasti : 𝔹.if b then 𝕃.length vl ℕ.> 0 else ⊤

    Vlapoi : List $ Σ Set (λ A → A → Bool) → Set → Set
    Vlapoi 𝕃.[] b = b
    Vlapoi ((x , d) 𝕃.∷ xs) b = Σ x (ValsiBitmu ∘ d) × Vlapoi xs b

  Vlapoi = Vlapoi.Vlapoi
\end{code}

\chapter{le se sitsku se ctaipe}

\begin{code}
  record ZoiX : Set
    where
    vbs : Jbovla → Bool
    vbs = {!!}

    field
      f : let Z = ZOI , ZOI.valsiBitmuSarcu in
          let S = String , λ _ → 𝔹.true in
          Vlapoi (Z 𝕃.∷ (Jbovla , vbs) 𝕃.∷ S 𝕃.∷ 𝕃.[]) Jbovla

    v₁ : Jbovla
    v₁ = Σ.proj₁ $ Σ.proj₁ $ Σ.proj₂ f

    v₂ : Jbovla
    v₂ = Σ.proj₂ $ Σ.proj₂ $ Σ.proj₂ f

    field
      vd : Jbovla.Dunli v₁ v₂
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
        SumtiZo'u : Vlapoi 𝕃.[ Sumti , {!!} ] ZOhU → Prenex'
        Liste : Vlapoi 𝕃.[ Prenex' , valsiBitmuSarcu ] Prenex' → Prenex'

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

    Jek' : Set
    Jek' = Vlapoi 𝕃.[ Na , const 𝔹.false ] $ Cnima'o.Cni JE

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
      LeSelbriC : Vlapoi 𝕃.[ LE , {!!} ] Selbri → Sumti'
      POIC : Poi.PoiCl Sumti'
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
        T (KOhAC k) = Cnima'o.CniTerm.Term KOhA.cniTerm k
        T (POIC c) = {!!}
        T (LeSelbriC x) = {!!}
        T (JekC x t j x₂) = {!!}
        T (UIC (Cnima'o.CniX s t c)) = {!!}
      briTerm = {!!}
      poiTerm = record {
        Term = T
        }
        where
        T : Sumti' → Set
        T (KOhAC x) = {!!}
        T (LeSelbriC x) = {!!}
        T (POIC x) with 𝕃.last (Poi.PoiCl.cl x)
        ... | ⁇.just x2 = Σ.uncurry Poi.JePoiTerm x2
        ... | ⁇.nothing = {!!}
        T (JekC x x₁ x₂ x₃) = {!!}
        T (UIC x) = {!!}
      jekTerm = {!!}

  Sumti = Sumti.Sumti'
\end{code}

\chapter{zo'e je la'oi .\F{Selbri}.}
ni'o sa'u la'oi .\F{Selbri}.\ se ctaipe zo'e ja lo selbri co'e be bau le jbobau be la .varik.

\begin{code}
  module Selbri where
    mutual
      data Selbri' : Set
        where
        NUC : (Vlapoi
                ((NU , NU.valsiBitmuSarcu) 𝕃.∷ 𝕃.[ Jufra , {!!} ])
                (Maybe KEI))
            → Selbri'
        GismuC : Gismu → Selbri'
        CmevlaC : Cmevla → Selbri'
        UIC : Cnima'o.Cni Selbri' → Selbri'

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
	\item lo mu'oi zoi.\ \AgdaField{Bridi.selbri}\ .zoi.\ be da cu selbri lo co'e be da gi
	\item lo mu'oi zoi.\ \AgdaField{Bridi.terbri}\ .zoi.\ be da cu liste lo'i ro co'e joi terbri be lo co'e be da
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
      terbri : List $ ST
      term : All Bri.Term $ ¯1↓ terbri
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
	\item da du la'o zoi. \IC{INI'OC} \Sym(\Sym(\B{v} \IC{,} \AgdaUnderscore \Sym) \IC{,} \B{n}\Sym)\ .zoi.\ gi da sinxa lo konkatena be lo se sinxa be la'oi .\B{v}.\ be'o bei lo se sinxa be la'oi .\B{n}.\ gi ga jonai ga je
	\item da du la'o zoi. \IC{FA'OC} \Sym(\Sym(\B{t} \IC{,} \AgdaUnderscore \Sym) \IC{,} \Sym(\B{f} \IC{,} \AgdaUnderscore \Sym) \IC{,} \B{s}\Sym)\ .zoi.\ gi da sinxa lo konkatena be lo se sinxa be la'oi .\B{t}.\ be'o bei lo se sinxa be la'oi .\B{f}.\ be'o bei la'oi .\B{s}.\ gi ga je
	\item da du la'o zoi. \IC{JufraC} \Sym(\Sym(\B{v} \IC{,} \AgdaUnderscore \Sym) \IC{,} \B{j}\Sym) \AgdaBound{m}\ .zoi.\ gi da sinxa lo konkatena be lo se sinxa be la'oi .\B{v}.\ be'o bei lo se sinxa be la'oi .\B{j}.
\end{itemize}

\begin{code}
    data T : Set
      where
      NILC : T
      INI'OC : Vlapoi 𝕃.[ T , valsiBitmuSarcu ] INI'O
             → T
      JufraC : (v : Vlapoi 𝕃.[ T , valsiBitmuSarcu ] Jufra)
             → JufraMapti $ Σ.proj₁ $ Σ.proj₁ v
             → T
      FA'OC : let TX = T , valsiBitmuSarcu in
              Vlapoi (TX 𝕃.∷ 𝕃.[ FAhO , const 𝔹.true ]) String
            → T
\end{code}

\section{la'oi .\F{JufraMapti}.}
ni'o ro da poi ke'a ctaipe la'oi .\D{T}.\ zo'u ga jo ctaipe lo me'oi .\F{JufraMapti}.\ be da gi gerna fi lo konkatena be lo se sinxa be da be'o bei lo jufra

\begin{code}
    JufraMapti : T → Set
    JufraMapti NILC = ⊤
    JufraMapti (JufraC _ _) = ⊥
    JufraMapti (INI'OC _) = ⊤
    JufraMapti (FA'OC _) = ⊥
\end{code}

\section{la'oi .\F{valsiBitmuSarcu}.}
ni'o ro da poi ke'a ctaipe la'oi .\D{T}.\ zo'u ga jo la'o zoi.\ \IC{𝔹.true}\ .zoi.\ me'oi .\F{valsiBitmuSarcu}.\ da gi sarcu va'o zo'e fa lo nu zo'e ja lo valsi bitmu lerfu cu bitmu lo se sinxa be da be'o bei lo jufra

\begin{code}
    valsiBitmuSarcu : T → Bool
    valsiBitmuSarcu NILC = 𝔹.false
    valsiBitmuSarcu (INI'OC (x , inj₁ (I.IC x₁))) = 𝔹.false
    valsiBitmuSarcu (INI'OC (x , inj₁ (I.UIC (Cnima'o.CniX _ _ c)))) = Cnima'o.valsiBitmuSarcu c
    valsiBitmuSarcu (INI'OC (x , inj₂ (NIhO.Ni'oC _ _ _ _))) = 𝔹.false
    valsiBitmuSarcu (INI'OC (x , inj₂ (NIhO.UIC x₁))) = {!!}
    valsiBitmuSarcu (JufraC (_ , j) _) = Jufra.valsiBitmuSarcu j
    valsiBitmuSarcu (FA'OC _ ) = {!!}
\end{code}
\end{document}

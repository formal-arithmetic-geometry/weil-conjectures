/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Blowup.Affine.ChartAlgebra
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataRing
import Sheaf.AlgebraicGeometry.ReducedNormalization
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup
import Sheaf.TraceFormula.ProperFlatFiniteDenseOpen
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Blowup.FiniteDegree.Algebra

/-!
# Simultaneous integral etale-chart flatification

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose II, proof of Theorem 3.2.3,
printed p. 30; Stacks Project, Tags 081R, 05BA, 0B48, 035S and 0BAJ
(blueprint: lem-per-integral-etale-chart-flatification).

The auxiliary constructions specialize the existing scheme-theoretic image to the generic
fibre of `F ×[E] (E ×[X] X')`. This ambient scheme is canonically `F ×[X] X'`.
No choice of a closure, comparison morphism or function-field action is made.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The generic-fibre inclusion in the source after base change along `p`: Mathlib's
scheme-theoretic fibre `Scheme.Hom.fiberι` of `F ×[E] E' ⟶ E'` at the generic point of the
integral `E' = E ×[X] X'`. Source: Stacks Project, Tags 01RV and 01QR; ILO, Expose II, 3.2.3,
printed p. 30 (blueprint: lem-per-integral-etale-chart-flatification). -/
def Scheme.Hom.chartGenericFibreι
    {X E F X' : Scheme.{u}} (e : E ⟶ X) (f : F ⟶ E) (p : X' ⟶ X)
    [IsIntegral (pullback e p)] :
    (pullback.snd f (pullback.fst e p)).fiber (genericPoint (pullback e p : Scheme.{u})) ⟶
      pullback f (pullback.fst e p) :=
  (pullback.snd f (pullback.fst e p)).fiberι (genericPoint (pullback e p : Scheme.{u}))

/-- The scheme-theoretic closure of the generic fibre in the base-changed source.
It is the existing `Scheme.Hom.image`, defined by the kernel ideal sheaf; on affine opens
this is exactly the kernel of restriction to the generic fibre (Stacks, Tag 01QR).
Source: ILO, Expose II, 3.2.3, printed p. 30
(blueprint: lem-per-integral-etale-chart-flatification). -/
def Scheme.Hom.chartGenericClosure
    {X E F X' : Scheme.{u}} (e : E ⟶ X) (f : F ⟶ E) (p : X' ⟶ X)
    [IsIntegral (pullback e p)] : Scheme.{u} :=
  (Scheme.Hom.chartGenericFibreι e f p).image

/-- The canonical closed embedding of the generic closure into the base-changed source.
Source: Stacks Project, Tag 01QR; ILO, Expose II, 3.2.3, printed p. 30
(blueprint: lem-per-integral-etale-chart-flatification). -/
def Scheme.Hom.chartGenericClosureι
    {X E F X' : Scheme.{u}} (e : E ⟶ X) (f : F ⟶ E) (p : X' ⟶ X)
    [IsIntegral (pullback e p)] :
    Scheme.Hom.chartGenericClosure e f p ⟶ pullback f (pullback.fst e p) :=
  (Scheme.Hom.chartGenericFibreι e f p).imageι

/-- The canonical map from the generic closure to the modified etale chart.
Source: ILO, Expose II, 3.2.3, printed p. 30; Stacks Project, Tag 081R
(blueprint: lem-per-integral-etale-chart-flatification). -/
def Scheme.Hom.chartGenericClosureMap
    {X E F X' : Scheme.{u}} (e : E ⟶ X) (f : F ⟶ E) (p : X' ⟶ X)
    [IsIntegral (pullback e p)] :
    Scheme.Hom.chartGenericClosure e f p ⟶ pullback e p :=
  Scheme.Hom.chartGenericClosureι e f p ≫ pullback.snd f (pullback.fst e p)

/-- The canonical map from the generic closure to the original source.
It is over `E`, since both maps are projections of the same pullback.
Source: ILO, Expose II, 3.2.3, printed p. 30; Stacks Project, Tag 081R
(blueprint: lem-per-integral-etale-chart-flatification). -/
def Scheme.Hom.chartGenericClosureToSource
    {X E F X' : Scheme.{u}} (e : E ⟶ X) (f : F ⟶ E) (p : X' ⟶ X)
    [IsIntegral (pullback e p)] :
    Scheme.Hom.chartGenericClosure e f p ⟶ F :=
  Scheme.Hom.chartGenericClosureι e f p ≫ pullback.fst f (pullback.fst e p)

/-- Simultaneous flatification over a finite family of integral etale charts, without a
covering hypothesis. The modified sources are the canonical generic closures defined above.
The function-field degree uses the actual stalk map at the generic point of `F i`;
dominance identifies its source stalk with the generic stalk of `E i`. The two birational
conclusions explicitly send generic points to generic points and require bijective stalk maps.

Source: ILO, Expose II, proof of Theorem 3.2.3, printed p. 30; Stacks Project, Tags 081R,
05BA, 0B48, 035S, 035Q, 0BAJ and 07QV
(blueprint: lem-per-integral-etale-chart-flatification).

Proof (the node's steps):
1. Put $K_i=k(E_i)$ and $L_i=k(F_i)$. The generic fibre of $f_i$ is $\operatorname{Spec}L_i$.
   Indeed, on any nonempty affine open $\operatorname{Spec}B$ of $f_i^{-1}(\operatorname{Spec}A)$,
   dominance embeds $A$ in $B$ and the fraction-field lemma embeds $B$ in $L_i$. Thus
   $B\otimes_AK_i$ is a subalgebra of the finite-dimensional $K_i$-vector space $L_i$, is a
   domain, and has fraction field $L_i$. Multiplication by a nonzero element on this finite-
   dimensional domain is injective and hence surjective; it is therefore a field and equals $L_i$.
   These affine pieces all have the same generic point of $F_i$, so their generic fibres glue to
   that single spectrum. Uses: lem-sc-integral-function-field-affine-fraction.
2. The sources $E_i$ and $F_i$ are Noetherian: the given maps are of finite type, proper maps are
   of finite type, and finite type is closed under composition. Properness also makes $f_i$ quasi-
   compact and separated, hence quasi-separated. The generic-finite neighbourhood lemma applies to
   $f_i$, by Step 1, and supplies an open $V_i\subseteq E_i$ containing its generic point over
   which $f_i$ is finite. Uses: def-weil-proper-morphism, lem-sfb-finite-type-composition-base-
   change, lem-weil-pbc-finite-type-over-noetherian, lem-pc-separated-quasi-separated, lem-weil-
   pbc-generic-finite-morphism-open-neighborhood.
3. Form $W=\coprod_{i\in I}F_i$ and let $g:W\to X$ have components $e_if_i$. This is finite type
   and separated: locally on each open-and-closed component these properties hold for $e_if_i$,
   and the finite family supplies quasi-compactness; the diagonal has empty off-diagonal
   components. Generic flatness applied to $g$ gives a nonempty open $U\subseteq X$ over which $g$
   is flat and locally of finite presentation. The scheme $X$ is quasi-compact by its finite
   affine cover and quasi-separated by local Noetherianness; $U$ is quasi-compact since $X$ is
   Noetherian. Thus $X,U,g$ meet all hypotheses of the flattening theorem. If $I$ is empty take
   $W=\varnothing$ and $U=X$. Uses: lem-weil-pbc-scheme-coproduct-family, lem-sfb-finite-type-
   composition-base-change, lem-weil-pbc-proper-fp-permanence, lem-sbc-generic-flat-finite-
   presentation, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-affine-scheme-qcqs.
4. Apply flattening to $g$ and $U$. Obtain a $U$-admissible blowup $b:B\to X$ for which the strict
   transform $T$ of $W$ is flat and of finite presentation over $B$. Let $O=X\setminus V(\mathcal
   I)$ for the centre ideal. It contains $U$, and $B\times_XO\simeq O$. The blowup is proper,
   hence finite type. Its standard affine charts over an integral affine
   $\operatorname{Spec}A\subset X$ have rings $A[\mathcal I/a]\subseteq A_a$. Nonempty charts are
   domains, and their common open over $O$ is dense in every chart: localization at the nonzero
   $a$ embeds the chart ring in $A_a$. Hence $B$ is integral and has function field $k(X)$. It is
   Noetherian and all its affine coordinate rings are quasi-excellent, by finite-type stability.
   Uses: lem-trf-flattening-by-admissible-blowup, lemma-nagata-admissible-blowup-over-open, lemma-
   nagata-blowup-proper, prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring, lem-
   weil-pbc-finite-type-over-noetherian, lem-per-quasi-excellent-finite-type-stability.
5. Set $E_{i,B}=E_i\times_XB$. The open-and-closed decomposition
   $W\times_XB=\coprod_i(F_i\times_XB)$ restricts the strict transform $T$ to closed subschemes
   $T_i\subseteq F_i\times_XB$. This follows directly from the closure characterization: its
   defining ideal restricts separately on disjoint open components. Each $T_i\to B$ is flat and
   locally of finite presentation, and its restriction over $O$ is $F_i\times_XO$. Each
   $E_{i,B}\to B$ is etale. At $t\in T_i$ mapping to $z\in E_{i,B}$, the etale local-ring flatness
   lemma, applied to $M=\mathcal O_{T_i,t}$, changes flatness over $\mathcal O_{B,b(z)}$ into
   flatness over $\mathcal O_{E_{i,B},z}$. Consequently $T_i\to E_{i,B}$ is flat. Uses: lemma-
   nagata-strict-transform-closure-characterization, lemma-nagata-scheme-image-restrict-open, lem-
   weil-pbc-etale-scheme-base-change, lem-trf-etale-local-ring-flatness, def-weil-flat-morphism.
6. The morphism $T_i\to E_{i,B}$ is proper: it is the composite of its closed immersion in
   $F_i\times_{E_i}E_{i,B}$ and the base change of $f_i$. The target $E_{i,B}$ is Noetherian by
   finite-type base change and finite-type permanence; properness and the locally-Noetherian
   finite-presentation lemma therefore make $T_i\to E_{i,B}$ locally of finite presentation. Uses:
   lem-weil-pbc-proper-fp-permanence, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-
   finite-type-over-noetherian, pqf-lem-lft-fp-locnoeth.
7. The open $D_i=E_{i,B}\times_{E_i}(V_i\cap e_i^{-1}O)$ is dense in $E_{i,B}$. To check this, the
   etale map $E_{i,B}\to B$ is open, so any nonempty open in $E_{i,B}$ meets the inverse image of
   the dense open $b^{-1}O$ of $B$. That inverse image is identified with the nonempty open
   $e_i^{-1}O$ of the integral scheme $E_i$. It meets $V_i$ densely. Here $e_i^{-1}O$ is nonempty
   because the nonempty etale source $E_i$ maps openly to the integral $X$, so its image meets
   $O$. Over $D_i$, the morphism $T_i\to E_{i,B}$ is the finite map $f_i|_{V_i}$ restricted
   further. Apply the proper-flat finiteness lemma, using Step 6 for local finite presentation, to
   conclude that $T_i\to E_{i,B}$ is finite, flat and locally of finite presentation. Uses: def-
   weil-etale-morphism, lem-weil-pbc-flat-lfp-open, lem-trf-proper-flat-finite-dense-open.
8. Let $\nu:X'\to B$ be the componentwise normalization of the integral $B$. On an affine open
   $\operatorname{Spec}A\subseteq B$, it is $\operatorname{Spec}\overline A$, where $\overline A$
   is the integral closure of $A$ in $k(X)$. Quasi-excellence makes $A$ Nagata. As $A$ is a
   domain, the zero-prime clause of the Nagata definition says it is Japanese, and the degree-one
   case of that definition makes $\overline A$ a finite $A$-module. The integral-closure normality
   lemma says $\overline A$ is a normal domain with fraction field $k(X)$. Its localizations are
   normal domains. The affine normalization description and localization compatibility therefore
   give an integral normal scheme $X'$ finite over $B$. Uses: def-weil-pbc-reduced-normalization,
   lem-per-componentwise-normalization-affine-charts, lem-exc-quasi-excellent-nagata, def-weil-
   pbc-nagata-ring, def-weil-pbc-japanese-domain, lem-weil-pbc-integral-closure-finite-extension-
   normal, lem-weil-pbc-localization-normal-domain, lem-weil-pbc-integral-closure-commutes-
   localization, def-weil-finite-integral-morphism.
9. There is a nonempty open of $B$ on which $\nu$ is an isomorphism. Indeed choose a nonempty
   affine $\operatorname{Spec}A\subseteq b^{-1}O$ and finite $A$-module generators
   $c_1,\ldots,c_r$ of $\overline A\subseteq\operatorname{Frac}A$. Write $c_j=a_j/d_j$ with
   $d_j\ne0$. For $d=\prod_jd_j$ one has $\overline A_d=A_d$; localization compatibility
   identifies this with the restriction of $\nu$. Since $b$ is an isomorphism over $O$, the
   nonempty $D(d)$ is also an open of $X$. Thus $p=b\nu$ is an isomorphism on a dense open of $X$.
   It is proper since finite maps are proper and proper maps compose. It is finite type, and $X'$
   is Noetherian by finite-type permanence. Uses: lem-weil-pbc-integral-closure-commutes-
   localization, lem-weil-pbc-finite-proper, lem-weil-pbc-proper-composition, def-weil-proper-
   morphism, lem-weil-pbc-finite-type-over-noetherian.
10. For $E_i'=E_i\times_XX'$, base change gives an etale map $E_i'\to X'$, and finite-type
   permanence makes $E_i'$ Noetherian. The normal-components lemma writes it as a finite disjoint
   union of open-and-closed normal integral schemes. Let $H\subseteq X$ be the dense open on which
   $p$ is an isomorphism. Every nonempty open of $E_i'$ meets the inverse image of $p^{-1}H$,
   because its image under the open map to $X'$ is nonempty open and $p^{-1}H$ is dense in the
   integral $X'$. This inverse image is $e_i^{-1}H$, a nonempty integral open in $E_i$. It cannot
   meet two disjoint open-and-closed components. Hence $E_i'$ has exactly one component and is
   normal integral. The identification over $H$ also identifies its function field with $K_i$.
   Uses: lem-weil-pbc-etale-scheme-base-change, lem-sfb-finite-type-composition-base-change, lem-
   weil-pbc-finite-type-over-noetherian, lem-fin-etale-normal-components, def-weil-etale-morphism,
   lem-weil-pbc-flat-lfp-open, lem-sc-integral-function-field-affine-fraction.
11. Define $F_i'=T_i\times_{E_{i,B}}E_i'$ via the canonical map $E_i'\to E_{i,B}$ induced by
   $\nu$. On an affine $\operatorname{Spec}A\subseteq E_{i,B}$, write its finite inverse image as
   $\operatorname{Spec}C$. Over an affine $\operatorname{Spec}A'$ of $E_i'$ mapping there, the
   inverse image is $\operatorname{Spec}(C\otimes_AA')$; finite generators of $C$ tensor to finite
   generators. Thus $a_i:F_i'\to E_i'$ is finite. It is flat by flat base change and locally of
   finite presentation by base-change permanence, hence finite locally free by definition. The
   projections give the requested $E_i$-morphism $F_i'\to F_i$. Over the generic point of $E_i'$,
   it is $\operatorname{Spec}L_i\to\operatorname{Spec}K_i$, since both the blowup and
   normalization preserve the function fields and the strict transform agrees with $F_i$ on the
   dense open $O$. Uses: def-weil-finite-integral-morphism, lem-weil-pbc-flat-morphism-base-
   change, lem-weil-pbc-qcqs-morphism-permanence, def-pc-finite-locally-free, lem-sc-integral-
   function-field-affine-fraction.
12. The finite-locally-free pushforward lemma makes $a_{i*}\mathcal O_{F_i'}$ locally free of
   locally constant finite rank. On the connected integral $E_i'$ this rank is constant, and Step
   11 identifies its generic value with $\dim_{K_i}L_i=n_i$. On each affine trivializing
   neighbourhood $\operatorname{Spec}A$ its algebra $C$ is free of rank $n_i$. Tensoring with any
   residue field gives a vector space of dimension $n_i>0$, so its finite-dimensional nonzero
   algebra has a maximal ideal and its spectrum is nonempty. This proves surjectivity and constant
   fibre rank $n_i$. Uses: lem-sc-finite-pushforward-locally-free, def-pc-finite-locally-free.
13. On every nonempty affine $\operatorname{Spec}A\subseteq E_i'$, the finite inverse image is
   $\operatorname{Spec}C$. Flatness and the affine criterion make $C$ a flat $A$-module. Since $A$
   is a domain, the flat-torsionfree lemma shows $C\hookrightarrow C\otimes_AK_i=L_i$. Thus $C$ is
   a domain and its fraction field is $L_i$: its localization by $A\setminus\{0\}$ already equals
   that field. These affine inverse images share their generic point $\operatorname{Spec}L_i$, are
   reduced and are nonempty by Step 12. They cover $F_i'$, so $F_i'$ is integral with function
   field $L_i$. The projection to $F_i$ induces the identity on $L_i$, as may be checked on the
   common generic fibre of Step 11. Uses: def-weil-finite-integral-morphism, lem-weil-pbc-flat-
   morphism-affine-criterion, lem-trf-flat-module-torsionfree-domain, def-pc-integral-scheme.
14. Finally $F_i'$ is the scheme-theoretic closure of that generic fibre in $F_i\times_XX'$. It is
   already a closed subscheme there, by base change of the closed immersion defining $T_i$. For
   any nonempty affine open of $F_i'$, its coordinate ring embeds in $L_i$ by integrality and the
   fraction-field lemma. Therefore restriction to its generic point has zero kernel. On an affine
   open $\operatorname{Spec}R$ of the ambient scheme, with $F_i'$ cut out by $J$, this says
   $J=\ker(R\to\Gamma(G,\mathcal O_G))$, where $G$ is the intersection of the generic fibre with
   this open; if the intersection with $F_i'$ is empty then both ideals are the unit ideal. This
   is precisely the asserted affine kernel description of closure. All schemes constructed are
   finite type over $X$: $p$ is proper, the $E_i'$ are finite type over $X'$ by base change, and
   $a_i$ is finite and hence finite type. Thus the $F_i'$ are Noetherian as well. Uses: lem-weil-
   pbc-proper-fp-permanence, lem-sc-integral-function-field-affine-fraction, lemma-nagata-scheme-
   image-ideal-qc, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-proper, def-
   weil-proper-morphism, lem-weil-pbc-finite-type-over-noetherian.
-/
theorem exists_integral_etale_chart_flatification
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U))
    (I : Type v) [Finite I] (E F : I → Scheme.{u})
    (e : ∀ i : I, E i ⟶ X) (f : ∀ i : I, F i ⟶ E i)
    [∀ i : I, IsIntegral (E i)] [∀ i : I, IsIntegral (F i)]
    [∀ i : I, IsSeparated (e i)] [∀ i : I, Etale (e i)]
    [∀ i : I, LocallyOfFiniteType (e i)] [∀ i : I, QuasiCompact (e i)]
    [∀ i : I, IsProper (f i)] [∀ i : I, IsDominant (f i)]
    (n : I → ℕ) (hn : ∀ i : I, 0 < n i)
    (hfinite : ∀ i : I, ((f i).stalkMap (genericPoint (F i))).hom.Finite)
    (hdegree : ∀ i : I,
      @Module.finrank ((E i).presheaf.stalk (f i (genericPoint (F i))))
        (F i).functionField _ _
        (@Algebra.toModule _ _ _ _
          ((f i).stalkMap (genericPoint (F i))).hom.toAlgebra) = n i) :
    ∃ (X' : Scheme.{u}) (_ : IsIntegral X') (p : X' ⟶ X),
      IsNormalScheme X' ∧ IsNoetherian X' ∧ IsProper p ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (p ∣_ U)) ∧
      LocallyOfFiniteType p ∧ QuasiCompact p ∧
      ∀ i : I, ∃ (_ : IsIntegral (pullback (e i) p)),
        IsNormalScheme (pullback (e i) p) ∧ IsNoetherian (pullback (e i) p) ∧
        LocallyOfFiniteType (pullback.snd (e i) p ≫ p) ∧
        QuasiCompact (pullback.snd (e i) p ≫ p) ∧
        (pullback.fst (e i) p : pullback (e i) p ⟶ E i)
            (genericPoint (pullback (e i) p : Scheme.{u})) = genericPoint (E i) ∧
        Function.Bijective
          ((pullback.fst (e i) p).stalkMap (genericPoint (pullback (e i) p : Scheme.{u}))) ∧
        ∃ (_ : IsIntegral (Scheme.Hom.chartGenericClosure (e i) (f i) p)),
          IsNoetherian (Scheme.Hom.chartGenericClosure (e i) (f i) p) ∧
          (Scheme.Hom.chartGenericClosureMap (e i) (f i) p).IsFiniteLocallyFreeOfDegree (n i) ∧
          Surjective (Scheme.Hom.chartGenericClosureMap (e i) (f i) p) ∧
          LocallyOfFiniteType
            (Scheme.Hom.chartGenericClosureMap (e i) (f i) p ≫ pullback.snd (e i) p ≫ p) ∧
          QuasiCompact
            (Scheme.Hom.chartGenericClosureMap (e i) (f i) p ≫ pullback.snd (e i) p ≫ p) ∧
          Scheme.Hom.chartGenericClosureToSource (e i) (f i) p
              (genericPoint (Scheme.Hom.chartGenericClosure (e i) (f i) p)) =
            genericPoint (F i) ∧
          Function.Bijective
            ((Scheme.Hom.chartGenericClosureToSource (e i) (f i) p).stalkMap
              (genericPoint (Scheme.Hom.chartGenericClosure (e i) (f i) p))) := by
  sorry

end AlgebraicGeometry

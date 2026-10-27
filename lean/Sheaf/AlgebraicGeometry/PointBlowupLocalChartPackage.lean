/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Affine.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Blowup.Affine.Proper
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Local charts for a regular point blowup

Source: Stacks Project, Divisors, Tags 0804 and 0805; Algebra, Tags 00NP and 00NQ;
Resolution of Surfaces, Tag 0AGS, first proof paragraph
(blueprint: lem-sfb-point-blowup-local-chart-package).

The auxiliary definitions expand the canonical maps and the clauses of the single package.
No auxiliary existence theorem is used to choose any data.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.PointBlowupLocal

/-- The ratio-ring chart map, using the existing homogeneous chart equivalence.
Source: Stacks Project, Tag 0804
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def ratioChart {A : Type u} [CommRing A] (I : Ideal A)
    (a : A) (ha : a ∈ I) : Spec (.of (AffineBlowup.chartRing I a)) ⟶ AffineBlowup I :=
  Spec.map (CommRingCat.ofHom (AffineBlowup.homogeneousAwayEquivChart I ha).toRingHom) ≫
    AffineBlowup.chart I (reesX I a ha) (reesX_mem I a ha)

/-- Functions in ratio coordinates on an affine open chart.
Source: Stacks Project, Tags 0804 and 01HV
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def chartSections {X : Scheme.{u}} (U : X.Opens) {C : Type u} [CommRing C]
    (e : Spec (.of C) ≅ U.toScheme) : Γ(X, U) →+* C :=
  (Scheme.ΓSpecIso (.of C)).hom.hom.comp (e.hom.appTop.hom.comp U.topIso.inv.hom)

/-- The natural inclusion of the `s`-ratio ring in `A[1/(st)]`.
Source: Stacks Project, Tag 00CO and the fraction maps in Tag 0804
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def leftInclusion {A : Type u} [CommRing A] (I : Ideal A) (s t : A) :
    AffineBlowup.chartRing I s →+* Localization.Away (s * t) :=
  (IsLocalization.Away.awayToAwayRight s t).comp (AffineBlowup.chartRing I s).val.toRingHom

/-- The natural inclusion of the `t`-ratio ring in `A[1/(st)]`.
Source: Stacks Project, Tag 00CO and the fraction maps in Tag 0804
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def rightInclusion {A : Type u} [CommRing A] (I : Ideal A) (s t : A) :
    AffineBlowup.chartRing I t →+* Localization.Away (s * t) :=
  (IsLocalization.Away.awayToAwayLeft t s).comp (AffineBlowup.chartRing I t).val.toRingHom

/-- The two-chart and overlap clauses of the package on its affine Rees model.
Generators `s, t` of the maximal ideal exist, and the clauses hold for every such choice.
The chart morphisms, structure maps, fractions and restrictions are all the canonical ones.
The coefficient equation makes the overlap ring homomorphism an `A`-algebra homomorphism
without choosing a second algebra instance on a section ring.
Source: Stacks Project, Tags 0804, 01M3, 01M4 and 0AGS
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
def TwoCharts (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  (∃ s t : A, s ∈ IsLocalRing.maximalIdeal A ∧ t ∈ IsLocalRing.maximalIdeal A ∧
    IsLocalRing.maximalIdeal A = Ideal.span {s, t}) ∧
  ∀ (s t : A) (hs : s ∈ IsLocalRing.maximalIdeal A)
      (ht : t ∈ IsLocalRing.maximalIdeal A),
    IsLocalRing.maximalIdeal A = Ideal.span {s, t} → s ≠ 0 ∧ t ≠ 0 ∧
    RingTheory.Sequence.IsRegular A [s, t] ∧
    ∃ (Us Ut : (AffineBlowup (IsLocalRing.maximalIdeal A)).Opens)
      (es : Spec (.of (AffineBlowup.chartRing (IsLocalRing.maximalIdeal A) s)) ≅ Us.toScheme)
      (et : Spec (.of (AffineBlowup.chartRing (IsLocalRing.maximalIdeal A) t)) ≅ Ut.toScheme)
      (rs : Γ(AffineBlowup (IsLocalRing.maximalIdeal A), Us))
      (rt : Γ(AffineBlowup (IsLocalRing.maximalIdeal A), Ut)),
      Us ⊔ Ut = ⊤ ∧
      es.hom ≫ Us.ι = ratioChart (IsLocalRing.maximalIdeal A) s hs ∧
      et.hom ≫ Ut.ι = ratioChart (IsLocalRing.maximalIdeal A) t ht ∧
      es.hom ≫ Us.ι ≫ AffineBlowup.toSpec (IsLocalRing.maximalIdeal A) =
        Spec.map (CommRingCat.ofHom (algebraMap A _)) ∧
      et.hom ≫ Ut.ι ≫ AffineBlowup.toSpec (IsLocalRing.maximalIdeal A) =
        Spec.map (CommRingCat.ofHom (algebraMap A _)) ∧
      (chartSections Us es rs : Localization.Away s) = AffineBlowup.chartFraction s 1 t ∧
      (chartSections Ut et rt : Localization.Away t) = AffineBlowup.chartFraction t 1 s ∧
      Us ⊓ Ut = (AffineBlowup (IsLocalRing.maximalIdeal A)).basicOpen rs ∧
      Us ⊓ Ut = (AffineBlowup (IsLocalRing.maximalIdeal A)).basicOpen rt ∧
      ∃ ψ : Γ(AffineBlowup (IsLocalRing.maximalIdeal A), Us ⊓ Ut) →+*
          Localization.Away (s * t),
        (∀ a : A,
          ψ (((AffineBlowup.toSpec (IsLocalRing.maximalIdeal A)).appLE ⊤ (Us ⊓ Ut)
            le_top) ((Scheme.ΓSpecIso (.of A)).inv a)) = algebraMap A _ a) ∧
        (∀ c : Γ(AffineBlowup (IsLocalRing.maximalIdeal A), Us),
          ψ ((AffineBlowup (IsLocalRing.maximalIdeal A)).presheaf.map
            (homOfLE inf_le_left).op c) =
            leftInclusion (IsLocalRing.maximalIdeal A) s t (chartSections Us es c)) ∧
        (∀ c : Γ(AffineBlowup (IsLocalRing.maximalIdeal A), Ut),
          ψ ((AffineBlowup (IsLocalRing.maximalIdeal A)).presheaf.map
            (homOfLE inf_le_right).op c) =
            rightInclusion (IsLocalRing.maximalIdeal A) s t (chartSections Ut et c)) ∧
        ∀ z : Γ(AffineBlowup (IsLocalRing.maximalIdeal A), ⊤),
          leftInclusion (IsLocalRing.maximalIdeal A) s t
            (chartSections Us es ((AffineBlowup (IsLocalRing.maximalIdeal A)).presheaf.map
              (homOfLE le_top).op z)) =
          rightInclusion (IsLocalRing.maximalIdeal A) s t
            (chartSections Ut et ((AffineBlowup (IsLocalRing.maximalIdeal A)).presheaf.map
              (homOfLE le_top).op z))

/-- The actual fibre product `(b⁻¹V) ×_V Spec O_{T,x}`.
Source: Stacks Project, Tags 0804 and 0805
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def model (T : Scheme.{u}) (x : T) (hx : IsClosed ({x} : Set T))
    (V : T.affineOpens) (hxV : x ∈ V.1) : Scheme.{u} :=
  pullback ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap ∣_ V.1)
    (V.1.fromSpecStalkOfMem x hxV)

/-- The structural map of the local model.
Source: Stacks Project, Tag 0805
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def projection (T : Scheme.{u}) (x : T) (hx : IsClosed ({x} : Set T))
    (V : T.affineOpens) (hxV : x ∈ V.1) :
    model T x hx V hxV ⟶ Spec (T.presheaf.stalk x) :=
  pullback.snd _ _

/-- The projection of the local model to the original global blowup.
Source: Stacks Project, Tags 0804 and 0805
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
noncomputable def toBlowup (T : Scheme.{u}) (x : T) (hx : IsClosed ({x} : Set T))
    (V : T.affineOpens) (hxV : x ∈ V.1) :
    model T x hx V hxV ⟶ (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowup :=
  pullback.fst _ _ ≫
    ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap ⁻¹ᵁ V.1).ι

/-- Canonical local comparisons, including singleton-cover normalization and the fibre.
Here `e` keeps both projections, so the flat comparison used is exactly the recorded
`blowupFlatBaseChange`; `ea` is fixed by the singleton affine chart and the coefficient map.
Source: Stacks Project, Tags 0804, 0805 and 01JP
(blueprint: lem-sfb-point-blowup-local-chart-package). -/
def Comparisons (T : Scheme.{u}) (x : T) (hx : IsClosed ({x} : Set T))
    (V : T.affineOpens) (hxV : x ∈ V.1) : Prop :=
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  let A := T.presheaf.stalk x
  let J := I.comap (T.fromSpecStalk x)
  let m := IsLocalRing.maximalIdeal A
  ∃ (e : model T x hx V hxV ≅ pullback I.blowupMap (T.fromSpecStalk x))
    (ea : J.blowup ≅ AffineBlowup m)
    (hm : (J.ideal ⟨⊤, isAffineOpen_top (Spec A)⟩).map
      (Scheme.ΓSpecIso A).hom.hom = m),
    e.hom ≫ pullback.fst _ _ = toBlowup T x hx V hxV ∧
    e.hom ≫ pullback.snd _ _ = projection T x hx V hxV ∧
    J = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).ker ∧
    ea.hom ≫ AffineBlowup.toSpec m = J.blowupMap ∧
    ea.inv = AffineBlowup.hom (Scheme.ΓSpecIso A).hom.hom hm ≫
      J.blowupι ⟨⊤, isAffineOpen_top (Spec A)⟩ ∧
    (e ≪≫ (I.blowupFlatBaseChangeIso (T.fromSpecStalk x)).symm ≪≫ ea).hom ≫
      AffineBlowup.toSpec m = projection T x hx V hxV ∧
    (∃ ef : pullback (projection T x hx V hxV)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅ I.blowupMap.fiber x,
      ef.hom ≫ I.blowupMap.fiberι x =
        pullback.fst _ _ ≫ toBlowup T x hx V hxV ∧
      ef.hom ≫ I.blowupMap.fiberToSpecResidueField x = pullback.snd _ _) ∧
    (ringKrullDim A = 0 → m = ⊥ ∧ IsEmpty (model T x hx V hxV)) ∧
    (ringKrullDim A = 1 → IsIso (projection T x hx V hxV)) ∧
    (ringKrullDim A = 2 → TwoCharts A)

/-- The complete local package for a reduced closed point of a regular scheme of
dimension at most two. The `TwoCharts` clause is on the affine Rees model identified
with `model` by the specified comparison, and thus gives the stated charts on `Z`.

Source: Stacks Project, Tags 0804, 0805, 00NP, 00NQ and 0AGS
(blueprint: lem-sfb-point-blowup-local-chart-package).

Proof plan:
1. By regularity choose an affine neighbourhood $V=\operatorname{Spec}R$ with $R$ Noetherian and
regular. The closed point $x$ corresponds to a maximal ideal $\mathfrak p$, and the affine-stalk
localization theorem identifies the germ map with $R\to A=R_{\mathfrak p}$, with maximal ideal
$\mathfrak m=\mathfrak pA$. Thus $A$ is regular local. It is a nonzero domain by the
regular-local-domain theorem. By the local-dimension theorem, $\dim A$ is the supremum of lengths
of chains of irreducible closed subsets of $T$ starting at $\overline{\{x\}}$; these are among the
chains defining $\dim T$. Consequently $0\le d=\dim A\le2$, so $d\in\{0,1,2\}$.
Uses: def-weil-regular-scheme, lem-weil-pbc-affine-open-stalk-localization,
def-weil-pbc-localization-at-prime, lem-sc-regular-local-domain,
lem-sc-scheme-stalk-dimension-generalization-chains, def-kun-topological-krull-dimension.

2. The reduced closed point restricts on $V$ to $\operatorname{Spec}(R/\mathfrak p)$. The
affine-restriction clause of the Rees presentation identifies $b^{-1}V\to V$ with
$\operatorname{Proj}(\mathcal R_R(\mathfrak p))\to\operatorname{Spec}R$. Since $R$ is Noetherian,
its ideal $\mathfrak p$ is finitely generated. The affine-blowup properness theorem therefore
proves that $f:b^{-1}V\to V$ is proper. No global quasi-compactness or integrality of $T$ is
required.
Uses: lem-sfb-blowup-rees-symmetric-presentation, def-weil-pbc-noetherian-ring,
lemma-nagata-affine-blowup-proper.

3. Apply the affine-stalk localization theorem also to the affine scheme $V$ at $x$. Its germ map
identifies $\mathcal O_{V,x}$ with $R_{\mathfrak p}=A$ compatibly with the coefficient map $R\to
A$ already fixed in step 1. Thus the canonical spectrum-of-stalk morphism of $V$ is exactly
$g:\operatorname{Spec}A\to V$. The canonical-stalk-spectrum flatness theorem makes this particular
map flat. The inverse image of the centre is cut out by $\mathfrak pA=\mathfrak m$: indeed the
base-changed quotient is $A/\mathfrak pA$, since fractions from $R\setminus\mathfrak p$ are units
after base change. Apply the comparison with $X=V$. The global blowup of $V$ in its ideal
$\mathfrak p$ and $b^{-1}V$ are both identified over $V$ with $\operatorname{Proj}(\mathcal
R_R(\mathfrak p))$ by the affine-restriction clause of the Rees presentation (applied to $V$, and
to $T$ as in step 2), so the target $\operatorname{Spec}A\times_V\operatorname{Bl}_{\mathfrak
p}(V)$ is $\operatorname{Spec}A\times_V b^{-1}V$. The flat blowup comparison is then an
isomorphism $\operatorname{Bl}_{\mathfrak m}(\operatorname{Spec}A)\to\operatorname{Spec}A\times_V
b^{-1}V$. Exchange the factors by the unique morphism interchanging the two projections. Its
inverse exchanges them again, by the fibre-product universal property. Inverting the comparison
gives the required identification with $Z$.
Uses: lem-weil-pbc-affine-open-stalk-localization, lem-sbc-canonical-stalk-spectrum-flat,
def-weil-pbc-localization-at-prime, def-nagata-blowup-flat-base-change-map,
thm-nagata-blowup-flat-base-change, def-pc-fibre-product,
lem-sfb-blowup-rees-symmetric-presentation.

4. On the affine base $\operatorname{Spec}A$, the Rees presentation identifies the global blowup
with $\operatorname{Proj}(\mathcal R_A(\mathfrak m))$, which is the affine blowup by definition.
This is the comparison from the one-element affine cover: the presentation restricts to the same
affine model and the cover-independence theorem characterizes the comparison by that property.
Both structural coefficient maps are $a\mapsto a$ in degree zero; in the flat comparison the
degree-zero map is likewise the canonical coefficient identification, as specified in its
definition. Hence these are identifications over $\operatorname{Spec}A$ with the stated maps on
functions.
Uses: lem-sfb-blowup-rees-symmetric-presentation, def-nagata-affine-blowup,
prop-nagata-global-blowup-cover-independent, def-nagata-blowup-flat-base-change-map.

5. The residue field of the closed point of $\operatorname{Spec}A$ is $\kappa(x)=A/\mathfrak
m=R/\mathfrak p$: every nonzero element of the field $R/\mathfrak p$ is already invertible. Thus
both $Z\times_{\operatorname{Spec}A}\operatorname{Spec}\kappa(x)$ and the original scheme fibre
$W\times_T\operatorname{Spec}\kappa(x)$ represent the same pairs of morphisms with equal
composites to $T$. The mutually inverse maps are the maps keeping the $W$ and residue-field
projections. Their composites are identities by uniqueness in the fibre-product universal
property. This proves the canonical closed-fibre identification, including when that fibre is
empty.
Uses: def-weil-pbc-localization-at-prime, def-pc-fibre-product.

6. If $d=0$, the definition of regular locality says that $\mathfrak m$ is generated by the empty
family, so $\mathfrak m=0$. Apply the affine-blowup chart cover to $\mathfrak m=(0)$. Its only
chart ring $A[\mathfrak m/0]$ is a subalgebra of $A_0=0$, hence is the zero ring. Its spectrum is
empty because a prime ideal must be proper, and this chart covers $Z$. Therefore $Z$ is empty. If
$d=1$, choose a generator $s$ of $\mathfrak m$. By the regular-parameter theorem $s$ is a
nonzerodivisor in the nonzero domain $A$. Every $a\in\mathfrak m$ is $sc$ and $a/s=c$ in $A_s$, so
$A[\mathfrak m/s]$ is exactly the image of $A$, and $A\to A_s$ is injective: $s^na=0$ implies
$a=0$. The single chart in the chart-cover theorem is consequently $\operatorname{Spec}A$, with
coefficient map the identity, and its chart map is an isomorphism over $\operatorname{Spec}A$ by
the affine chart theorem. Since it covers $Z$, the structural map $Z\to\operatorname{Spec}A$ is an
isomorphism.
Uses: def-weil-regular-scheme, lem-weil-pbc-regular-local-generators-regular-sequence,
prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring,
def-weil-ring-localization-away, prop-nagata-affine-blowup-chart.

7. Suppose $d=2$ and choose $s,t$ generating $\mathfrak m$, as permitted by regular locality. The
regular-parameter theorem makes $(s,t)$ a regular sequence. Both elements are nonzero: the first
acts injectively on nonzero $A$, and the second acts injectively on nonzero $A/(s)$; zero could
not do so. Applying the chart-cover theorem to $(s,t)$ gives $U_s=\operatorname{Spec}A[\mathfrak
m/s]$ and $U_t=\operatorname{Spec}A[\mathfrak m/t]$, as $A$-schemes. Their maps into Proj are the
chart maps $\chi_s,\chi_t$ onto $D_+(su),D_+(tu)$, where $u$ is the Rees variable. The defining
chart isomorphism sends $au^n/(su)^n$ to $a/s^n$ and in degree zero sends $a$ to $a$. In
particular it sends $(tu)/(su)$ to $t/s$, with the analogous formula for $s/t$.
Uses: def-weil-regular-scheme, lem-weil-pbc-regular-local-generators-regular-sequence,
def-weil-pbc-regular-sequence, prop-nagata-affine-blowup-chart-cover,
prop-nagata-affine-blowup-chart, def-nagata-affine-blowup-chart-map,
def-nagata-homogeneous-away-to-chart.

8. The intersection of the two Proj opens is $D_+((su)(tu))$. In the localization at $su$, the
equation $tu=(su)((tu)/(su))$ shows that avoiding $tu$ is equivalent to avoiding $(tu)/(su)$: $su$
is already invertible. Under $\chi_s$ this is $D_{U_s}(t/s)$; exchanging $s,t$ gives
$D_{U_t}(s/t)$. The affine-basic-open sections theorem identifies its section ring $B$ with
$(C_s)_{t/s}$ and with $(C_t)_{s/t}$, with the natural localization restriction maps. The Proj
overlap equivalences are induced by further homogeneous localization, so the two identifications
use the same fractions on the intersection, as specified by the Proj chart-ring coherence theorem
and the definition of the Proj restriction maps.
Uses: lem-weil-pbc-projective-spectrum-basic-opens-basis, def-nagata-homogeneous-away-to-chart,
lem-weil-pbc-affine-open-section-vanishing-prime, lemma-nagata-proj-chart-ring-cocycle,
def-pc-proj.

9. The inclusions $C_s\subseteq A_s\to A_{st}$ and $C_t\subseteq A_t\to A_{st}$ are the natural
fraction maps. In $A_{st}$ both $s$ and $t$ are units: $s^{-1}=t/(st)$ and $t^{-1}=s/(st)$. Thus
the first inclusion extends to $B=(C_s)_{t/s}$ by $c/(t/s)^n\mapsto c(s/t)^n$. This respects
localization relations since $t/s$ is a unit. On $C_t$ it is the natural inclusion: $C_t=A[s/t]$,
because for $a=rs+qt\in\mathfrak m$ one has $a/t=r(s/t)+q$. The overlap sends the generator $s/t$
to the inverse of $t/s$, and fixes $A$, so the composites agree on these algebra generators. Hence
this is the required $A$-algebra map $B\to A_{st}$. The restrictions of a section of $Z$ to the
two charts have the same restriction to their intersection by the presheaf composition law;
applying this one map proves equality of their images in $A_{st}$.
Uses: def-nagata-blowup-chart-ring, def-weil-ring-localization-away, def-pc-proj,
lemma-nagata-proj-chart-ring-cocycle.
-/
theorem point_blowup_local_chart_package (T : Scheme.{u}) (hregular : IsRegularScheme T)
    (hdim : topologicalKrullDim T ≤ 2) (x : T) (hx : IsClosed ({x} : Set T)) :
    IsRegularLocalRing (T.presheaf.stalk x) ∧ IsDomain (T.presheaf.stalk x) ∧
    (ringKrullDim (T.presheaf.stalk x) = 0 ∨ ringKrullDim (T.presheaf.stalk x) = 1 ∨
      ringKrullDim (T.presheaf.stalk x) = 2) ∧
    ∃ (V : T.affineOpens) (hxV : x ∈ V.1),
      IsNoetherianRing Γ(T, V.1) ∧ IsRegularRing Γ(T, V.1) ∧
      (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal ∧
      (∃ e : Localization.AtPrime (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal ≃+*
          T.presheaf.stalk x,
        e.toRingHom.comp (algebraMap _ _) = (T.presheaf.germ V.1 x hxV).hom) ∧
      Ideal.map (T.presheaf.germ V.1 x hxV).hom (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal =
        IsLocalRing.maximalIdeal (T.presheaf.stalk x) ∧
      IsProper ((Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).blowupMap ∣_ V.1) ∧
      Comparisons T x hx V hxV := by
  sorry

end AlgebraicGeometry.PointBlowupLocal

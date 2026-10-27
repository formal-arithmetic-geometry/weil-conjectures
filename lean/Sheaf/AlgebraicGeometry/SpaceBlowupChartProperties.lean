/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Blowup.Affine.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import WeilConjectures.Blowup.Affine.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import WeilConjectures.Blowup.Affine.Principalization
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

/-! # Properties of algebraic-space blowups

Source: Stacks Project, spaces-divisors.tex, Tags 084B, 085Q, 085R, 085S, 085T,
085Z and 083S; descent.tex, Tags 03DX and 05VG
(blueprint: lem-sfb-space-blowup-chart-properties).

The conclusion uses the existing affine-etale blowup presentation, not a new blowup.
The structures below spell out the conclusion's comparisons and boundary. They are
outputs of the theorem, not extra assumptions on the ideal or the space.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical chart Spec R[K/a] -> Proj(Rees K), using the existing homogeneous
localization comparison, including when a is a zero divisor in R.
Source: Stacks, Tag 085R (blueprint: lem-sfb-space-blowup-chart-properties). -/
def spaceBlowupAffineChart {R : Type u} [CommRing R] (K : Ideal R) (a : K) :
    Spec (.of (AffineBlowup.chartRing K a.val)) ⟶ AffineBlowup K :=
  Spec.map (CommRingCat.ofHom (AffineBlowup.homogeneousAwayEquivChart K a.property).toRingHom)
    ≫ AffineBlowup.chart K
      ⟨Polynomial.monomial 1 a.val,
        reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using a.property)⟩
      (fun k hk ↦ by
        change (Polynomial.monomial 1 a.val).coeff k = 0
        rw [Polynomial.coeff_monomial, if_neg hk.symm])

/-- The flat restriction conclusion. The epimorphic factorization specifies exactly
im(h^*K -> O_A). For every presentation over A, the cartesian comparison is unique.
Scheme tests additionally use the ordinary scheme blowup of the corresponding
finite-type Zariski ideal. The chart V is identified with W by an over-S isomorphism
whose Yoneda map equals its chart map; thus the ideal is the restriction of J to W.
This uses the definition-owned blowupChartIdeal API on an actual scheme chart.
Source: Stacks, Tags 085S, 085R, 03DX and 05VG
(blueprint: lem-sfb-space-blowup-chart-properties). -/
structure SpaceBlowupFlatComparisons {S : Scheme.{u}} {T : AlgebraicSpace S}
    (K : QuasiCoherentIdeal T) (B : BlowupPresentation K) where
  flat (A : AlgebraicSpace S) (h : A ⟶ T) (hh : MapIsFlat h) :
    ∃ J : QuasiCoherentIdeal A,
      (J.val : A.Modules).IsFiniteType ∧
      (∃ q : (moduleTensorPullback h).obj (K.val : T.Modules) ⟶ (J.val : A.Modules),
        Epi q ∧ q ≫ J.val.arrow = idealTensorMap h K) ∧
      Nonempty (BlowupPresentation J) ∧
      ∀ BA : BlowupPresentation J, ∃! b : BA.space ⟶ B.space,
        IsPullback b BA.projection B.projection h
  openRestriction (A : AlgebraicSpace S) (h : A ⟶ T)
      (hh : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) h.hom.hom) :
    ∃ J : QuasiCoherentIdeal A,
      (J.val : A.Modules).IsFiniteType ∧
      (∃ q : (moduleTensorPullback h).obj (K.val : T.Modules) ⟶ (J.val : A.Modules),
        Epi q ∧ q ≫ J.val.arrow = idealTensorMap h K) ∧
      Nonempty (BlowupPresentation J) ∧
      ∀ BA : BlowupPresentation J, ∃! b : BA.space ⟶ B.space,
        IsPullback b BA.projection B.projection h
  scheme (W : Over S) (g : schemeSpace W ⟶ T) (hg : MapIsFlat g) :
    ∃ J : QuasiCoherentIdeal (schemeSpace W),
      (∃ q : (moduleTensorPullback g).obj (K.val : T.Modules) ⟶
          (J.val : (schemeSpace W).Modules),
        Epi q ∧ q ≫ J.val.arrow = idealTensorMap g K) ∧
      ∃ (V : (schemeSpace W).EtaleSite) (e : V.obj.left ≅ W),
        V.obj.hom = yoneda.map e.hom ∧
        (blowupChartIdeal J V).toModules.IsFiniteType ∧
        ∃ q : yoneda.obj (Over.mk
            ((blowupChartIdeal J V).blowupMap ≫ V.obj.left.hom)) ⟶ B.space.obj.obj,
          IsPullback q (yoneda.map (Over.homMk
            (U := Over.mk ((blowupChartIdeal J V).blowupMap ≫ V.obj.left.hom))
            (V := V.obj.left) (blowupChartIdeal J V).blowupMap (by rfl)))
            B.projection.hom.hom (V.obj.hom ≫ g.hom.hom)

/-- The complement is characterized on all etale tests by K being the unit ideal.
Its lift is precisely the inverse-image open and is an isomorphism over that complement.
The exceptional closed subspace is the inverse image of V(K), with ideal the image of
p^*K -> O_B. Regular principality is local at every point of every etale chart.
The monomorphism is the full small-etale structure-sheaf map into the open direct image,
not merely density on topological points.
Source: Stacks, Tags 085T, 083S and 03MB
(blueprint: lem-sfb-space-blowup-chart-properties). -/
structure SpaceBlowupBoundary {S : Scheme.{u}} {T : AlgebraicSpace S}
    (K : QuasiCoherentIdeal T) (B : BlowupPresentation K) where
  complement : AlgebraicSpace S
  inclusion : complement ⟶ T
  openImmersion :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) inclusion.hom.hom
  complement_test (V : T.EtaleSite) :
    (∃ a : yoneda.obj V.obj.left ⟶ complement.obj.obj,
      a ≫ inclusion.hom.hom = V.obj.hom) ↔ idealSectionImage K.val.arrow V = ⊤
  lift : complement ⟶ B.space
  restriction : IsPullback lift (𝟙 complement) B.projection inclusion
  lift_open : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) lift.hom.hom
  schematicallyDense : Mono (moduleStructureMap lift)
  centre : ClosedSubspace T
  centreIdeal : kernelSubobject (moduleStructureMap centre.val.arrow) = K.val
  exceptional : ClosedSubspace B.space
  toCentre : (exceptional.val : AlgebraicSpace S) ⟶ (centre.val : AlgebraicSpace S)
  exceptional_cartesian : IsPullback toCentre exceptional.val.arrow
    centre.val.arrow B.projection
  exceptionalIdeal : QuasiCoherentIdeal B.space
  exceptional_kernel :
    exceptionalIdeal.val = kernelSubobject (moduleStructureMap exceptional.val.arrow)
  exceptional_image :
    ∃ q : (moduleTensorPullback B.projection).obj (K.val : T.Modules) ⟶
        (exceptionalIdeal.val : B.space.Modules),
      Epi q ∧ q ≫ exceptionalIdeal.val.arrow = idealTensorMap B.projection K
  cartier (V : B.space.EtaleSite) (y : B.space.etaleForget.obj V) :
    ∃ W : (B.space.etaleForget.obj V).affineOpens, y ∈ W.1 ∧
      ((idealSectionImage (idealTensorMap B.projection K)
        ((B.space.schemeOpens V).obj W.1)).comap
          ((B.space.schemeOpensRingHom V).app (op W.1)).hom :
          Ideal Γ(B.space.etaleForget.obj V, W.1)).IsRegularPrincipal

/-- The scheme test is the affine Rees Proj, with its complete affine chart cover.
Source: Stacks, Tag 085R (blueprint: lem-sfb-space-blowup-chart-properties). -/
structure SpaceBlowupAffineComparisons {S : Scheme.{u}} {T : AlgebraicSpace S}
    (K : QuasiCoherentIdeal T) (B : BlowupPresentation K) where
  comparison (V : T.EtaleSite) [IsAffine V.obj.left.left] :
    ∃ (P : Over S)
      (e : P.left ≅ AffineBlowup ((blowupChartIdeal K V).ideal
        ⟨(⊤ : V.obj.left.left.Opens), isAffineOpen_top V.obj.left.left⟩))
      (a : P ⟶ V.obj.left) (q : yoneda.obj P ⟶ B.space.obj.obj),
      a.left = e.hom ≫ AffineBlowup.toSpec _ ≫ V.obj.left.left.isoSpec.inv ∧
      IsPullback q (yoneda.map a) B.projection.hom.hom V.obj.hom
  charts (V : T.EtaleSite) [IsAffine V.obj.left.left] :
    (∀ a : (blowupChartIdeal K V).ideal
        ⟨(⊤ : V.obj.left.left.Opens), isAffineOpen_top V.obj.left.left⟩,
      IsOpenImmersion (spaceBlowupAffineChart _ a)) ∧
    ∀ x : AffineBlowup ((blowupChartIdeal K V).ideal
        ⟨(⊤ : V.obj.left.left.Opens), isAffineOpen_top V.obj.left.left⟩),
      ∃ (a : (blowupChartIdeal K V).ideal
        ⟨(⊤ : V.obj.left.left.Opens), isAffineOpen_top V.obj.left.left⟩)
        (y : Spec (.of (AffineBlowup.chartRing _ a.val))),
        spaceBlowupAffineChart _ a y = x

/-- Finite-type algebraic-space blowups exist, are representable and proper, commute
canonically with flat base change (including open restriction and ordinary scheme
models), are isomorphisms off their centres, have effective Cartier exceptional
boundary with schematically dense complement, and have the asserted affine Rees charts.
These properties hold for every existing blowup presentation; there is no atlas,
Noetherian, reducedness, quasi-compactness or separation hypothesis.
Source: Stacks Project, spaces-divisors.tex, Tags 084B, 085Q, 085R, 085S, 085T,
085Z and 083S; descent.tex, Tags 03DX and 05VG
(blueprint: lem-sfb-space-blowup-chart-properties).

Proof:
1. Form the quasi-coherent Rees algebra, using the affine-chart calculus
   lem-sfb-space-qcoh-affine-chart-calculus for powers and tensor products, and
   lem-sfb-space-qcoh-kernels-colimits for sums. Apply
   lem-sfb-space-relative-proj-scheme-tests. On affine etale charts use
   lem-trf-space-chart-adjunction-tensor-realization and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, then the ordinary
   lemma-nagata-relative-proj-exists. This gives a BlowupPresentation.
2. For flat h, the degreewise maps b tensor x -> b h-sharp(x) identify the pulled
   Rees algebra with the Rees algebra of the image ideal, by
   def-nagata-flat-pullback-rees-map and lemma-nagata-flat-pullback-rees. Refine
   charts using lem-trf-space-fibre-products-etale-covers; tensor composition and
   restriction identify these maps. Their inverses glue by uniqueness.
3. Relative-Proj base change gives the cartesian comparison, including open
   restrictions. The Zariski/etale equivalence and
   lem-sfb-scheme-etale-module-exact-finiteness-comparison identify the finite-type
   scheme ideal and ordinary scheme blowup. Comparisons agree on further charts.
4. Each affine etale model is proper by lemma-nagata-affine-blowup-proper.
   Apply lem-sfb-space-proper-base-change, lem-sfb-space-flat-proper-fp-locality
   on every scheme test, and lem-sfb-space-proper-arbitrary-scheme-tests.
5. prop-nagata-affine-blowup-chart-cover, prop-nagata-affine-blowup-chart and
   def-nagata-affine-blowup-chart-map give the covering by Spec R[K/a]. The
   homogeneousAwayEquivChart identifies these with the standard Proj opens.
6. lemma-nagata-affine-blowup-complement gives the isomorphism off V(K);
   the inverses agree on overlaps and glue. No density of this open in T is used.
7. lem-sfb-space-ideal-closed-subspace-correspondence identifies the exceptional
   ideal with im(p^*K -> O_B). On R[K/a],
   lemma-nagata-chart-extended-ideal-principal gives K R[K/a] = (a), and
   lemma-nagata-chart-generator-regular says a is regular, even if it was a zero
   divisor in R. This is precisely the Cartier condition and the inverse-image centre.
8. On every affine etale test of this chart, etale flatness
   lem-weil-pbc-etale-algebra-flat and lem-trf-flat-tensor-preserves-injection keep
   a regular. A function vanishing on D(a) is killed by a power of a, hence zero.
   Refine every etale test by these affine tests using
   lem-trf-space-representable-etale-scheme-tests. Sheaf separatedness then gives
   the monomorphism on the full small etale site. The same argument gives uniqueness
   of flat comparison maps: they agree off the centre, and their equalizer is closed
   because the blowup is separated. Its ideal is zero by this injectivity argument.
   The empty space, unit ideal, zero ideal and nilpotent ideals are all included. -/
theorem exists_space_blowup_chart_properties {S : Scheme.{u}} {T : AlgebraicSpace S}
    (K : QuasiCoherentIdeal T) (hK : (K.val : T.Modules).IsFiniteType) :
    Nonempty (BlowupPresentation K) ∧
      ∀ B : BlowupPresentation K,
        IsRepresentable B.projection.hom.hom ∧ MapIsProper B.projection ∧
          Nonempty (SpaceBlowupFlatComparisons K B) ∧
          Nonempty (SpaceBlowupBoundary K B) ∧ Nonempty (SpaceBlowupAffineComparisons K B) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

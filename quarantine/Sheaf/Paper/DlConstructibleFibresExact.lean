/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.PointProEtaleSectionsExact
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.Paper.PointSectionsFiniteness
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.FieldCohomologyScalarExtension
import Sheaf.Paper.ContinuousIntegralScalarExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Topology.NoetherianGoodStratificationRefinement
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.RingTheory.ProEtale.WLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import Mathlib.CategoryTheory.Sites.LocalProperties
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Sheaf.Paper.SfWeilSheafComplex
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Sheaf.Paper.CondensedERealization
import Sheaf.Paper.StratifiedLatticeRank
import Sheaf.RingTheory.IndPrincipalZariski

/-! # Exact and jointly conservative constructible adic coefficient fibres

Source: Bhatt--Scholze, Section 6.8, Proposition 6.8.4, Corollary 6.8.5,
Lemma 6.8.7 and Proposition 6.8.14; Stacks Project Tag 03PU at finite etale level
(blueprint: lem-dl-a1-constructible-fibres-exact).

Fibres use the recorded completed derived pullback, point-section functor and
coefficient cohomology, on the literal common-stage constructible heart. The local
clause uses compatible objects on all separated finite-type opens, allowing the
coefficient stage to vary between opens.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v s w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)

/-- The geometric coefficient fibre is H^0 Fib_s Ly^* on the actual constructible heart.
Points are arbitrary scheme maps from Spec k; no linearity over k is imposed on them.
Source: BS 6.8.14, with the point functor of blueprint order 1509
(blueprint: lem-dl-a1-constructible-fibres-exact). -/
def dlAdicHeartFibre (T : Over (Spec (.of D.k))) (x : Spec (.of D.k) ⟶ T.left) :
    sfCommonStageHeart c.l T.left c.Qbar ⥤ ModuleCat.{u} c.Qbar :=
  (sfCommonStageHeartProperty c.l T.left c.Qbar).ι ⋙
    @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ x
      (dlAdicGeometricResidueInvertible D c (Spec (.of D.k)))
      (dlAdicGeometricResidueInvertible D c T.left) ⋙
    pointQbarFibre D c.l c.different c.Qbar ⋙
    DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0

/-- All fibre assertions, including finite-dimensionality, exactness, joint reflection
of isomorphisms, detection of zero maps and the short exactness criterion. The module
criterion uses injectivity, Function.Exact and surjectivity of the actual linear maps.
Source: BS 6.8.4--6.8.7 and 6.8.14
(blueprint: lem-dl-a1-constructible-fibres-exact). -/
def DlAdicFibreAssertions {C : Type v} [Category.{s} C] [Preadditive C]
    (T : Scheme.{u}) (F : (Spec (.of D.k) ⟶ T) → (C ⥤ ModuleCat.{u} c.Qbar)) : Prop :=
  (∀ x, (F x).Additive ∧ PreservesFiniteLimits (F x) ∧ PreservesFiniteColimits (F x) ∧
    ∀ M : C, FiniteDimensional c.Qbar ((F x).obj M)) ∧
  (∀ (M N : C) (f : M ⟶ N), (∀ x, IsIso ((F x).map f)) → IsIso f) ∧
  (∀ (M N : C) (f : M ⟶ N), (∀ x, (F x).map f = 0) → f = 0) ∧
  (∀ S : ShortComplex C, S.ShortExact ↔ ∀ x,
    Function.Injective ((F x).map S.f) ∧
      Function.Exact ((F x).map S.f) ((F x).map S.g) ∧
        Function.Surjective ((F x).map S.g))

/-- Local exactness on every separated finite-type open covering of the k0-scheme.
The source is locally finite type over k0, with no quasi-compactness or separatedness
assumption. The cover index is arbitrary and may be empty on the empty scheme.
Source: BS 6.8.6, 6.8.7 and Remark 6.8.15
(blueprint: lem-dl-a1-constructible-fibres-exact). -/
def DlAdicLocalExactness : Prop :=
  ∀ (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
    (I : Type w) (U : I → DlAdicFiniteOpen D T₀),
    (⨆ i : I, (U i).val) = ⊤ →
    ∀ S : ShortComplex (DlLocallyConstructibleAdicHeart D c T₀),
      S.ShortExact ↔ ∀ i : I,
        (S.map (dlAdicLocalEvaluation D c T₀ (U i))).ShortExact

/-- Geometric coefficient fibres are exact and jointly conservative on the constructible
common-stage adic heart, detect zero arrows and short exact sequences, and have the same
properties on constructible Weil sheaves after forgetting their Weil structure.
Exactness for locally constructible adic sheaves is local on separated finite-type opens.
Source: BS Section 6.8 and Stacks Tag 03PU
(blueprint: lem-dl-a1-constructible-fibres-exact).

Proof:
1. Finite type over the algebraic closure gives a noetherian finite-dimensional scheme.
A k-linear point is a section of its separated structure map, hence a closed immersion
(lem-weil-pbc-section-separated-closed-immersion). An arbitrary Spec k point differs
by a self-embedding of k; it permutes each finite subfield and is an automorphism.
2. The immersion completed-pullback comparison identifies integral pullback with exact
ordinary inverse image. The integral stratified-perfect characterization identifies
the integral category used here with the bounded constructible complete category.
Rational transport and the integral-representative standard classes imply t-exactness.
3. At Spec k, pro-etale sections are exact and commute with cohomology. Localization is
exact. Point-section finiteness gives bounded finite-dimensional E-cohomology. The
heart short-exact/triangle correspondence makes the degree-zero fibre exact.
4. Common-stage calculus descends every finite diagram and equality. Truncations commute
with finite scalar extension, so take H^0 of representatives and compute kernels and
cokernels from cones at one stage. The point scalar comparisons and cohomology/scalar
comparison identify the resulting Qbar fibre with the scalar-extended E-vector space.
5. The condensed E-realization is extension to the continuous coefficient ring. Its
integral extension is exact; hence the standard halves map to ambient standard halves.
The lisse rational realization identifies restrictions to the finite strata with
locally free finite-rank continuous-coefficient sheaves.
6. Refine to a good stratification. Each reduced stratum has finitely many open connected
components. Each nonempty component has a k-point by the affine Nullstellensatz.
The stratified-lattice rank lemma makes its lisse rank constant on that component.
7. If all fibres vanish, faithful E-to-Qbar scalar extension makes the tested E-fibre
zero. The normalized lisse realization identifies it with point sections. A trivializing
pro-etale cover of Spec k has a section by the w-contractible geometric criterion,
since k is strictly henselian. Thus point sections of a rank-r lisse sheaf are E^r.
The rank is zero on every component. Sheaf-cover locality and the realization
equivalence give zero restriction on each stratum.
8. Remove open strata successively from a finite good stratification. The open-closed
triangle and induction show the object is zero. The empty scheme is the base case.
9. Exact fibres preserve kernels, cokernels and images. Fibrewise invertibility forces
the kernel and cokernel to vanish, giving joint conservativity; fibrewise zero forces
the image to vanish, giving zero-map detection.
10. Apply joint reflection of short exactness to these exact, jointly conservative
functors; module short exactness is injectivity, middle exactness and surjectivity.
11. In Frobenius-fixed pairs, kernels and cokernels inherit their invertible Weil maps
from t-exact Frobenius pullback. Forgetting creates them and is faithful, exact and
reflects exactness, giving all Weil assertions.
12. Restriction to an open is exact by step 2. The left kernel, middle homology and
right cokernel restrict to the corresponding defects. Test a locally constructible
defect on separated affine finite-type opens, take finite subcovers of intersections,
and use common-stage calculus and the continuous-coefficient realization to apply
sheaf-cover locality. Each defect is zero iff its cover restrictions are zero.
No global finite field of definition on a non-quasi-compact scheme is required. -/
theorem dlConstructibleFibresExact (_ι : c.Qbar ≃+* ℂ) :
    (∀ (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
      [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom],
      DlAdicFibreAssertions D c (D.geometricFiber Y₀).left
        (dlAdicHeartFibre D c (D.geometricFiber Y₀)) ∧
      (qbarCurveWeilHeartForget D c.l c.different c.Qbar Y₀).Additive ∧
      PreservesFiniteLimits (qbarCurveWeilHeartForget D c.l c.different c.Qbar Y₀) ∧
      PreservesFiniteColimits (qbarCurveWeilHeartForget D c.l c.different c.Qbar Y₀) ∧
      DlAdicFibreAssertions D c (D.geometricFiber Y₀).left
        (fun x ↦ qbarCurveWeilHeartForget D c.l c.different c.Qbar Y₀ ⋙
          dlAdicHeartFibre D c (D.geometricFiber Y₀) x)) ∧
    DlAdicLocalExactness.{u, w} D c := by
  sorry

end WeilConjectures

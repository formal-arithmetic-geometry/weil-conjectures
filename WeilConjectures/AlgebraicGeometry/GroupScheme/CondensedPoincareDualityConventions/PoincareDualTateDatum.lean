/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Data.Finset.Max
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Dual and Tate data in the condensed Poincare conventions

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/sec-frobenius/
sk-def-sf-weil-complexes/def-pod-dual-tate-datum.md (blueprint: def-pod-dual-tate-datum).

The three-arrow dual and inverse-tensorator twisted dual reuse the recorded strict-Weil
constructions. The final statements record the constant-unit normalization and its
ordinary and compact-support global Frobenius iterates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedPoincareDualityConventions

variable (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)

set_option quotPrecheck false

local notation "Λ" => (P.presentation c).obj P.ell
local notation "g" =>
  (show P.X ≅ P.X from
    ⟨(P.datum.geometricFrobenius P.X₀).hom, (P.datum.geometricFrobenius P.X₀).inv,
      (P.datum.geometricFrobenius P.X₀).hom_inv_id,
      (P.datum.geometricFrobenius P.X₀).inv_hom_id⟩)

/-- The coefficient-dual datum for a perfect strict Weil complex. The existing definition
is exactly the evaluation comparison, then RHom(id, phi_A), then RHom(phi_K^-1, id).
Source: the displayed composite (blueprint: def-pod-dual-tate-datum). -/
def perfectDualDatum (K : P.strictWeil c)
    (_hK : IsPerfectOnCoefficientSite Λ P.X K.carrier.obj) :
    (StrictWeilCondensed.action Λ g).obj (P.coefficientDual c K.carrier) ≅
      P.coefficientDual c K.carrier :=
  StrictWeilCondensed.dualDatum Λ g K.carrier.obj ((ObjectProperty.ι _).mapIso K.str)

/-- The twisted dual uses the inverse tensorator, the coefficient-dual datum, and tau_r.
The Tate factor is the existing root-normalized datum, whose geometric-point scalar is
q^(-r), hence q^r for -r, by StrictWeilCondensed.tatePull_scalar.
Source: the twisted-dual sentence (blueprint: def-pod-dual-tate-datum). -/
def perfectTwistedDualDatum (K : P.strictWeil c)
    (hK : IsPerfectOnCoefficientSite Λ P.X K.carrier.obj) (r : ℤ) :
    (StrictWeilCondensed.action Λ g).obj
        (P.coefficientDual c K.carrier ⊗ (P.tateWeil c r).carrier.obj) ≅
      P.coefficientDual c K.carrier ⊗ (P.tateWeil c r).carrier.obj :=
  StrictWeilCondensed.tensorDatum Λ g (P.perfectDualDatum c K hK)
    ((ObjectProperty.ι _).mapIso (P.tateWeil c r).str)

/-- The constant coefficient complex with its canonical coefficient-unit datum.
Source: the constant-sheaf sentence (blueprint: def-pod-dual-tate-datum). -/
def constantUnitWeil : P.strictWeil c :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ⟨𝟙_ _, smoothTraceUnit_mem P.ell (P.presentation c) P.X⟩
    (ObjectProperty.isoMk _ (Functor.Monoidal.εIso (StrictWeilCondensed.action Λ g)).symm)

/-- The dual constant complex uses the existing contragredient datum, not an arbitrary
Weil structure transferred from the unit.
Source: the constant-sheaf sentence (blueprint: def-pod-dual-tate-datum). -/
def constantDualWeil : P.strictWeil c :=
  StrictWeilCondensed.dualComplex Λ g (P.constantUnitWeil c) (P.constantUnitDual_mem c)

/-- The canonical identification [1,1] = 1 intertwines the two Weil data.
Source: the constant-unit sentence (blueprint: def-pod-dual-tate-datum).
Proof: write a for the inverse monoidal unit map and d for the three-arrow dual
structure. The evaluation identity of the closed comparison and naturality in both
Hom slots give ev (1 tensor d) = a P(ev) mu (a^-1 tensor 1). Precompose with the
inverse left unitor. The monoidal left-unit equation identifies the last two
factors with P(lambda^-1), giving u d = a P(u). Here u is exactly the inverse
unitNatIso, so this is the stated equation, with no choice of a unit identification. -/
theorem constantDual_datum :
    (P.constantDualWeil c).str.hom.hom ≫
        (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv =
      (StrictWeilCondensed.action Λ g).map
          (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv ≫
        (P.constantUnitWeil c).str.hom.hom := by
  have hunit : (ObjectProperty.ι _).mapIso (P.constantUnitWeil c).str =
      (Functor.Monoidal.εIso (StrictWeilCondensed.action Λ g)).symm := by
    ext
    simp [constantUnitWeil]
  simp only [constantDualWeil, StrictWeilCondensed.dualComplex,
    Endofunctor.IsoAlgebra.mk_str, ObjectProperty.isoMk, ObjectProperty.homMk_hom]
  rw [hunit]
  simpa [constantUnitWeil, StrictWeilCondensed.dualDatum] using
    unit_dual (StrictWeilCondensed.action Λ g)

/-- The constant-dual global operators identify with the iterated global geometric
Frobenius operators of the coefficient unit, for ordinary and compact supports.
Source: the final sentence (blueprint: def-pod-dual-tate-datum).
Proof: constantDual_datum makes the canonical unit identification a morphism of
strict Weil pairs. The ordinary and compact-support transports are natural in
that morphism. Compose their naturality squares with the Weil equation to obtain
intertwining for m=1. For m=0 both sides are the same map. Induction using
associativity proves the equalities for every natural m. The operators here are
precisely the two canonical global transports followed by the Weil structure,
as fixed by the Poincare conventions, so their powers are the required iterates. -/
theorem constantDual_frobenius (m : ℕ) :
    (P.frobeniusIterate c (P.constantDualWeil c) m).1 ≫
        (P.ordinarySections c).map (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv =
      (P.ordinarySections c).map (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv ≫
        (P.frobeniusIterate c (P.constantUnitWeil c) m).1 ∧
    (P.frobeniusIterate c (P.constantDualWeil c) m).2 ≫
        (P.compactSections c).map (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv =
      (P.compactSections c).map (unitNatIso.app (𝟙_ (P.ambient c P.X))).inv ≫
        (P.frobeniusIterate c (P.constantUnitWeil c) m).2 := by
  sorry

end WeilConjectures.CondensedPoincareDualityConventions

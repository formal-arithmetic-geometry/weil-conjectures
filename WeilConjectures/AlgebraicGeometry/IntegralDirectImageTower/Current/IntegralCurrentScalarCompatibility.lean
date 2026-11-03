/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.Current.IntegralCurrentReductionPullback
import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom

/-! # Scalar compatibility for the current reduction construction

The existing generator and representative proofs are reused on construction-only data.
Source: integral direct-image proof (2), normalized proper/open scalar maps.
(blueprint: lem-sp-current-scalar-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The inverse open reduction mate is invertible once its target has open support.
Source: blueprint integral direct-image proof paragraph (2), exact slice tensor identity.
Proof: expand the inverse Hom correspondence as the open extension of the input
map followed by the open counit. The input map is the reduction of the integral
open unit followed by the pullback/reduction isomorphism. Fully faithful integral
extension by zero makes that unit invertible. Functors preserve its invertibility,
and the support hypothesis makes the remaining counit invertible. Their composite
is precisely the specified mate, with no choice of an additional comparison.
(blueprint: lem-sp-current-scalar-compatibility). -/
theorem open_reduction_isIso_of_support (s : Coefficients l E)
    (q : ScalarCompatibility l E s) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (N : Integral l E U)
    (hsupport : IsIso ((s.operations.openOp j).derivedAdjunction.counit.app
      ((derivedReduction l E s T).obj
        ((CondensedRing.openImmersionLowerShriek
          (spIntegralCondensed l E) j).mapDerivedCategory.obj N)))) :
    IsIso (openReductionInverse l E s q j N) := by
  have hu : IsIso
      ((((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (spIntegralCondensed l E) j).ofNatIsoRight
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (spIntegralCondensed l E) j).symm).unit.app N)) := by
    change IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
        (spIntegralCondensed l E) j).unit.app N)
    infer_instance
  have := hsupport
  unfold openReductionInverse
  rw [Adjunction.homEquiv_counit]
  infer_instance


/-- The current reduction admits the sectionwise and representative-normalized
scalar comparisons, and the specified open-unit mate is invertible.
Proof: identify ordinary evaluation by its identical sections and restriction maps.
Construct the ordinary pullback isomorphism on generating tensors and descend it
uniquely using flat-term K-flat representatives. Finite scalar extension preserves
open support by its exact slice tensor identity. Exact evaluations detect the
invertibility of the open counit on that supported reduction. Expanding the open
mate expresses it as open extension of the reduced integral unit, followed by the
tower open counit; each factor is invertible. No constructibility is assumed.
Source: blueprint integral direct-image proof (2).
(blueprint: lem-sp-current-scalar-compatibility). -/
theorem scalar_compatibility_exists (s : Coefficients l E) :
    ∃ q : ScalarCompatibility l E s, OpenScalarIsIso l E s q := by
  classical
  let q : ScalarCompatibility l E s :=
    { evaluation := normalizedEvaluation l E s
      pullback := fun f ↦
        (normalized_reduction_pullback_existsUnique l E s
          (normalizedEvaluation l E s) f).exists.choose }
  refine ⟨q, ?_⟩
  intro U T j hj N
  have hc : IsIso ((s.operations.openOp j).derivedAdjunction.counit.app
      ((derivedReduction l E s T).obj
        ((CondensedRing.openImmersionLowerShriek
          (spIntegralCondensed l E) j).mapDerivedCategory.obj N))) :=
    (s.base.calculus T).detects _
      (fun n ↦ finite_open_reduction_support l E s j N n)
  exact open_reduction_isIso_of_support l E s q j N hc

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current

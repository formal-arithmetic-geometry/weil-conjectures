/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData
public import WeilConjectures.DeligneLaumon.NativeOpenCoefficientObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.IntegralOpenReductionComparison
import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections

/-!
# Native open extension and coefficient comparisons

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-integral-adjunction/
sk-prop-sp-integral-adjunction-direct-image.proof.md,
det-sp-integral-direct-image-tower clause (2)
(blueprint: lem-dla1-native-open-extension-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

open NativeOpenExtension

/-- Native strict open reduction for every supplied coefficient-tower presentation s.
The inverse of r is the specified open-unit mate, formed before any finite evaluation.
Its geometric input retains the ordinary generator and K-flat representative equations.
Source: clause (2) (blueprint: lem-dla1-native-open-extension-comparison). -/
structure NativeOpenReductionData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (s : IntegralDirectImageTower.Presentation l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] where
  geometry : IntegralDirectImageTower.ReductionGeometry l E s
  r : (constantModelBoundedConstructible (spIntegralCondensed l E) U).ι ⋙
        IntegralDirectImageTower.openD l E j ⋙
        IntegralDirectImageTower.derivedReduction l E s T ≅
      (constantModelBoundedConstructible (spIntegralCondensed l E) U).ι ⋙
        IntegralDirectImageTower.derivedReduction l E s U ⋙
        SpTowerShriek.openD l E s.base (s.operations.openOp j)
  normalization : ∀ K,
    r.inv.app K = IntegralDirectImageTower.openReductionInverse l E s geometry j K.obj
  counit : ∀ N,
    (SpTowerShriek.openD l E s.base (s.operations.openOp j)).map
        ((geometry.pullback j).derived.inv.app N) ≫
      IntegralDirectImageTower.openReductionInverse l E s geometry j
        ((IntegralDirectImageTower.pull l E j).obj N) ≫
      (IntegralDirectImageTower.derivedReduction l E s T).map
        ((IntegralDirectImageTower.openAdjunction l E j).counit.app N) =
    (s.operations.openOp j).derivedAdjunction.counit.app
      ((IntegralDirectImageTower.derivedReduction l E s T).obj N)

/-- The clauses of the native open comparison, including genuine rational finite vanishing.
Source: det-sp-integral-direct-image-tower clause (2)
(blueprint: lem-dla1-native-open-extension-comparison). -/
structure NativeOpenExtensionComparisonData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (s : IntegralDirectImageTower.Presentation l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] where
  reduction : NativeOpenReductionData l E s j
  constructibleExtension : ∀ K : IntegralDirectImageTower.Integral l E U,
    constantModelBoundedConstructible (spIntegralCondensed l E) U K →
      constantModelBoundedConstructible (spIntegralCondensed l E) T
        (D(CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j).obj K)
  integralScalar : ScalarCompatibility (nativeInclusion l E) j
  fieldScalar : ∀ (E' : Type u) [Field E'] [Algebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E'] (f : E →ₐ[ℚ_[l]] E')
    (hf : @Continuous E E' (fieldTopology l E) (fieldTopology l E') f),
    ScalarCompatibility (fieldMap l E E' f hf) j
  rationalFiniteEvaluation : ∀ (X : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (fieldRing l E) X))),
    IsZero ((rationalEvaluation l E X n).obj K)

/-- Native open extension and its normalized coefficient comparisons.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-integral-adjunction/
sk-prop-sp-integral-adjunction-direct-image.proof.md,
det-sp-integral-direct-image-tower clause (2)
(blueprint: lem-dla1-native-open-extension-comparison).

Proof plan, following the four DAG steps:
1. Finite-type schemes over k are Noetherian. The adic constructibility comparison identifies
finite constant models with the internal constructibility predicate. Exact native extension
by zero preserves these cohomology sheaves and their finite cohomological range.
2. Fix the supplied coefficient-tower presentation s; no presentation is chosen existentially.
The integral criterion gives completeness. Use internal_module_operations_transport and
the normalized section equivalence to identify the native open adjunction with its section
model. Apply integralOpenReductionComparison before evaluation and transport its strict map
through those fixed comparisons. ReductionGeometry records the generator and representative
normalization. Its inverse open-unit mate is openReductionInverse; the mate counit identity
gives the displayed equation for the actual native counit.
3. For O→E and finite E→E', transpose the scalar-unit balanced map under extension/restriction
of scalars. Open tensor normalization identifies it with derivedOpenImmersionShriekIso.
The conjugate identity gives the displayed square with the actual open counits.
4. Keep the comparison on whole strict systems; semilinear evaluation gives its finite
formulas without assuming derived evaluation faithful. For a field complex, restriction to O
followed by derived tensor with O/pi^(n+1) is zero, since pi is invertible on the complex.
No smooth exceptional adjunction or absolute cohomological dimension input is used.
-/
theorem nativeOpenExtensionComparison
    (k : Type u) [Field k] [PerfectField k]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (s : IntegralDirectImageTower.Presentation l E)
    {U T : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (j : U ⟶ T) [IsOpenImmersion j.left] [QuasiCompact j.left] :
    Nonempty (NativeOpenExtensionComparisonData l E s j.left) := by
  sorry

end WeilConjectures

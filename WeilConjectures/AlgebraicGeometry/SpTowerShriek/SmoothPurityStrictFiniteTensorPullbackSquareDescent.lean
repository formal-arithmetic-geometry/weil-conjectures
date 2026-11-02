/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex

/-! Descent statement for the prescribed finite tensor pullback square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

/-- The proposition expressing the prescribed finite tensor square.

This isolates the categorical descent step from the representative calculation.
-/
def strictFiniteTensorPullbackSquareStatement (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) : Prop :=
  (comparisonFiniteRealization l E b X n).map
      (((leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) ≫
    (tensor X n).hom.app
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          f).leftDerivedFunctor.obj M,
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
          f).leftDerivedFunctor.obj N) ≫
    (comparisonLevelTensor l E b X n).map
      (Prod.mkHom ((comparisonFinitePull l E b f n).hom.app M)
        ((comparisonFinitePull l E b f n).hom.app N)) =
  (comparisonFinitePull l E b f n).hom.app
      ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) Y).obj (M, N)) ≫
    (proEtaleConstantRingDerivedPullback (R l E n) f).map
      ((tensor Y n).hom.app (M, N)) ≫
    (levels.tensorPullback f n).hom.app
      ((comparisonFiniteRealization l E b Y n).obj M,
        (comparisonFiniteRealization l E b Y n).obj N)

/-- Representative squares descend through the two derived-category variables.
Source: blueprint operations proof (2), final localization and replacement step.
(blueprint: new-lem-sp-strict-finite-tensor-pullback-square-descent).

Proof: by CochainComplex.exists_quasiIso_flat_kFlat (Stacks 06YS) every derived
object is isomorphic to Q of a flat-term K-flat complex; choose such replacements
in both variables, apply the
representative equality to their images in the derived category, and use the
universal property of the localization together with naturality of every
comparison map. The replacement maps are inverted by the left-derived
functors, so the resulting equality is the displayed square for arbitrary
objects. This is independent of the calculation of the representative square.
-/
theorem strictFiniteTensorPullbackSquare_descent (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hrep : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
      (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))) ℤ),
      WeilConjectures.finiteScalarFlatRepresentatives Y (R l E n) P →
      WeilConjectures.finiteScalarFlatRepresentatives Y (R l E n) Q →
      strictFiniteTensorPullbackSquareStatement l E b o levels tensor f n
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
      (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b X n).map
          (((leftDerivedUpperStarTensorComparison
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) f).app M).app N) ≫
        (tensor X n).hom.app
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj M,
            (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj N) ≫
        (comparisonLevelTensor l E b X n).map
          (Prod.mkHom ((comparisonFinitePull l E b f n).hom.app M)
            ((comparisonFinitePull l E b f n).hom.app N)) =
      (comparisonFinitePull l E b f n).hom.app
          ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) Y).obj (M, N)) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          ((tensor Y n).hom.app (M, N)) ≫
        (levels.tensorPullback f n).hom.app
          ((comparisonFiniteRealization l E b Y n).obj M,
            (comparisonFiniteRealization l E b Y n).obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek

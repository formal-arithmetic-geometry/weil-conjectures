/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteTensorPullbackSquareDescent
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels

/-! Representative calculation for the prescribed finite tensor pullback square. -/

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

/-- The pinned square on flat-term K-flat representatives.
Source: blueprint operations proof (2), tensor comparison on signed total representatives.
(blueprint: new-lem-sp-strict-finite-tensor-pullback-square-representatives).

Proof: evaluate the two composites on flat-term K-flat complexes, reduce to pure
sections, and use the scalar unit and sectionwise inverse-image unit to identify
the ordinary tensor arrows. The finite tensor pin gives the prescribed arrows;
its model equation and ComparisonFiniteTensorRepresentative identify the target
with the semilinear model. The normalized tensorPullback equation then closes
the signed total-complex calculation. The remaining localization details are
handled by the separate descent lemma.

STATEMENT-DISPUTED: the interfaces do not require generic.levelPushUnderlying
of o.geometry to act identically on sections. Simultaneously negating that
identification and inverseImage.moduleUnderlying preserves the unit equation,
but negates the normalized ordinary tensor comparison and its derived map.
The fixed comparisonFinitePull and finite tensor pins do not change. A uniform
sign at all levels also preserves ordinaryUnitTransition. Thus the intended
calculation needs an additional actual-section normalization (the hpush used
by exists_tensorLevelCoordinates). The private diagnostics above certify this
local ambiguity; the complete structural argument and blueprint question are
in the delivery report. No hypothesis or conclusion is changed here.
-/
theorem strictFiniteTensorPullbackSquare_representatives (b : Base l E)
    (o : Operations l E b) (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hpin : (∀ (T : Scheme.{u}) (n : ℕ),
    ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n),
    ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n),
    ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
          (e.derived.prod e.derived) ⋙ t.functor,
      HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
      HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
      HEq t.functor (comparisonLevelTensor l E b T n) ∧
      ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
      Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
        (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
        (comparisonFiniteConstantSection l E T n) e t d)))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))) ℤ)
    (hP : WeilConjectures.finiteScalarFlatRepresentatives Y (R l E n) P)
    (hQ : WeilConjectures.finiteScalarFlatRepresentatives Y (R l E n) Q) :
    strictFiniteTensorPullbackSquareStatement l E b o levels tensor f n
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek

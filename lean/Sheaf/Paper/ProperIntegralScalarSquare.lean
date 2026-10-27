/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.ProperCoefficientDescentData

/-! # Descent of the proper comparison through coefficient stages -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ProperCoefficientDescent
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients
open TensorProduct

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]


section Descent
variable (B : FiniteFieldDatum.{u}) (hl : l ≠ B.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of B.k))] [Y.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))] [IsSeparated (Y ↘ Spec (.of B.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of B.k))] [IsProper f]


/-- The integral identity-open comparison commutes with the specified scalar maps.
Source: current blueprint, prop-weil-proper-compact-coincidence.proof.md,
first paragraph; coefficient-descent argument, Steps 1--3.
(blueprint: lem-weil-proper-integral-scalar-square).

Proof: use the section formulas in InducedOnFullTower to identify the identity-open
map before reduction. Open tensor normalization makes its restriction and scalar
squares commute on the strict coefficient diagram. Transpose both composites through
the common mixed tensor unit. The compact coefficient action and the normalized
strict-image mixed-unit theorem identify these transposes with the same composite
of the finite identity-open map, direct image of the mixed unit, and restriction.
The coefficient-extension reduction model identifies the resulting coherent system
maps, retaining transitions. Cancel the target reduction isomorphism and apply
faithfulness of coherent reduction on the integral constructible category. This
proves the equation in the full integral category; separate evaluation faithfulness
is neither asserted nor used. -/
theorem integralScalarSquare
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (hD : SfStrictDirectImageScalar.HasIntegralLaws l Ω f D)
    (S : SfCompactSupportCoefficientAction l B.k
      (PurCompactSupport.coefficientPrimeUnit l B hl) Ω (Compactification.ofIsProper f))
    (θ : ∀ E : Index l Ω, compactIntegral l Ω B hl f E ≅ (D.integral E).image)
    (hθ : PreservesProjections l Ω B hl f D θ)
    (hθtower : InducedOnFullTower l Ω B hl f D θ) :
    ∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X),
      (integralTransition l Ω Y E L h).map ((θ E).hom.app K) ≫
          (D.integralComparison E L h).inv.app K =
        (S.integralBeta h).hom.app K ≫
          (θ L).hom.app ((integralTransition l Ω X E L h).obj K) := by sorry

end Descent
end WeilConjectures.ProperCoefficientDescent

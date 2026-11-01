/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.IntegralNormalizedRingRefinementCompositionAfterInclusion

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The composition clause for the completed integral refinement maps.
Source: the composition clause of integral normalized refinement pasting
(blueprint: lem-sf-integral-normalized-ring-refinement-composition).

This is the composition component of the parent integral normalized refinement laws.
The proof applies the integral pasting theorem to the binary refinement diagram,
using the normalized open comparison and integral-left realization supplied by `N`
and `R`. -/
theorem integral_normalized_ring_refinement_composition
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (N : CoefficientConstructionRefinements.{u, v} l Ω D hl R F M)
    (E : FieldStage.{max u v} l) :
    ∀ {a b c : Compactification f} (r : a.Refinement b) (t : b.Refinement c),
      (N.refinement (r.comp t) (.integral E)).left =
        (N.refinement r (.integral E)).left ≪≫
          (N.refinement t (.integral E)).left := by
  let I := RingStage.inclusion.{u, v} l Ω Y (.integral E)
  let _ : I.Faithful := by
    dsimp only [I]
    cases E
    dsimp only [RingStage.inclusion]
    infer_instance
  intro a b c r t
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply I.map_injective
  exact integral_normalized_ring_refinement_composition_after_inclusion
    l Ω D hl R F M N E r t K

end WeilConjectures.ConstructibleExceptionalCoefficients

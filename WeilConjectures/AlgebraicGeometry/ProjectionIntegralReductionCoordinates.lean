/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralProjectionReductionCoordinates

/-! Finite-stage coordinate data used in the integral projection action. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures
open IntegralProjectionReduction

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The complete finite-stage coordinate package needed to compare an integral
projection action with its finite evaluations. -/
def projectionIntegralReductionCoordinates
    (d : SixFunctorOperationDatum D C E n hn) : Prop :=
  ∀ m : ℕ,
    ∃ t : TensorCoordinates d m,
      (∀ (X : SixFunctorSpace D)
        (K K' L : sfIntegralConstructibleCategory C.l E X.obj.left) (a : K ⟶ K'),
        (reduction d m X).map (((d.higher.integralTensor X).map a).app L) ≫
            (t X K' L).hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).map
              ((reduction d m X).map a)).app ((torReduction d m X).obj L)) ∧
      (∀ (X : SixFunctorSpace D)
        (K L L' : sfIntegralConstructibleCategory C.l E X.obj.left) (b : L ⟶ L'),
        (reduction d m X).map (((d.higher.integralTensor X).obj K).map b) ≫
            (t X K L').hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
              ((reduction d m X).obj K)).map ((torReduction d m X).map b)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProjectionComponent d.higher.integralExchange f c K L) ≫
            (targetIso d m t f c K L).hom =
          (sourceIso d m t f c K L).hom ≫
            CompactSupportFiniteProjection.component (stage d m) f c
              ((reduction d m X).obj K) ((torReduction d m Y).obj L)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProperProjection d.higher.integralExchange f K L) ≫
            (properTargetIso d m t f K L).hom =
          (properSourceIso d m t f K L).hom ≫
            CompactSupportFiniteProjection.properComponent (stage d m) f
              ((reduction d m X).obj K) ((torReduction d m Y).obj L))

/-- The coordinate package is supplied by the integral reduction-coordinate
construction. Its remaining use is the finite tensor-action comparison.
Source: current blueprint prop-sf-pf-coherence, finite-coordinate construction
used by the integral reduction clause
(blueprint: lem-sf-projection-reduction-integral-coordinates).
Proof: at each reduction level m apply integralProjection_reduction_coordinates;
its witness and four equations are the fields of the package. -/
theorem projectionIntegralReduction_coordinates
    (d : SixFunctorOperationDatum D C E n hn) :
    projectionIntegralReductionCoordinates d := by
  intro m
  exact integralProjection_reduction_coordinates d m

end WeilConjectures

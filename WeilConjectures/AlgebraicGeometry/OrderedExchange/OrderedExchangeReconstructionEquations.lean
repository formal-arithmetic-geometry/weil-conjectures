/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData

/-! # reconstructionCoefficientEquations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- reconstructionCoefficientEquations: the indicated part of the ordered comparison argument.
Source: blueprint completed-exchange-coherence, second proof paragraph;
Stacks Tags 099M, 099N, 0A07 and 0E48.
(blueprint: lem-weil-pbc-ordered-reconstruction-equations).
Proof: the completion reflector identifies the completed pullback with quotient
tower reconstruction, and restriction preserves its actual unit by rho_unit.
The unit equation defining phi therefore identifies the restricted reconstruction
with constant reconstruction. Uniqueness follows by injective precomposition with
the completion unit into a complete target. This proves the target reconstruction
equation. Apply the same equation to the complete object Rf_*K, use chi to replace
its restriction by the constant direct image, and use naturality of its quotient
unit; this proves the source reconstruction equation. Compose the source equation
with the strict projection formula comparison. Its scalar compatibility and
naturality of lambda give the displayed sourceA equation. On the target, write
targetA as the specified direct-image/derived-limit comparison. The scalar limit
square, followed by naturality for the pullback reconstruction, converts it to
the constant direct-image/limit comparison. Substitute the target reconstruction
equation to get the final displayed equality. All comparisons are the specified
unit and counit comparisons, and direct image preserves completeness, so each
application is on the stated full complete category. -/
theorem reconstructionCoefficientEquations (sq : ChosenCartesianSquare g' f' f g) :
    ∀ (K : d.derived X) (hK : d.TowerComplete X K),
      ((res d Y').map (sourceReconstruction (f := f) (g := g) d K).hom ≫
          (lambda d Y').hom.app
            ((completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K))) ≫
          (rlim (A := A) Y').map (rhoM (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom) ∧
      ((lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
          (rlim (A := A) X').map (rhoPull (g' := g') d K).hom =
        (phi d g').hom.app ⟨K, hK⟩ ≫
          (reconstruction d g' ((res d X).obj K)).hom) ∧
      ((res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (beta (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom ≫
          (S (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((res d Y').map (targetA (g' := g') (f' := f') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K).hom =
        (iotaT (f' := f') (g' := g') d K hK).hom ≫
          (T (f' := f') (g' := g') d ((res d X).obj K)).hom) := by sorry

end AlgebraicGeometry.Scheme.OrderedExchange

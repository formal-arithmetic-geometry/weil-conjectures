/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
import WeilConjectures.AlgebraicGeometry.DiagonalCompletedGeneratorExt
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalBaseChangeCartesian

/-! # Integral-generator detection after geometric inverse image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace

/-- Pullback of the completed supported source is detected by its integral generator
against every finite-torsion supported target.

Source: blueprint latest, diagonal coefficient changes (3), comparison of ordinary
source cones under geometric pullback.
(blueprint: lem-diagonal-pulled-completed-generator-ext).

Proof: transpose both maps under geometric inverse-image/direct-image adjunction.
Composition of direct images and the commutative diagonal square identify the
new target with closed direct image of the direct image on the projective line.
That direct image remains killed by the same prime power, section by section.
Use supported integral-generator detection there. Naturality of the adjunction
transposes the assumed generator equality to exactly the required equality.
Cancel the direct-image comparison and reverse adjunction. -/
theorem diagonalPulledCompletedGenerator_hom_ext (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (n : ℕ)
    (Q : Sheaf (Scheme.ProEt.topology (ProjectiveLine Y')) Ab.{u + 1})
    (hQ : ∀ (V : (ProjectiveLine Y').ProEtᵒᵖ) (y : Q.obj.obj V),
      l ^ (n + 1) • y = 0)
    (f h : (upperStar Ab.{u + 1} (baseW g)).obj
        ((diagonalForget l (diagonalSurface Y)).obj
          ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
            (diagonalCompletedSource l Y))) ⟶
      (lowerStar Ab.{u + 1} (diagonalImmersion Y')).obj Q)
    (heq : (upperStar Ab.{u + 1} (baseW g)).map (diagonalCompletedGenerator l Y) ≫ f =
      (upperStar Ab.{u + 1} (baseW g)).map (diagonalCompletedGenerator l Y) ≫ h) :
    f = h := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)
  let k := (lowerStarComp Ab.{u + 1} (diagonalImmersion Y') (baseW g) ≪≫
    lowerStarCongr Ab.{u + 1} (diagonalBaseChange_cartesian g).w.symm ≪≫
    (lowerStarComp Ab.{u + 1} (baseP g) (diagonalImmersion Y)).symm).app Q
  apply (adj.homEquiv _ _).injective
  apply (cancel_mono k.hom).mp
  apply diagonalCompletedGenerator_hom_ext l Y n
    ((lowerStar Ab.{u + 1} (baseP g)).obj Q)
  · intro V y
    exact hQ _ y
  · simp only [← Category.assoc]
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left, heq]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalIntegralForget

/-! # Forgetting support after coefficient extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A source comparison preserving the quotient unit automatically preserves the
Chern class of the actual positive diagonal divisor.

Source: latest blueprint classes proof, clause (3), integral forget-support equation.
(blueprint: lem-sp-tower-class-diagonal-chern-normalization).

Proof: substitute the source normalization and cancel the source isomorphism
against its inverse in the diagonal arrow. Combine the two reduction maps using
functoriality. The integral supported boundary precomposed with the integral
supported unit is the positive divisor line class. Apply reduction and scalar
extension to that equality; the remaining target and shift comparisons are
literally those defining firstChern. -/
theorem diagonal_chern_normalization {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} (c : Chern l E (diagonalSurface S))
    {g : SpTowerShriek.Geometry l E b (diagonalImmersion S)}
    (p : CoefficientPullback l E b (diagonalImmersion S) g)
    (s : diagonalExtendedSource l E c ≅
      (SpTowerShriek.push l E b g).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
    (hs : diagonalExtendedUnit l E c ≫ s.hom = unitArrow l E p) :
    unitArrow l E p ≫ diagonalArrow l E c s = firstChern l E c (diagonalPic S) := by
  rw [← hs]
  unfold diagonalArrow diagonalExtendedUnit firstChern firstChernR
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    ← c.scalar.T.map_comp_assoc, ← c.reduction.derived.map_comp_assoc,
    diagonalIntegral_forget]
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses

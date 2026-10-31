/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestrictionEvaluation
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
/-- Evaluation of the normalized proper comparison at a finite level.
Source: Stacks 0D6E and 070Y; coefficient-composition argument, step 7.
(blueprint: lem-sp-system-restriction-finite-proper-evaluation).
This is the `properEvaluation` field alone; its proof is the K-injective mate
calculation and does not assert the open fields. -/
theorem finiteCompatibility_properEvaluation (l : ℕ) [Fact l.Prime]
    {B C : Etale.SystemProjection.Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (d : Comparison a j p) (h : ∀ n : ℕ, LevelComm a p n) : ∀ (n : ℕ)
    (M : VaryingRing.Derived (levels C) (steps C) Z),
    (VaryingRing.ev (levels B) (steps B) Y n).map (d.properPart.iso.hom.app M) ≫
      (restrictionEvaluation Y a n).hom.app
        ((VaryingRing.P (levels C) (steps C) p).obj M) ≫
      (levelRestriction Y a n).map
        ((VaryingRing.evalP (levels C) (steps C) p n).hom.app M) =
    (VaryingRing.evalP (levels B) (steps B) p n).hom.app
        ((derivedRestriction Z a).obj M) ≫
      (StrictTower.moduleDirectImage (levels B n) p).rightDerivedFunctor.map
        ((restrictionEvaluation Z a n).hom.app M) ≫
      (levelProper (h n)).hom.app
        ((VaryingRing.ev (levels C) (steps C) Z n).obj M) := by
  sorry
end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

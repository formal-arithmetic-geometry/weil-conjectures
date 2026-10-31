/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionEvaluation
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
/-- Evaluation of the normalized open comparison at a finite level.
Source: Stacks 03DI and 03DJ; coefficient-composition argument, step 7.
(blueprint: lem-sp-system-restriction-finite-open-evaluation).
This is exactly the `openEvaluation` field, isolated from the other compatibility
conditions. -/
theorem finiteCompatibility_openEvaluation (l : ℕ) [Fact l.Prime]
    {B C : Etale.SystemProjection.Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (d : Comparison a j p) (h : ∀ n : ℕ, LevelComm a j n)
    (o : ∀ n : ℕ, levelRestriction X a n ⋙ (StrictTower.moduleJ (levels B n) j).mapDerivedCategory ≅
      (StrictTower.moduleJ (levels C n) j).mapDerivedCategory ⋙ levelRestriction Z a n) : ∀ (n : ℕ)
    (M : VaryingRing.Derived (levels C) (steps C) X),
    (VaryingRing.ev (levels B) (steps B) Z n).map (d.openPart.derived.hom.app M) ≫
      (restrictionEvaluation Z a n).hom.app
        ((VaryingRing.J (levels C) (steps C) j).obj M) ≫
      (levelRestriction Z a n).map
        ((VaryingRing.evalJ (levels C) (steps C) j n).hom.app M) =
    (VaryingRing.evalJ (levels B) (steps B) j n).hom.app
        ((derivedRestriction X a).obj M) ≫
      (StrictTower.moduleJ (levels B n) j).mapDerivedCategory.map
        ((restrictionEvaluation X a n).hom.app M) ≫
      (o n).hom.app
        ((VaryingRing.ev (levels C) (steps C) X n).obj M) := by
  sorry
end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

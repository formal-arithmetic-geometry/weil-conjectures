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
/-- Unit normalization of the finite-level open comparison.
Source: Stacks 03DI and 03DJ; coefficient-composition argument, step 7.
(blueprint: lem-sp-system-restriction-finite-open-normalized).
The proof is the localized summand-adjunction computation for `d.openPart`; this
statement is only the `openNormalized` field and is strictly weaker than
`FiniteCompatibility`. -/
theorem finiteCompatibility_openNormalized (l : ℕ) [Fact l.Prime]
    {B C : Etale.SystemProjection.Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (d : Comparison a j p) (h : ∀ n : ℕ, LevelComm a j n)
    (o : ∀ n : ℕ, levelRestriction X a n ⋙ (StrictTower.moduleJ (levels B n) j).mapDerivedCategory ≅
      (StrictTower.moduleJ (levels C n) j).mapDerivedCategory ⋙ levelRestriction Z a n) : ∀ (n : ℕ)
    (M : DerivedCategory (StrictTower.Modules (levels C n) X)),
    (VaryingRing.levelJAdj (levels B) j n).unit.app ((levelRestriction X a n).obj M) ≫
      (StrictTower.modulePullback (levels B n) j).mapDerivedCategory.map
        ((o n).hom.app M) ≫
      (levelPull (h n)).inv.app
        ((StrictTower.moduleJ (levels C n) j).mapDerivedCategory.obj M) =
    (levelRestriction X a n).map ((VaryingRing.levelJAdj (levels C) j n).unit.app M) := by
  sorry
end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

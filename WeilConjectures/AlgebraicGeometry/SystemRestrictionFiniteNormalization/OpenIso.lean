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
/-- Finite-level open restriction comparison for a normalized system comparison.
Source: Stacks 03DI and 03DJ; coefficient-composition argument, step 7.
(blueprint: lem-sp-system-restriction-finite-open-iso).
The proof localizes the section-normalized open comparison `d.openPart` and identifies
its finite level through the existing evaluation functors. This is strictly the open
comparison isomorphism field of `FiniteCompatibility`; it does not assert any other
field or use faithfulness of evaluation. -/
theorem finiteCompatibility_openIso (l : ℕ) [Fact l.Prime]
    {B C : Etale.SystemProjection.Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (d : Comparison a j p) : Nonempty (∀ n : ℕ,
    levelRestriction X a n ⋙ (StrictTower.moduleJ (levels B n) j).mapDerivedCategory ≅
      (StrictTower.moduleJ (levels C n) j).mapDerivedCategory ⋙ levelRestriction Z a n) := by
  sorry
end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

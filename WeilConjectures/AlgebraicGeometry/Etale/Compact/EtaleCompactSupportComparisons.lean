/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion

/-!
# Canonical comparisons for ordinary etale compact support

The existing bounded-below API supplies the natural isomorphisms and their coherence:
* `rightDerivedLowerShriekOfCompactificationPlusRefinementIso`, with its `_id` and `_comp`;
* `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`, `_refl`, `_trans`;
* `rightDerivedLowerShriekPlusCompIso`, its `_hom_eq`, and its `_assoc`.
These are used for `ModuleCat.{u + 1} Λ`, with finite commutative `Λ`.
`IsNoetherian` is exactly the finite affine Noetherian-cover condition, by Mathlib's
`isNoetherian_iff_of_finite_affine_openCover`.

The statement below identifies the refinement isomorphism with precisely the specified
proper/open alpha map, after applying the ambient pushforward and its canonical composition
identification. Together with the existing declarations listed above, it supplies all the
clauses of the comparison and composition package, without introducing a second comparison
or composition construction.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical refinement comparison is the ambient proper pushforward of the specified
proper/open comparison, followed by the canonical direct-image composition identification.
No Cartesian-square or density assumption is placed on the refinement.

Source: Stacks Project, Tags 0F7I, 0F7J, 0F7K. -/
theorem etaleCompactSupport_refinementComparison_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r).hom.app K =
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
        (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
      ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pfComp'
        r.hom d.g c.g r.hom_g).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K) := by
  have sq : IsPullback (𝟙 X) f f (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := (compactSupportFiniteTorsion Λ sq c).2 d r K
  simp only [compactSupportProperOpenRefinementMap] at h
  rw [derivedPlusFormalism_shriekIso] at h
  rw [rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq,
    rightDerivedLowerShriekOfCompactificationPlusIso_symm,
    derivedPlusFormalism_pfComp'_inv]
  exact h.symm

end AlgebraicGeometry.Etale

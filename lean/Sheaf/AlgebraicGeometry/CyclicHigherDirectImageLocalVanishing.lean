/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-!
# Local vanishing of higher direct images with cyclic coefficients

Source: Stacks Project, Tag 03Q8, and the affine basis of the small etale site.
(blueprint: lem-sbc-cyclic-higher-direct-image-local-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Local annihilation of every cohomology class on affine etale objects makes the
higher direct image of a constant cyclic abelian sheaf zero.

Source: Stacks Project, Tag 03Q8; the vanishing argument in
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`.
(blueprint: lem-sbc-cyclic-higher-direct-image-local-vanishing).

Proof: Identify the higher direct image with the sheafification of the presheaf
U ↦ H^q(Y ×_X U, Z/e), using Tag 03Q8. The restriction along V → U is the
cohomology pullback along Y ×_X V → Y ×_X U, followed by the canonical constant
coefficient identification. This identification carries zero to zero. Each class
on an affine etale U therefore restricts to zero on a jointly surjective etale
family by the hypothesis. Affine etale objects form a basis: any etale object is
covered by its affine open subschemes. Thus every section of the cohomology
presheaf is locally zero. The map to its sheafification is locally surjective;
a section of the sheafification locally lifts to the presheaf and, after a
further cover, is zero. The separatedness of the sheaf makes that section zero.
Consequently all section groups of the associated sheaf are zero, so it and the
isomorphic higher direct image are zero objects. This works also for e = 0,
where ZMod 0 is Z, and for degree zero and empty schemes. -/
theorem isZero_cyclicHigherDirectImage_of_locally_zero {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ)
    (H : ∀ ⦃U : Scheme.{u}⦄ (u : U ⟶ X) [Etale u] [IsAffine U]
      (ξ : Sheaf.H ((pullback h u).constantZMod e) q),
      ∃ (ι : Type u) (V : ι → Scheme.{u}) (v : ∀ i, V i ⟶ U), (∀ i, Etale (v i)) ∧
        (∀ x : U, ∃ i y, (v i).base y = x) ∧
        ∀ i, Etale.cohomologyMap (pullback.map h (v i ≫ u) h u (𝟙 Y) (v i) (𝟙 X) (by simp)
          (by simp)) _ q ξ = 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj (Y.constantZMod e)))) := by
  sorry

end AlgebraicGeometry.Etale

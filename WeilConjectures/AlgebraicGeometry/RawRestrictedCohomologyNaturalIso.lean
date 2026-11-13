/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality

/-! # Raw derived Hom equals restricted single-complex cohomology

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Raw derived Hom is naturally isomorphic to cohomology on the restricted etale
scheme, for every structure morphism and coefficient sheaf. -/
theorem exists_raw_restricted_cohomology_natural_iso (S : Scheme.{v}) (p : ℕ)
    (U : S.Etale) :
    ∃ e : ∀ {Y : Scheme.{v}} (h : Y ⟶ S)
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}),
      (abelianHigherDirectImageRawPresheaf h p F).obj (op U) ≅
        rawAffineRestrictedCohomology h p F U,
      ∀ {Y Y' : Scheme.{v}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
        (w : a ≫ h = h')
        (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
        (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
        (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F')
        (t : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)),
        rawAffineRestrictedCohomologyMap a h h' w p F F' φ U ((e h F).hom t) =
          (e h' F').hom (abelianHigherDirectImageRawPullback a h h' w p F F' φ U t) := by
  have hi {Y : Scheme.{v}} (h : Y ⟶ S)
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
      IsIso (rawRestrictedCohomologyComparison h p F U) :=
    isIso_rawRestrictedCohomologyComparison h p F U
  refine ⟨fun h F ↦ asIso (rawRestrictedCohomologyComparison h p F U), ?_⟩
  intro Y Y' a h h' w F F' φ t
  exact rawRestrictedCohomologyComparison_naturality a h h' w p F F' φ U t

end AlgebraicGeometry.Etale

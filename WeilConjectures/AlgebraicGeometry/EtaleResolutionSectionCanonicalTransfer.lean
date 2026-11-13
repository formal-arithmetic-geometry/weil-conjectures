/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalGlobalTransfer
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenTransfer

/-!
# Transfer of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Canonical comparisons identify augmentation-preserving section transfers with pullback.
Source: Stacks Project, Tag 01F8 and Remark 01FB (functoriality through resolutions),
Tag 03F3 (localization), and Tag 0A50 (section complexes). -/
theorem resolutionSection_canonical_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (cX : ResolutionSectionCanonicalComparison G I)
    (cY : ResolutionSectionCanonicalComparison
      ((upperStar AddCommGrpCat.{u + 1} g).obj G) J) :
    (∀ q x, cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (cX.globalEquiv q x)) ∧
    (∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (cX.openEquiv W q x)) := by
  constructor
  · exact resolutionSection_canonical_transfer_global_pointwise g G I J α hα cX cY
  · exact resolutionSection_canonical_transfer_open g G I J α hα cX cY

end AlgebraicGeometry.Etale

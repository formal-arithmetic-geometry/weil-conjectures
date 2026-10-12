/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Transfer of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The open component of augmentation-preserving canonical section transfer.
Source: Stacks Project, Tags 01F8 and 01FB (resolution functoriality),
Tag 03F3 (localization), and Tag 0A50 (section complexes).
(blueprint: lem-weil-pbc-etale-resolution-section-open-transfer)

Proof: Represent a homology class over W by a cycle z using surjectivity of homologyπ.
The sheafification/free-abelian/Yoneda adjunction gives a unique morphism f from the free
sheaf representing W with section equal to iCycles z; its naturality makes f a cocycle.
Adjoint α to β : g*I → J. Exactness of g* and hα identify β as a comparison of the
resolution g*I of g*G with J. The derived-category formula extMk_hom then computes
pullback of the Ext class of f by applying β to g*f. Precompose with the identity
section on g⁻¹W, pulled through the free-representable comparison. Naturality of the
adjunction unit identifies its evaluation with α at W followed by openSectionPullback.
Expand etaleOpenObjectCohomologyMap as inverse-image Ext followed by precomposition
with etaleOpenFreeSheafUnit. Functoriality of inverse image for the commuting square
(g restricted to W) ≫ W.ι = (g⁻¹W).ι ≫ g gives precisely the coefficient isomorphism
in openCohomologyPullback. Apply cX.open_cocycle and cY.open_cocycle and naturality of
homologyπ, first on z and then on all classes. Boundaries map to boundaries because α
is a chain map. Empty opens, identity morphisms and degree zero need no extra hypothesis. -/
theorem resolutionSection_canonical_transfer_open
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
    ∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (cX.openEquiv W q x) := by sorry

end AlgebraicGeometry.Etale

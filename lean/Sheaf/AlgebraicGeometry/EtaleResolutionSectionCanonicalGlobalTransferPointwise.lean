/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Pointwise canonical global transfer identity

Source: Stacks Project, Tags 0A50, 03F3, 01F8 and 01FB.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The canonical global transfer identity for one degree and one homology class.
Source: Stacks Project, Tags 0A50 and 03F3; this is the pointwise cocycle calculation
used in the global transfer theorem.
(blueprint: lem-weil-pbc-etale-resolution-section-global-transfer-pointwise)

Proof: Represent the chosen homology class by a cycle and identify its representative
with a morphism from the constant lifted integer sheaf by the sections adjunction.
Adjoint the augmentation-preserving chain map, apply inverse image to the cocycle,
and use the derived-category `extMk_hom` identity. Exactness of inverse image and the
augmentation equation identify the resulting Ext class with the explicit transfer;
normalization of the two canonical comparisons then gives the displayed equality.
The argument is valid in every degree, including degree zero and the zero sheaf.
-/
theorem resolutionSection_canonical_transfer_global_pointwise
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
      ((upperStar AddCommGrpCat.{u + 1} g).obj G) J)
    (q : ℕ)
    (x : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homology q) :
    cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (cX.globalEquiv q x) := by
  sorry

end AlgebraicGeometry.Etale

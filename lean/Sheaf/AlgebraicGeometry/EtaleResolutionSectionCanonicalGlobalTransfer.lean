/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison

/-!
# Transfer of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The global component of augmentation-preserving canonical section transfer.
Source: Stacks Project, Tags 01F8 and 01FB (resolution functoriality),
Tag 03F3 (localization), and Tag 0A50 (section complexes).
(blueprint: lem-weil-pbc-etale-resolution-section-global-transfer)

Proof: Represent a homology class by a cycle z, using surjectivity of homologyπ.
The constant-sheaf adjunction and evaluation at 1 give a unique morphism f representing
its underlying section. Naturality of this equivalence and the cycle equation give
f ≫ d = 0. Adjoint α to β : g*I → J. The equation hα identifies the augmentation
of β with the identity of g*G. Exactness of g* makes g*I a resolution of g*G.
In the derived category, write I.extMk f using extMk_hom. Apply the exact functor g*
and precompose with the constant-sheaf comparison. The augmentation equation cancels
the two resolution identifications, yielding the Ext class of the cocycle β after g*f.
Under the constant-sheaf adjunction this cocycle evaluates to α at the terminal object
followed by restriction along terminalSectionPullback g. This is exactly the degree-q
map of globalResolutionSectionTransfer. The chain-map equation makes its value a cycle.
Apply cX.global_cocycle and cY.global_cocycle to these representatives, and use naturality
of homologyπ to obtain the claimed equality for z, hence for every class. This argument
uses no positive-degree assumption; zero coefficients and empty schemes cause no change. -/
theorem resolutionSection_canonical_transfer_global
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
    ∀ q x, cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (cX.globalEquiv q x) := by sorry

end AlgebraicGeometry.Etale

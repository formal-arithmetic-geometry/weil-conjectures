module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer
import Sheaf.AlgebraicGeometry.EtaleResolutionSectionHomologyData
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale
/-- Compatibility identities for chosen section-homology equivalences.
Source: Stacks Project, Tag 0A50.
(blueprint: lem-weil-pbc-etale-resolution-section-homology-naturality).
Proof: use naturality of the adjunction unit and localization comparisons, then apply the
augmentation-preserving chain map induced by α to verify the six displayed
compatibility families. -/
theorem resolutionSection_homology_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (eX : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+ Sheaf.H G q)
    (eOX : ∀ (W : X.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q)
    (eY : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 Y))).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q)
    (eOY : ∀ (W : Y.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj
            ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q)
    : (∀ W q x, eOX W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (eX q x)) ∧
    (∀ (A B : X.Opens) (h : A ≤ B) q x,
      eOX A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (eOX B q x)) ∧
    (∀ W q x, eOY W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 Y)) J.cocomplex) q x) =
      cohomologyMap W.ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eY q x)) ∧
    (∀ (A B : Y.Opens) (h : A ≤ B) q x,
      eOY A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (Y.homOfLE h) (Y.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) J.cocomplex) q x) =
        openCohomologyRestriction h ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
          (eOY B q x)) ∧
    (∀ q x, eY q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (eX q x)) ∧
    (∀ W q x, eOY (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (eOX W q x))  := by sorry
end AlgebraicGeometry.Etale

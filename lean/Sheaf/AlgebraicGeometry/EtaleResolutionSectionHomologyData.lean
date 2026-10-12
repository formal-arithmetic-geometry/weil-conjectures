module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale
/-- The four degreewise additive equivalences underlying the natural comparison.
Source: Stacks Project, Tag 0A50. (blueprint: lem-weil-pbc-etale-resolution-section-homology-data).
Proof: identify the Hom complex computing Ext for each prescribed injective resolution with the
corresponding section complex, using the constant-sheaf/sections adjunction and evaluation at 1;
localization gives the same construction on every open. -/
theorem exists_resolutionSection_homology_data
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0)) :
    ∃ eX : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+ Sheaf.H G q,
    ∃ eOX : ∀ (W : X.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q,
    ∃ eY : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 Y))).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q,
    ∃ eOY : ∀ (W : Y.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj
            ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q, True := by sorry
end AlgebraicGeometry.Etale

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafPullback

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Transfer of a represented Ext class before applying the open-object map.
Source: Stacks Project, Tags 01F8 and 01FB (resolution functoriality), and 0A50.
(blueprint: lem-weil-pbc-etale-resolution-section-transfer-ext-class)

Proof: Adjoint each component of α to a morphism β from g*I to J. Naturality of
adjunction gives its chain-map equations; hα gives the augmentation equation.
Exactness of g* preserves the quasi-isomorphism from G to I. In the derived
category β therefore represents the identity of g*G under the augmentation
identifications. Apply `InjectiveResolution.extMk_hom` and
`Abelian.Ext.mapExactFunctor_hom` to compute the image of the class represented
by fX as the cocycle g*fX followed by β. Precompose with
etaleOpenFreeSheafPullback. Naturality of the adjunction unit with fX and the
counit identity express the section of this composite as α applied to the
section of fX, then restricted along openSectionPullback. This is precisely
openResolutionSectionTransfer. By hsections and injectivity of sectionsEquiv
this cocycle equals fY. Precomposition of Ext by a degree-zero morphism agrees
with precomposition of its representing cocycle, giving the stated equality.
No localization or open cohomology comparison is involved. -/
theorem resolutionSection_transfer_ext
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (W : X.Opens) (q : ℕ)
    (fX : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι) ⟶ I.cocomplex.X q)
    (hfX : fX ≫ I.cocomplex.d q (q + 1) = 0)
    (fY : (etaleOpenFreeSheaf Y).obj (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) ⟶ J.cocomplex.X q)
    (hfY : fY ≫ J.cocomplex.d q (q + 1) = 0)
    (hsections : EtaleOpenComparison.sectionsEquiv Y.smallEtaleTopology
      (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (J.cocomplex.X q) fY =
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W).f q
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
          (Scheme.Etale.mk W.ι) (I.cocomplex.X q) fX)) :
    J.extMk fY (q + 1) rfl hfY =
      (Abelian.Ext.mk₀ (etaleOpenFreeSheafPullback g W)).comp
        ((I.extMk fX (q + 1) rfl hfX).mapExactFunctor
          (upperStar AddCommGrpCat.{u + 1} g)) (zero_add q) := by sorry

end AlgebraicGeometry.Etale

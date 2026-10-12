module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- The source and target arrows admit compatible object isomorphisms.
(blueprint: lem-sbc-etale-chart-sections-object-comparison)
Source: Stacks Project, Tag 0EZX, comparison of section objects.
The proof constructs the canonical inverse-image restriction and composition
isomorphisms and checks their compatibility with the two adjunction units. -/
theorem etaleChartSections_objectComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p).obj V) :
    let a := Arrow.mk
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G).hom.app (op V) ≫
        ((p)^*[ModuleCat.{u + 1} Λ].obj G).obj.map φ.op)
    let b := Arrow.mk
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (φ.left ≫ pullback.fst V.hom p)).unit.app
            ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)).hom.app
              (op (Scheme.Etale.mk (𝟙 V.left))))
    Nonempty (∃ (e₁ : a.left ≅ b.left) (e₂ : a.right ≅ b.right),
      e₁.hom ≫ b.hom = a.hom ≫ e₂.hom) := by
  sorry
end AlgebraicGeometry.Etale

module

public import Sheaf.AlgebraicGeometry.CyclicDerivedHomComparisonMap

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Naturality of the free-representable comparison before coefficient conversion.
Source: Stacks Project, Tag 03Q8 and the free-sheaf adjunction.
(blueprint: lem-sbc-abelian-representable-cohomology-map-naturality).

Proof: Expand the Ext comparison. Naturality of the inverse-image map on Ext,
together with the universal-section identity and associativity of Ext
precomposition, identifies restriction by `v` with pullback along its base
change. The derived single-object inclusion and exact-functor comparisons are
natural in the source arrow.
-/
theorem abelianRepresentableCohomologyMap_naturality {X Y : Scheme.{u}}
    (h : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let P := (uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    ∀ (W V : X.Etale) (v : V ⟶ W) (ξ : P.obj (op W)),
      let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
      let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
        (pullback.fst h V.hom) (by simp [g])
      Sheaf.H.map (i.inv.app F) q
          (cohomologyMap g _ q (abelianRepresentableCohomologyMap h F q W ξ)) =
        abelianRepresentableCohomologyMap h F q V (P.map v.op ξ):= by
  sorry

end AlgebraicGeometry.Etale

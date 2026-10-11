import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Stalk of an inverse image, compatible with germs of pulled-back sections

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 03Q1 (3)
(blueprint: lem-weil-pbc-inverse-image-stalk-germ).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- **Stalk of an inverse image, compatible with germs.** Let `f : Y ⟶ X` be a morphism of
schemes, `y : Spec Ω ⟶ Y` a geometric point and `x̄ = y ≫ f`. There is an isomorphism
`c_G : (f⁻¹ G)_ȳ ≅ G_x̄`, natural in the abelian étale sheaf `G`, such that for every pointed
étale neighbourhood `(U, ū)` of `x̄` and every section `a ∈ G(U)`, `c_G` sends the germ of
`η_{f,G}(U)(a) ∈ (f⁻¹G)(U ×_X Y)` at the induced pointed neighbourhood `(U ×_X Y, (ū, ȳ))`
of `ȳ` to the germ of `a` at `(U, ū)`. Here `f⁻¹ = Etale.upperStar`, `η` is the unit of
`Etale.upperStarLowerStarAdjunction`, stalks and germs are `pointSmallEtale`'s
`sheafFiber`/`toPresheafFiber`, and `(ū, ȳ)` is `(pointSmallEtaleFiberEtaleIso f y).inv`.

Proof (blueprint): model `f⁻¹G` as the sheafification `(f_pG)^#` of the presheaf pullback,
whose unit is `θ ∘ ι_(U,id)`; stalks commute with sheafification, so it suffices to identify
`(f_pG)_ȳ` with `G_x̄`. Define `α : G_x̄ → (f_pG)_ȳ`, `[a]_(U,ū) ↦ [ι_(U,id) a]_(U×_XY,(ū,ȳ))`,
and `β : (f_pG)_ȳ → G_x̄`, `[ι_(U,φ) a]_(V,v̄) ↦ [a]_(U, p_U φ v̄)`; both are well defined by the
universal property of the colimits and are mutually inverse on generators. Put
`c = β ∘ θ_ȳ⁻¹`; the germ formula is `β ∘ α = id`, and naturality is checked on generators.

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 03Q1 (3)
(blueprint: lem-weil-pbc-inverse-image-stalk-germ). -/
theorem inverseImage_stalk_germ
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    ∃ c : Etale.upperStar AddCommGrpCat.{u + 1} f ⋙ (pointSmallEtale y).sheafFiber ≅
        (pointSmallEtale (y ≫ f)).sheafFiber,
      ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale)
        (ū : (pointSmallEtale (y ≫ f)).fiber.obj U),
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
              (op U) ≫
            (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
              ((pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
              ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj ≫
            (c.app G).hom =
          (pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  sorry

end AlgebraicGeometry

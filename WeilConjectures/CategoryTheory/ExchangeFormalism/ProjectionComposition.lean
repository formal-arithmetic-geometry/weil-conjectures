/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.CategoryTheory.ExchangeFormalism.ProjectionExchange

/-!
# The exceptional projection morphisms and the composition isomorphisms

Let `F` be an exchange formalism whose categories are monoidal and whose pullbacks are monoidal,
compatibly with the composition isomorphisms. For a factorization `X ⟶[i] W ⟶[p] S` of `h` with
`i` an open immersion, the *exceptional projection morphism*
`PF_{i,p} : p_* i_! K ⊗ B ⟶ p_* i_! (K ⊗ h^* B)`
(`CategoryTheory.ExchangeFormalism.shriekProjection`) is the projection morphism of `p^* ⊣ p_*`,
followed by the inverse of the projection comparison of `i_! ⊣ i^*` and the identification
`i^* p^* ≅ h^*`.

The composition isomorphism of a triangle of factorizations intertwines these morphisms
(`CategoryTheory.ExchangeFormalism.compIso_hom_app_whiskerRight_comp_shriekProjection`): this is
the compatibility of the projection formula with the composition of compactly supported direct
images (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2).

-/

@[expose] public section

universe w v₁ v u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪) [∀ X, MonoidalCategory (F.obj X)]
  [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal]

/-- The exceptional projection morphism `PF_{i,p} : p_* i_! K ⊗ B ⟶ p_* i_! (K ⊗ h^* B)` of a
factorization `X ⟶[i] W ⟶[p] S` of `h`: the projection morphism of `p^* ⊣ p_*`, the inverse of the
projection comparison of `i_! ⊣ i^*` and the identification `i^* p^* ≅ h^*`. -/
noncomputable def shriekProjection {X W S : 𝒞} (i : X ⟶ W) [Fact (𝒪 i)] (p : W ⟶ S) (h : X ⟶ S)
    (w : i ≫ p = h) [∀ K N, IsIso ((F.shAdj i).projectionComparison K N)] (K : F.obj X)
    (B : F.obj S) :
    (F.shriek i p).obj K ⊗ B ⟶ (F.shriek i p).obj (K ⊗ (F.pb h).obj B) :=
  (F.adj p).projectionMorphism ((F.sh i).obj K) B ≫
    (F.pf p).map (inv ((F.shAdj i).projectionComparison K ((F.pb p).obj B)) ≫
      (F.sh i).map (K ◁ (F.pbComp' i p h w).inv.app B))

/-- **The composition isomorphism intertwines the exceptional projection morphisms** (blueprint
`prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2): for a triangle of factorizations `T` of
`f : X ⟶ Y` and `g : Y ⟶ S`, through the composition isomorphism
`(i₁, p₁)_! ⋙ (i₂, p₂)_! ≅ (i, p)_!` and `(f ≫ g)^* ≅ g^* ⋙ f^*`, the exceptional projection
morphism of the composite factorization `(i, p)` of `f ≫ g` is that of `(i₂, p₂)` followed by
`(i₂, p₂)_!` of that of `(i₁, p₁)`. -/
theorem compIso_hom_app_whiskerRight_comp_shriekProjection
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    [∀ {X Y : 𝒞} (j : X ⟶ Y) [Fact (𝒪 j)] (K : F.obj X) (N : F.obj Y),
      IsIso ((F.shAdj j).projectionComparison K N)]
    {X Y S : 𝒞} (T : ShriekTriangle 𝒪 X Y S)
    [IsIso (F.baseChange T.p₁ T.q T.i₂ T.r T.w).natTrans]
    [IsIso (F.exchange T.p₁ T.q T.i₂ T.r T.w).natTrans]
    {f : X ⟶ Y} {g : Y ⟶ S} (hf : T.i₁ ≫ T.p₁ = f) (hg : T.i₂ ≫ T.p₂ = g)
    (hfg : T.i ≫ T.p = f ≫ g) (K : F.obj X) (B : F.obj S) :
    (F.compIso T).hom.app K ▷ B ≫ F.shriekProjection T.i T.p (f ≫ g) hfg K B ≫
        (F.shriek T.i T.p).map (K ◁ (F.pbComp f g).hom.app B) =
      F.shriekProjection T.i₂ T.p₂ g hg ((F.shriek T.i₁ T.p₁).obj K) B ≫
        (F.shriek T.i₂ T.p₂).map (F.shriekProjection T.i₁ T.p₁ f hf K ((F.pb g).obj B)) ≫
        (F.compIso T).hom.app (K ⊗ (F.pb f).obj ((F.pb g).obj B)) := by
  sorry

end CategoryTheory.ExchangeFormalism

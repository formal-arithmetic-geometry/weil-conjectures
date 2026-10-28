/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange
public import WeilConjectures.PoincareDuality.ProjectionCoherence

/-!
# The exchange map and the projection formulas in an exchange formalism

Let `F` be an exchange formalism whose categories are monoidal and whose pullbacks are monoidal,
compatibly with the composition isomorphisms. For a commutative square `t ≫ r = l ≫ b` with `l`
and `r` open immersions whose base change map is an isomorphism,
```
U' --t--> U
|l        |r
Z' --b--> Z
```
the exchange map `r_! t_* ⟶ b_* l_!` intertwines the projection formulas: the projection morphism
of `t^* ⊣ t_*` read through the projection formula of `r_!` and the projection morphism of
`b^* ⊣ b_*` read through the projection formula of `l_!`
(`CategoryTheory.ExchangeFormalism.exchange_whiskerRight_comp_projectionMorphism`; SGA 4,
Exposé XVII, 5.2.2).

-/

@[expose] public section

universe w v₁ v u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪) [∀ X, MonoidalCategory (F.obj X)]
  [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal]

variable {U' U Z' Z : 𝒞}

/-- **The exchange map intertwines the projection formulas**: for a commutative square
`t ≫ r = l ≫ b` with `l`, `r` open immersions whose base change map is an isomorphism, the
square
```
r_! t_* A ⊗ N ────ex ▷ N────▶ b_* l_! A ⊗ N ──PF_b──▶ b_* (l_! A ⊗ b^* N) ──q_l⁻¹──▶ b_* l_! (A ⊗ l^* b^* N)
      │ q_r⁻¹                                                                            │ ≅
      ▼                                                                                   ▼
r_! (t_* A ⊗ r^* N) ──r_! PF_t──▶ r_! t_* (A ⊗ t^* r^* N) ─────────────ex─────────────▶ b_* l_! (A ⊗ t^* r^* N)
```
commutes, where `ex` is the exchange map, `PF` the projection morphisms of the pullback–pushforward
adjunctions, `q` the projection comparisons of the extensions by zero and `l^* b^* ≅ t^* r^*` the
square isomorphism. -/
theorem exchange_whiskerRight_comp_projectionMorphism
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 r)]
    (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w).natTrans]
    [∀ K N, IsIso ((F.shAdj l).projectionComparison K N)]
    [∀ K N, IsIso ((F.shAdj r).projectionComparison K N)] (A : F.obj U') (N : F.obj Z) :
    (F.exchange t l r b w).natTrans.app A ▷ N ≫
        (F.adj b).projectionMorphism ((F.sh l).obj A) N ≫
        (F.pf b).map (inv ((F.shAdj l).projectionComparison A ((F.pb b).obj N)) ≫
          (F.sh l).map (A ◁ (F.sqIso t l r b w).inv.app N)) =
      inv ((F.shAdj r).projectionComparison ((F.pf t).obj A) N) ≫
        (F.sh r).map ((F.adj t).projectionMorphism A ((F.pb r).obj N)) ≫
        (F.exchange t l r b w).natTrans.app (A ⊗ (F.pb t).obj ((F.pb r).obj N)) := by
  sorry

end CategoryTheory.ExchangeFormalism

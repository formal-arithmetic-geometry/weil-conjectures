/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# The projection map of an adjunction

Let `adj : F ⊣ G` be an adjunction with `F : C ⥤ D`, let `T : C ⥤ C ⥤ C` and
`T' : D ⥤ D ⥤ D` be bifunctors (typically tensor products, written `⊗` below), let
`G' : D ⥤ C` be a functor and let `δ : G X ⊗ G' Y ⟶ G (X ⊗ Y)` be natural in `X` and `Y`.
The *projection map* is the morphism of bifunctors
```
F (K ⊗ G' M) ⟶ F K ⊗ M
```
whose transpose along `F ⊣ G` is
```
K ⊗ G' M --(η ⊗ 1)--> G (F K) ⊗ G' M --δ--> G (F K ⊗ M).
```
The typical example is a right adjoint `G = G'` with a strong monoidal structure and `δ` the
inverse of its comparison; then the projection map is an isomorphism for example when `F`
is the extension by zero along an open immersion.

## Main definitions and results

- `CategoryTheory.Adjunction.projectionMapTranspose`: the morphism
  `K ⊗ G' M ⟶ G (F K ⊗ M)` above. It is an isomorphism if the unit of `adj` and `δ` are.
- `CategoryTheory.Adjunction.projectionMap`: its transpose `F (K ⊗ G' M) ⟶ F K ⊗ M`.
- `CategoryTheory.Adjunction.isIso_map_projectionMap_app_app`: `G` of the projection map is
  an isomorphism if the unit of `adj` and `δ` are.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (G' : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj T ⟶
    (Functor.postcompose₂.obj G).obj T')

/-- The morphism `K ⊗ G' M ⟶ G (F K ⊗ M)` of bifunctors `C ⥤ D ⥤ C`, the composite
```
K ⊗ G' M --(η ⊗ 1)--> G (F K) ⊗ G' M --δ--> G (F K ⊗ M)
```
where `η` is the unit of `adj`. Its transpose is `Adjunction.projectionMap`. -/
noncomputable def projectionMapTranspose :
    (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj G').obj T ⟶
      (Functor.postcompose₂.obj G).obj
        ((((Functor.whiskeringLeft₂ D).obj F).obj (𝟭 D)).obj T') :=
  (((Functor.whiskeringLeft₂ C).map adj.unit).app G').app T ≫
    (((Functor.whiskeringLeft₂ C).obj F).obj (𝟭 D)).map δ

instance isIso_projectionMapTranspose [IsIso adj.unit] [IsIso δ] :
    IsIso (adj.projectionMapTranspose G' T T' δ) := by
  dsimp only [projectionMapTranspose]
  infer_instance

/-- The **projection map** `F (K ⊗ G' M) ⟶ F K ⊗ M` of bifunctors `C ⥤ D ⥤ D`: the transpose
along `F ⊣ G` of `Adjunction.projectionMapTranspose`, that is the composite
```
F (K ⊗ G' M) --F(φ)--> F (G (F K ⊗ M)) --ε--> F K ⊗ M
```
where `φ = (η ⊗ 1) ≫ δ` is `Adjunction.projectionMapTranspose` and `ε` is the counit of
`adj`. -/
noncomputable def projectionMap :
    (Functor.postcompose₂.obj F).obj ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj G').obj T) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj (𝟭 D)).obj T' :=
  (Functor.postcompose₂.obj F).map (adj.projectionMapTranspose G' T T' δ) ≫
    (Functor.postcompose₂.map adj.counit).app _

/-- The components of the projection map are the transposes along `F ⊣ G` of the components
`φ` of `Adjunction.projectionMapTranspose`:
```
F (K ⊗ G' M) --F(φ)--> F (G (F K ⊗ M))
        \                    |
         \                   | ε
       projection            v
           ----------->  F K ⊗ M
```
-/
lemma projectionMap_app_app (K : C) (M : D) :
    ((adj.projectionMap G' T T' δ).app K).app M =
      (adj.homEquiv _ _).symm (((adj.projectionMapTranspose G' T T' δ).app K).app M) := by
  simp [projectionMap, homEquiv_counit]

/-- `G` of the projection map, preceded by the unit, is `Adjunction.projectionMapTranspose`:
```
K ⊗ G' M ---------η---------> G (F (K ⊗ G' M))
        \                             |
         \                            | G(projection)
          φ                           v
           ------------------>  G (F K ⊗ M)
```
-/
@[reassoc]
lemma unit_app_comp_map_projectionMap_app_app (K : C) (M : D) :
    adj.unit.app _ ≫ G.map (((adj.projectionMap G' T T' δ).app K).app M) =
      ((adj.projectionMapTranspose G' T T' δ).app K).app M := by
  refine (adj.homEquiv_unit _ _ _).symm.trans ?_
  rw [projectionMap_app_app]
  exact Equiv.apply_symm_apply _ _

/-- `G` of the projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` is an isomorphism if the unit of
`F ⊣ G` and `δ` are. -/
lemma isIso_map_projectionMap_app_app [IsIso adj.unit] [IsIso δ] (K : C) (M : D) :
    IsIso (G.map (((adj.projectionMap G' T T' δ).app K).app M)) := by
  rw [(IsIso.eq_inv_comp _).2 (adj.unit_app_comp_map_projectionMap_app_app G' T T' δ K M)]
  infer_instance

end CategoryTheory.Adjunction

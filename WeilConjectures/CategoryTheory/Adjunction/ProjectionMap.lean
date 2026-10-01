/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# The projection map of an adjunction

Let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, let `T_C : C ⥤ C ⥤ C` and
`T_D : D ⥤ D ⥤ D` be bifunctors, and let `φ : F (T_D a b) ⟶ T_C (F a) (F b)` be a natural
transformation of bifunctors `D ⥤ D ⥤ C`. We construct the projection map
`T_D (G M) L ⟶ G (T_C M (F L))`, natural in `M` in `C` and `L` in `D`. It is the transpose
along `adj` of the composite in the diagram
```
 F (T_D (G M) L) ──── (adj.homEquiv _ _).symm (projection map) ────▶ T_C M (F L)
        │                                                                ▲
        │ φ                                                              │ T_C (ε_M) (𝟙 (F L))
        ▼                                                                │
 T_C (F (G M)) (F L) ════════════════════════════════════════ T_C (F (G M)) (F L)
```
where `ε` is the counit of `adj`. When `T_C` and `T_D` are tensor products and `φ` is the
oplax monoidal structure of `F`, this is the classical projection map
`G M ⊗ L ⟶ G (M ⊗ F L)`.

## Main definitions and results

- `CategoryTheory.Adjunction.projectionMap adj φ`: the projection map, as a natural
  transformation of bifunctors `C ⥤ D ⥤ D`.
- `CategoryTheory.Adjunction.homEquiv_symm_projectionMap_app_app`: its transpose along `adj`
  is `φ` followed by the counit of `adj` in the first variable.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The projection map `T_D (G M) L ⟶ G (T_C M (F L))` attached to an adjunction `F ⊣ G` and
a comparison `φ : F (T_D a b) ⟶ T_C (F a) (F b)`, as a natural transformation of bifunctors
`C ⥤ D ⥤ D`. It is the transpose along `adj` of
`(φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L)`, see
`CategoryTheory.Adjunction.homEquiv_symm_projectionMap_app_app`. -/
def projectionMap :
    G ⋙ T_D ⟶ (postcompose₂.obj G).obj ((((whiskeringLeft₂ C).obj (𝟭 C)).obj F).obj T_C) where
  app M :=
    { app L := adj.homEquiv _ _
        ((φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L))
      naturality L L' f := by
        dsimp
        rw [← homEquiv_naturality_left, ← homEquiv_naturality_right]
        congr 1
        simpa using (φ.app (G.obj M)).naturality_assoc f ((T_C.map (adj.counit.app M)).app _) }
  naturality M M' f := by
    ext L
    dsimp
    rw [← homEquiv_naturality_left, ← homEquiv_naturality_right]
    congr 1
    simpa [← NatTrans.comp_app, ← Functor.map_comp] using NatTrans.naturality_app_assoc φ L
      (G.map f) ((T_C.map (adj.counit.app M')).app (F.obj L))

lemma projectionMap_app_app (M : C) (L : D) :
    ((adj.projectionMap φ).app M).app L = adj.homEquiv _ _
      ((φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L)) :=
  rfl

/-- The transpose along `adj : F ⊣ G` of the projection map
`T_D (G M) L ⟶ G (T_C M (F L))` is the composite
```
 F (T_D (G M) L) ──── (adj.homEquiv _ _).symm (projection map) ────▶ T_C M (F L)
        │                                                                ▲
        │ φ                                                              │ T_C (ε_M) (𝟙 (F L))
        ▼                                                                │
 T_C (F (G M)) (F L) ════════════════════════════════════════ T_C (F (G M)) (F L)
```
-/
@[simp, reassoc]
lemma homEquiv_symm_projectionMap_app_app (M : C) (L : D) :
    (adj.homEquiv _ _).symm (((adj.projectionMap φ).app M).app L) =
      (φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L) :=
  Equiv.symm_apply_apply _ _

/-- The counit form of `CategoryTheory.Adjunction.homEquiv_symm_projectionMap_app_app`:
applying `F` to the projection map and composing with the counit of `adj` gives
`φ` followed by the counit of `adj` in the first variable. -/
@[reassoc]
lemma map_projectionMap_app_app_comp_counit (M : C) (L : D) :
    F.map (((adj.projectionMap φ).app M).app L) ≫ adj.counit.app _ =
      (φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L) := by
  simpa [homEquiv_counit] using adj.homEquiv_symm_projectionMap_app_app φ M L

end CategoryTheory.Adjunction

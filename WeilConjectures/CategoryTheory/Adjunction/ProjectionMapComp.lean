/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# The right adjoint projection map and composition of adjunctions

Let `adj₁ : F₁ ⊣ G₁` and `adj₂ : F₂ ⊣ G₂` be adjunctions with `F₁ : D ⥤ E` and `F₂ : E ⥤ C`,
and let `φ₁`, `φ₂` be comparisons `F(a ⊗ b) ⟶ F a ⊗ F b` for bifunctors `T_D`, `T_E`, `T_C`.
The right adjoint projection map (`CategoryTheory.Adjunction.rightAdjointProjectionMap`) of
the composite adjunction `adj₁.comp adj₂`, for the composite comparison, is the composite of the
projection maps of `adj₁` and `adj₂`
(`CategoryTheory.Adjunction.comp_rightAdjointProjectionMap_app_app`).

The projection map is also invariant under replacing the left adjoint by an isomorphic functor:
if `e : F ≅ F'`, `adj : F ⊣ G` and `adj' : F' ⊣ G'`, and the comparison `φ` of `F` is the
transport of the comparison `φ'` of `F'` along `e`, then the projection maps of `adj` and `adj'`
are isomorphic as arrows (`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_iff`).

Finally, for `X` such that the unit of `adj` is an isomorphism at `X` and at `T_D X Y` and the
comparison `φ` is an isomorphism at `(X, Y)`, the projection map at `(F X, Y)` is an isomorphism
(`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_obj_app`).

## Main definitions and results

- `CategoryTheory.Adjunction.compComparison e φ₁ φ₂`: the comparison of `F` obtained from the
  comparisons `φ₁` of `F₁` and `φ₂` of `F₂` and an isomorphism `e : F ≅ F₁ ⋙ F₂`.
- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_iff_comp`: if the
  comparison `φ` of `F` is `compComparison e φ₁ φ₂`, the projection map of `adj : F ⊣ G` at
  `(M, L)` is an isomorphism if and only if the composite of the projection maps of `adj₁` and
  `adj₂` is.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

section Comp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {F₁ : D ⥤ E} {G₁ : E ⥤ D} (adj₁ : F₁ ⊣ G₁) {F₂ : E ⥤ C} {G₂ : C ⥤ E} (adj₂ : F₂ ⊣ G₂)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_E : E ⥤ E ⥤ E}
  (φ₁ : (postcompose₂.obj F₁).obj T_D ⟶ (((whiskeringLeft₂ E).obj F₁).obj F₁).obj T_E)
  (φ₂ : (postcompose₂.obj F₂).obj T_E ⟶ (((whiskeringLeft₂ C).obj F₂).obj F₂).obj T_C)

/-- The comparison `F₂(F₁(a ⊗ b)) ⟶ F₂(F₁ a ⊗ F₁ b) ⟶ F₂(F₁ a) ⊗ F₂(F₁ b)` of the composite
`F₁ ⋙ F₂`, built from the comparisons `φ₁` of `F₁` and `φ₂` of `F₂`. -/
def compComparison₀ :
    (postcompose₂.obj (F₁ ⋙ F₂)).obj T_D ⟶
      (((whiskeringLeft₂ C).obj (F₁ ⋙ F₂)).obj (F₁ ⋙ F₂)).obj T_C :=
  (postcompose₂.obj F₂).map φ₁ ≫ (((whiskeringLeft₂ C).obj F₁).obj F₁).map φ₂

lemma compComparison₀_app_app (a b : D) :
    ((compComparison₀ φ₁ φ₂).app a).app b =
      F₂.map ((φ₁.app a).app b) ≫ (φ₂.app (F₁.obj a)).app (F₁.obj b) :=
  rfl

/-- The projection map of a composite adjunction `adj₁.comp adj₂` is the composite of the
projection maps of `adj₁` and `adj₂`:
```
  T_D (G₁ G₂ M) L ⟶ G₁ (T_E (G₂ M) (F₁ L)) ⟶ G₁ G₂ (T_C M (F₂ F₁ L)).
```
-/
lemma comp_rightAdjointProjectionMap_app_app (M : C) (L : D) :
    (((adj₁.comp adj₂).rightAdjointProjectionMap (compComparison₀ φ₁ φ₂)).app M).app L =
      ((adj₁.rightAdjointProjectionMap φ₁).app (G₂.obj M)).app L ≫
        G₁.map (((adj₂.rightAdjointProjectionMap φ₂).app M).app (F₁.obj L)) := by
  apply ((adj₁.comp adj₂).homEquiv _ _).symm.injective
  rw [homEquiv_symm_rightAdjointProjectionMap_app_app, comp_homEquiv, Equiv.symm_trans_apply]
  erw [adj₁.homEquiv_naturality_right_symm, homEquiv_symm_rightAdjointProjectionMap_app_app,
    adj₂.homEquiv_naturality_left_symm, homEquiv_symm_rightAdjointProjectionMap_app_app]
  rw [compComparison₀_app_app, Functor.map_comp, Category.assoc, Category.assoc]
  have := NatTrans.naturality_app φ₂ (F₁.obj L) (adj₁.counit.app (G₂.obj M))
  dsimp at this
  rw [reassoc_of% this]
  simp

end Comp

section Iso

variable {C D : Type*} [Category* C] [Category* D] {F F' : D ⥤ C} {G G' : C ⥤ D}
  (adj : F ⊣ G) (adj' : F' ⊣ G') {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} (e : F ≅ F')
  (φ' : (postcompose₂.obj F').obj T_D ⟶ (((whiskeringLeft₂ C).obj F').obj F').obj T_C)

/-- The transport of a comparison `φ' : F'(a ⊗ b) ⟶ F' a ⊗ F' b` along an isomorphism
`e : F ≅ F'`: the comparison `F(a ⊗ b) ≅ F'(a ⊗ b) ⟶ F' a ⊗ F' b ≅ F a ⊗ F b` of `F`. -/
def transportComparison :
    (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C :=
  (postcompose₂.map e.hom).app T_D ≫ φ' ≫
    (((whiskeringLeft₂ C).obj F').map e.inv).app T_C ≫
    (((whiskeringLeft₂ C).map e.inv).app F).app T_C

lemma transportComparison_app_app (a b : D) :
    ((transportComparison e φ').app a).app b =
      e.hom.app _ ≫ (φ'.app a).app b ≫ (T_C.obj (F'.obj a)).map (e.inv.app b) ≫
        (T_C.map (e.inv.app a)).app (F.obj b) :=
  rfl

/-- The projection maps of adjunctions `F ⊣ G` and `F' ⊣ G'` with isomorphic left adjoints
`e : F ≅ F'`, for comparisons related by `e`, agree up to the isomorphism `G ≅ G'` conjugate to
`e`. -/
lemma rightAdjointProjectionMap_transportComparison_app_app (M : C) (L : D) :
    ((adj.rightAdjointProjectionMap (transportComparison e φ')).app M).app L ≫
        G.map ((T_C.obj M).map (e.hom.app L)) ≫
        (conjugateIsoEquiv adj adj' e.symm).hom.app _ =
      (T_D.map ((conjugateIsoEquiv adj adj' e.symm).hom.app M)).app L ≫
        ((adj'.rightAdjointProjectionMap φ').app M).app L := by
  have hβ (X : C) : F'.map ((conjugateIsoEquiv adj adj' e.symm).hom.app X) ≫ adj'.counit.app X =
      e.inv.app (G.obj X) ≫ adj.counit.app X :=
    conjugateEquiv_counit adj adj' e.inv X
  apply (adj'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, hβ]
  rw [e.inv.naturality_assoc, e.inv.naturality_assoc, adj.counit_naturality,
    map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit]
  have h := NatTrans.naturality_app φ' L ((conjugateIsoEquiv adj adj' e.symm).hom.app M)
  dsimp at h
  rw [reassoc_of% h, ← NatTrans.comp_app, ← Functor.map_comp, hβ, transportComparison_app_app]
  simp only [Category.assoc, Functor.map_comp, NatTrans.comp_app]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, (T_C.map _).naturality_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id,
    ← NatTrans.comp_app, ← Functor.map_comp]

/-- The projection maps of adjunctions `F ⊣ G` and `F' ⊣ G'` with isomorphic left adjoints
`e : F ≅ F'`, for comparisons related by `e`, are isomorphisms at the same objects. -/
lemma isIso_rightAdjointProjectionMap_transportComparison_app_app_iff (M : C) (L : D) :
    IsIso (((adj.rightAdjointProjectionMap (transportComparison e φ')).app M).app L) ↔
      IsIso (((adj'.rightAdjointProjectionMap φ').app M).app L) := by
  rw [← isIso_comp_right_iff _ (G.map ((T_C.obj M).map (e.hom.app L)) ≫
      (conjugateIsoEquiv adj adj' e.symm).hom.app _),
    rightAdjointProjectionMap_transportComparison_app_app, isIso_comp_left_iff]

end Iso

section CompIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {F₁ : D ⥤ E} {G₁ : E ⥤ D} (adj₁ : F₁ ⊣ G₁) {F₂ : E ⥤ C} {G₂ : C ⥤ E} (adj₂ : F₂ ⊣ G₂)
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_E : E ⥤ E ⥤ E} (e : F ≅ F₁ ⋙ F₂)
  (φ₁ : (postcompose₂.obj F₁).obj T_D ⟶ (((whiskeringLeft₂ E).obj F₁).obj F₁).obj T_E)
  (φ₂ : (postcompose₂.obj F₂).obj T_E ⟶ (((whiskeringLeft₂ C).obj F₂).obj F₂).obj T_C)

/-- The comparison `F(a ⊗ b) ⟶ F a ⊗ F b` of a functor `F` with an isomorphism
`e : F ≅ F₁ ⋙ F₂`, obtained from the comparisons `φ₁` of `F₁` and `φ₂` of `F₂`:
```
  F(a ⊗ b) ≅ F₂(F₁(a ⊗ b)) ⟶ F₂(F₁ a ⊗ F₁ b) ⟶ F₂(F₁ a) ⊗ F₂(F₁ b) ≅ F a ⊗ F b.
```
-/
def compComparison :
    (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C :=
  transportComparison e (compComparison₀ φ₁ φ₂)

lemma compComparison_app_app (a b : D) :
    ((compComparison e φ₁ φ₂).app a).app b =
      e.hom.app _ ≫ F₂.map ((φ₁.app a).app b) ≫ (φ₂.app (F₁.obj a)).app (F₁.obj b) ≫
        (T_C.obj (F₂.obj (F₁.obj a))).map (e.inv.app b) ≫ (T_C.map (e.inv.app a)).app (F.obj b) :=
  by simp [compComparison, transportComparison_app_app, compComparison₀_app_app]

/-- If the comparison of `F` is obtained from those of `F₁` and `F₂` through an isomorphism
`F ≅ F₁ ⋙ F₂`, the projection map of `adj : F ⊣ G` at `(M, L)` is an isomorphism if and only if
the composite of the projection maps of `adj₁` and `adj₂`
```
  T_D (G₁ G₂ M) L ⟶ G₁ (T_E (G₂ M) (F₁ L)) ⟶ G₁ G₂ (T_C M (F₂ F₁ L))
```
is. -/
lemma isIso_rightAdjointProjectionMap_compComparison_app_app_iff (M : C) (L : D) :
    IsIso (((adj.rightAdjointProjectionMap (compComparison e φ₁ φ₂)).app M).app L) ↔
      IsIso (((adj₁.rightAdjointProjectionMap φ₁).app (G₂.obj M)).app L ≫
        G₁.map (((adj₂.rightAdjointProjectionMap φ₂).app M).app (F₁.obj L))) := by
  rw [← comp_rightAdjointProjectionMap_app_app]
  exact isIso_rightAdjointProjectionMap_transportComparison_app_app_iff adj (adj₁.comp adj₂) e
    (compComparison₀ φ₁ φ₂) M L

end CompIso

section Unit

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The projection map at `(F X, Y)`, preceded by the unit of `adj` at `X`, is the unit of `adj`
at `T_D X Y` followed by `G` of the comparison `φ`:
```
  T_D X Y ─────η────▶ G F (T_D X Y)
     │                     │
     │ T_D(η) Y            │ G(φ)
     ▼                     ▼
  T_D (G F X) Y ──proj──▶ G (T_C (F X) (F Y))
```
-/
@[reassoc]
lemma map_unit_app_comp_rightAdjointProjectionMap_app_obj_app (X Y : D) :
    (T_D.map (adj.unit.app X)).app Y ≫ ((adj.rightAdjointProjectionMap φ).app (F.obj X)).app Y =
      adj.unit.app ((T_D.obj X).obj Y) ≫ G.map ((φ.app X).app Y) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm]
  erw [homEquiv_symm_rightAdjointProjectionMap_app_app]
  erw [← homEquiv_unit, Equiv.symm_apply_apply]
  have h := NatTrans.naturality_app φ Y (adj.unit.app X)
  dsimp at h
  rw [reassoc_of% h, ← NatTrans.comp_app, ← Functor.map_comp, left_triangle_components,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id]

/-- The projection map of `adj` at `(F X, Y)` is an isomorphism if the unit of `adj` is an
isomorphism at `X` and at `T_D X Y`, and the comparison `φ` is an isomorphism at `(X, Y)`. -/
lemma isIso_rightAdjointProjectionMap_app_obj_app (X Y : D) [IsIso (adj.unit.app X)]
    [IsIso (adj.unit.app ((T_D.obj X).obj Y))] [IsIso ((φ.app X).app Y)] :
    IsIso (((adj.rightAdjointProjectionMap φ).app (F.obj X)).app Y) := by
  rw [← isIso_comp_left_iff ((T_D.map (adj.unit.app X)).app Y),
    map_unit_app_comp_rightAdjointProjectionMap_app_obj_app]
  infer_instance

end Unit

end CategoryTheory.Adjunction

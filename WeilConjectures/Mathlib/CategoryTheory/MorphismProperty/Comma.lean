/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Iterated slices of `MorphismProperty.Over`

For a morphism property `P` that is stable under composition and cancels on the right
(`CategoryTheory.MorphismProperty.HasOfPostcompProperty`) and an object `U : P.Over ⊤ S`,
the slice `Over U` of `P.Over ⊤ S` is equivalent to `P.Over ⊤ U.left`
(`CategoryTheory.MorphismProperty.Over.overEquiv`). This is the `MorphismProperty` analogue
of `CategoryTheory.Over.iteratedSliceEquiv`: an object of `P.Over ⊤ S` over `U` is the same
thing as an object of `P.Over ⊤ U.left`, the structure morphism satisfying `P` because `P`
cancels on the right.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C] {P : MorphismProperty C}
  [P.IsStableUnderComposition] [P.HasOfPostcompProperty P] {S : C} (U : P.Over ⊤ S)

/-- An object `t` of `P.Over ⊤ S` over `U`, read as an object of `P.Over ⊤ U.left`: the
structure morphism is `t.hom.left`, which satisfies `P` since `P` cancels on the right in
the commuting triangle

```
  t.left.left ──t.hom.left──→ U.left
        │                       │
        │ t.left.hom            │ U.hom
        ↓                       ↓
        S ═══════════════════════
```
-/
@[simps]
def Over.overEquivFunctor : CategoryTheory.Over U ⥤ P.Over ⊤ U.left where
  obj t := Over.mk ⊤ t.hom.left
    (P.of_postcomp _ U.hom U.prop (by rw [Over.w]; exact t.left.prop))
  map φ := Over.homMk φ.left.left (congrArg (fun m ↦ m.left) (CategoryTheory.Over.w φ))
  map_id _ := Over.Hom.ext rfl
  map_comp _ _ := Over.Hom.ext rfl

/-- An object `V` of `P.Over ⊤ U.left`, read as the object `V.hom ≫ U.hom` of `P.Over ⊤ S`
over `U`. This is the inverse construction to
`CategoryTheory.MorphismProperty.Over.overEquivFunctor`:

```
  V.left ────V.hom────→ U.left
        \                 │
         \ V.hom ≫ U.hom  │ U.hom
          ↘               ↓
                          S
```
-/
@[simps]
def Over.overEquivInverse : P.Over ⊤ U.left ⥤ CategoryTheory.Over U where
  obj V := CategoryTheory.Over.mk (X := U)
    (Over.homMk (A := Over.mk ⊤ (V.hom ≫ U.hom) (P.comp_mem _ _ V.prop U.prop)) V.hom rfl)
  map {V V'} ψ := CategoryTheory.Over.homMk
    (Over.homMk (A := Over.mk ⊤ (V.hom ≫ U.hom) (P.comp_mem _ _ V.prop U.prop))
      (B := Over.mk ⊤ (V'.hom ≫ U.hom) (P.comp_mem _ _ V'.prop U.prop)) ψ.left
      (by simp [← Category.assoc]))
    (Over.Hom.ext (Over.w ψ))
  map_id _ := CategoryTheory.Over.OverMorphism.ext (Over.Hom.ext rfl)
  map_comp _ _ := CategoryTheory.Over.OverMorphism.ext (Over.Hom.ext rfl)

/-- **The slice of `P.Over ⊤ S` at `U` is `P.Over ⊤ U.left`**: an object `t` of
`P.Over ⊤ S` equipped with a morphism to `U` is the same thing as the object `t.hom.left`
of `P.Over ⊤ U.left`, and conversely `V : P.Over ⊤ U.left` corresponds to
`V.hom ≫ U.hom : V.left ⟶ S` over `U`; see the triangles in the docstrings of
`CategoryTheory.MorphismProperty.Over.overEquivFunctor` and
`CategoryTheory.MorphismProperty.Over.overEquivInverse`. Both functors are the identity on
the underlying objects of `C`. -/
@[simps! functor inverse]
def Over.overEquiv : CategoryTheory.Over U ≌ P.Over ⊤ U.left where
  functor := Over.overEquivFunctor U
  inverse := Over.overEquivInverse U
  unitIso := NatIso.ofComponents
    (fun t ↦ CategoryTheory.Over.isoMk
      (Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w t.hom)))
      (Over.Hom.ext (Category.id_comp _)))
    (fun _ ↦ CategoryTheory.Over.OverMorphism.ext
      (Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)))
  counitIso := NatIso.ofComponents (fun _ ↦ Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ ↦ Over.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))
  functor_unitIso_comp _ := Over.Hom.ext (Category.comp_id _)

/-- The composite `P.Over ⊤ U.left ⥤ Over U ⥤ P.Over ⊤ S` is postcomposition with `U.hom`:

```
  P.Over ⊤ U.left ──overEquiv.inverse──→ Over U
                \                          │
                 \ Over.map ⊤ U.prop       │ Over.forget U
                  ↘                        ↓
                                     P.Over ⊤ S
```
-/
def Over.overEquivInverseCompForgetIso :
    (Over.overEquiv U).inverse ⋙ CategoryTheory.Over.forget U ≅ Over.map ⊤ U.prop :=
  NatIso.ofComponents (fun _ ↦ Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun _ ↦ Over.Hom.ext (by simp [Over.overEquiv]))

/-! ### Comparison of morphisms across the equivalence

The two lemmas below express that the equivalence `overEquiv` matches the morphisms into
`t : Over U` with the morphisms into `(overEquiv U).functor.obj t`; they are what makes the
comparison of covering families on the two sides mechanical. -/

/-- A morphism `g : V ⟶ (overEquiv U).functor.obj t` of `P.Over ⊤ U.left` and a morphism
`h` of `P.Over ⊤ S` into `t.left` with the same underlying morphism determine the same
morphism of `Over U`, up to the canonical isomorphism of the sources. -/
lemma Over.overEquiv_functor_map_homMk {t : CategoryTheory.Over U} {V : P.Over ⊤ U.left}
    (g : V ⟶ (Over.overEquiv U).functor.obj t)
    (h : Over.mk ⊤ (V.hom ≫ U.hom) (P.comp_mem _ _ V.prop U.prop) ⟶ t.left)
    (hh : h.left = g.left) :
    (Over.overEquiv U).functor.map
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (h ≫ t.hom)) h) =
      (Over.isoMk (Iso.refl _) (show 𝟙 _ ≫ V.hom = h.left ≫ t.hom.left by
        rw [Category.id_comp, hh]; exact (Over.w g).symm) :
        (Over.overEquiv U).functor.obj (CategoryTheory.Over.mk (h ≫ t.hom)) ≅ V).hom ≫ g :=
  Over.Hom.ext (hh.trans (Category.id_comp _).symm)

/-- A morphism `h` of `P.Over ⊤ S` into `((overEquiv U).inverse.obj V).left` determines a
morphism into `V` of `P.Over ⊤ U.left`, whose image under `(overEquiv U).inverse` is the
morphism of `Over U` determined by `h`, up to the canonical isomorphism of the sources. -/
lemma Over.overEquiv_inverse_map_homMk {V : P.Over ⊤ U.left} {W : P.Over ⊤ S}
    (h : W ⟶ ((Over.overEquiv U).inverse.obj V).left) (hW : P (h.left ≫ V.hom)) :
    (Over.overEquiv U).inverse.map
        (Over.homMk (A := Over.mk ⊤ (h.left ≫ V.hom) hW) h.left rfl) =
      (CategoryTheory.Over.isoMk
        (Over.isoMk (Iso.refl _) (show 𝟙 _ ≫ W.hom = (h.left ≫ V.hom) ≫ U.hom by
          rw [Category.id_comp, Category.assoc]; exact (Over.w h).symm))
        (Over.Hom.ext (Category.id_comp _)) :
          (Over.overEquiv U).inverse.obj (Over.mk ⊤ (h.left ≫ V.hom) hW) ≅
            CategoryTheory.Over.mk (h ≫ ((Over.overEquiv U).inverse.obj V).hom)).hom ≫
        CategoryTheory.Over.homMk
          (U := CategoryTheory.Over.mk (h ≫ ((Over.overEquiv U).inverse.obj V).hom)) h :=
  CategoryTheory.Over.OverMorphism.ext (Over.Hom.ext (Category.id_comp _).symm)

end CategoryTheory.MorphismProperty

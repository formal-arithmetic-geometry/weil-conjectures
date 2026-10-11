/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!

# Transposing the image of a counit under a composed adjunction

Let `adj : L ⊣ R` and `adjS : S ⊣ S'` be adjunctions with `L : D ⥤ C`, `R : C ⥤ D`,
`S : C ⥤ E` and `S' : E ⥤ C`, so that `adj.comp adjS : L ⋙ S ⊣ S' ⋙ R`. For an object `Y`
of `C` the counit `adj.counit.app Y : L (R Y) ⟶ Y` gives, after applying `S`, a morphism
`S (L (R Y)) ⟶ S Y` out of `(L ⋙ S) (R Y)`, and this file computes its transpose along
`adj.comp adjS`: it is the image under `R` of the transpose along `adjS`.

We also record that representability of a presheaf `F` by `Y` gives representability of its
restriction `L.op ⋙ F` along a left adjoint `L ⊣ R` by `R.obj Y`.

## Main results

- `CategoryTheory.Adjunction.comp_homEquiv_map_counit_app_comp`.
- `CategoryTheory.Functor.RepresentableBy.ofAdjunction`.
- `CategoryTheory.Adjunction.comp_map_counit_eq_comp_homEquiv_symm`: composing with a counit
  read through an identification of a right adjoint with a left adjoint factors through a unit.

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
  {S : C ⥤ E} {S' : E ⥤ C} (adjS : S ⊣ S')

/-- The transpose along `adj.comp adjS : L ⋙ S ⊣ S' ⋙ R` of the morphism
`S (ε_Y) ≫ g : S (L (R Y)) ⟶ M` is the image under `R` of the transpose of `g` along
`adjS`, where `ε` is the counit of `adj : L ⊣ R`. Both sides are morphisms
`R Y ⟶ R (S' M)`, and the equality between them is the naturality square of the unit `η` of
`adjS` at `ε_Y`
```
                     η_{L (R Y)}
     L (R Y) --------------------------> S' (S (L (R Y)))
        |                                       |
       ε_Y                              S' (S (ε_Y))
        ↓                                       ↓
        Y ------------------------------> S' (S Y)
                         η_Y
```
composed with the right triangle identity of `adj`, which says that
`R Y ⟶ R (L (R Y)) ⟶ R Y` is the identity. -/
theorem comp_homEquiv_map_counit_app_comp (Y : C) (M : E) (g : S.obj Y ⟶ M) :
    (adj.comp adjS).homEquiv (R.obj Y) M (S.map (adj.counit.app Y) ≫ g) =
      R.map (adjS.homEquiv Y M g) := by
  have h := adjS.unit.naturality (adj.counit.app Y)
  dsimp at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [S'.map_comp, ← Category.assoc, ← h, Category.assoc, R.map_comp, ← Category.assoc,
    adj.right_triangle_components, Category.id_comp]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {L : D ⥤ C}
  {R : C ⥤ D} {F : Cᵒᵖ ⥤ Type w} {Y : C}

/-- If `adj : L ⊣ R` and `Y` represents `F`, then `R.obj Y` represents `L.op ⋙ F`: a morphism
`X ⟶ R.obj Y` is a morphism `L.obj X ⟶ Y`, that is, an element of `F (L.obj X)`. The
representation is the composite
```
  (X ⟶ R.obj Y) --(adj.homEquiv X Y).symm--> (L.obj X ⟶ Y) --r.homEquiv--> F (L.obj X).
```

For `L = Over.map p` and `R = Over.pullback p` this says that the base change of a representing
object represents the restriction of the functor to the slice. -/
@[simps]
def ofAdjunction (r : F.RepresentableBy Y) (adj : L ⊣ R) :
    (L.op ⋙ F).RepresentableBy (R.obj Y) where
  homEquiv {X} := (adj.homEquiv X Y).symm.trans r.homEquiv
  homEquiv_comp f g := by
    simp [Adjunction.homEquiv_naturality_left_symm, r.homEquiv_comp]

end CategoryTheory.Functor.RepresentableBy

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Let `adj₁ : L ⊣ R` and `adj₂ : S ⊣ T` be adjunctions between `C` and `D` whose right adjoint
`R` and left adjoint `S` are identified by `θ : S ≅ R`. For `e : L A ≅ B`, `σ : N ≅ S M` and
`γ : M ≅ T A`, composing a morphism `f : A ⟶ N` with the counit of `adj₂` read through `σ`
and `γ` factors through the morphism `A ⟶ R (L A) ≅ R B ≅ S B` given by the unit of `adj₁`:
the second factor `S B ⟶ A` is the transpose of `f` along `adj₁`, `e`, `γ` and `adj₂`. -/
theorem comp_map_counit_eq_comp_homEquiv_symm {L : D ⥤ C} {R : C ⥤ D} {S : C ⥤ D} {T : D ⥤ C}
    (adj₁ : L ⊣ R) (adj₂ : S ⊣ T) (θ : S ≅ R) {A N : D} {B M : C} (e : L.obj A ≅ B)
    (σ : N ≅ S.obj M) (γ : M ≅ T.obj A) (f : A ⟶ N) :
    f ≫ σ.hom ≫ S.map γ.hom ≫ adj₂.counit.app A =
      (adj₁.unit.app A ≫ R.map e.hom ≫ θ.inv.app B) ≫
        (adj₂.homEquiv B A).symm
          (e.inv ≫ (adj₁.homEquiv A M).symm (f ≫ (σ ≪≫ θ.app M).hom) ≫ γ.hom) := by
  have h₁ : adj₁.unit.app A ≫ R.map ((adj₁.homEquiv A M).symm (f ≫ (σ ≪≫ θ.app M).hom)) =
      f ≫ (σ ≪≫ θ.app M).hom :=
    (adj₁.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  rw [homEquiv_counit, Category.assoc, Category.assoc, ← Category.assoc (θ.inv.app B),
    ← θ.inv.naturality, Category.assoc, ← Functor.map_comp_assoc, ← Category.assoc e.hom,
    Iso.hom_inv_id, Category.id_comp, Functor.map_comp_assoc, ← Category.assoc (adj₁.unit.app A),
    h₁]
  simp

end CategoryTheory.Adjunction

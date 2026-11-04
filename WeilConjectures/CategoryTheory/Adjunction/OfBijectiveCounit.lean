/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions from a counit inducing bijections, and comparison with free objects

Let `L : C ⥤ D` and `R : D ⥤ C` be functors and `ε : R ⋙ L ⟶ 𝟭 D` a natural transformation. If for
all `X` and `Y` the map `Hom(X, R Y) ⟶ Hom(L X, Y)`, `g ↦ L g ≫ ε_Y`, is bijective, then `L ⊣ R`
with counit `ε` (`CategoryTheory.Adjunction.ofBijectiveCounit`).

To check such bijectivity on free objects, let `free₁ ⊣ forget₁` and `free₂ ⊣ forget₂` be
adjunctions and `c : L ⋙ forget₂ ≅ forget₁ ⋙ L'` an isomorphism, for functors `L` between the
categories of "structured" objects and `L'` between the underlying categories. The comparison
`β_M : free₂ (L' M) ⟶ L (free₁ M)` (`CategoryTheory.Adjunction.freeComparison`) is the adjoint of
`L' (η_M) ≫ c⁻¹`. When it is an isomorphism, the map `g ↦ L g ≫ ε` on morphisms out of `free₁ M`
is bijective if and only if the map `f ↦ L' f ≫ c⁻¹ ≫ forget₂ ε` on morphisms out of `M` is
(`CategoryTheory.Adjunction.bijective_map_comp_free_iff`).

## Main declarations

- `CategoryTheory.Adjunction.ofBijectiveCounit`
- `CategoryTheory.Adjunction.freeComparison`
- `CategoryTheory.Adjunction.bijective_map_comp_free_iff`
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Adjunction

/-- **An adjunction from a counit inducing bijections.** If `ε : R ⋙ L ⟶ 𝟭 D` is such that
`g ↦ L g ≫ ε_Y` is a bijection `Hom(X, R Y) ≃ Hom(L X, Y)` for all `X` and `Y`, then `L ⊣ R`,
with this bijection as hom-equivalence (inverted) and `ε` as counit. -/
noncomputable def ofBijectiveCounit {L : C ⥤ D} {R : D ⥤ C} (ε : R ⋙ L ⟶ 𝟭 D)
    (h : ∀ (X : C) (Y : D), Function.Bijective fun g : X ⟶ R.obj Y ↦ L.map g ≫ ε.app Y) :
    L ⊣ R :=
  mkOfHomEquiv
    { homEquiv X Y := (Equiv.ofBijective (fun g : X ⟶ R.obj Y ↦ (L.map g ≫ ε.app Y : L.obj X ⟶ Y))
        (h X Y)).symm
      homEquiv_naturality_left_symm f g := by simp
      homEquiv_naturality_right {X Y Y'} f g := by
        have := ε.naturality g
        dsimp at this
        rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, Functor.map_comp, Category.assoc, this,
          ← Category.assoc]
        exact congrArg (· ≫ g) ((Equiv.ofBijective _ (h X Y)).apply_symm_apply f).symm }

@[simp]
lemma ofBijectiveCounit_counit {L : C ⥤ D} {R : D ⥤ C} (ε : R ⋙ L ⟶ 𝟭 D)
    (h : ∀ (X : C) (Y : D), Function.Bijective fun g : X ⟶ R.obj Y ↦ L.map g ≫ ε.app Y) :
    (ofBijectiveCounit ε h).counit = ε := by
  ext Y
  simp [ofBijectiveCounit]

/-- The map `g ↦ L g ≫ ε` stays bijective after precomposition with an isomorphism. -/
lemma bijective_map_comp_iff_of_iso (L : C ⥤ D) {X X' P : C} {T : D} (ε : L.obj P ⟶ T)
    (e : X ≅ X') :
    (Function.Bijective fun g : X ⟶ P ↦ L.map g ≫ ε) ↔
      Function.Bijective fun g : X' ⟶ P ↦ L.map g ≫ ε := by
  rw [← Function.Bijective.of_comp_iff _ e.symm.homFromEquiv.bijective,
    ← Function.Bijective.of_comp_iff' (L.mapIso e).symm.homFromEquiv.bijective]
  convert Iff.rfl using 2
  ext g
  simp

variable {C' D' : Type*} [Category C'] [Category D']
  {free₁ : C' ⥤ C} {forget₁ : C ⥤ C'} (adj₁ : free₁ ⊣ forget₁)
  {free₂ : D' ⥤ D} {forget₂ : D ⥤ D'} (adj₂ : free₂ ⊣ forget₂)
  (L : C ⥤ D) (L' : C' ⥤ D') (c : L ⋙ forget₂ ≅ forget₁ ⋙ L')

/-- The comparison `free₂ (L' M) ⟶ L (free₁ M)` attached to an isomorphism
`c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`: the adjoint of `L' (η_M) ≫ c⁻¹_{free₁ M}` (a component of the
mate of `c⁻¹`). -/
noncomputable def freeComparison (M : C') : free₂.obj (L'.obj M) ⟶ L.obj (free₁.obj M) :=
  (adj₂.homEquiv _ _).symm (L'.map (adj₁.unit.app M) ≫ c.inv.app (free₁.obj M))

/-- **Bijectivity on free objects.** If the comparison `β_M : free₂ (L' M) ⟶ L (free₁ M)` is an
isomorphism, then `g ↦ L g ≫ ε` is bijective on the morphisms `free₁ M ⟶ Q` if and only if
`f ↦ L' f ≫ c⁻¹_Q ≫ forget₂ ε` is bijective on the morphisms `M ⟶ forget₁ Q`. -/
theorem bijective_map_comp_free_iff (M : C') [IsIso (freeComparison adj₁ adj₂ L L' c M)] {Q : C}
    {T : D} (ε : L.obj Q ⟶ T) :
    (Function.Bijective fun g : free₁.obj M ⟶ Q ↦ L.map g ≫ ε) ↔
      Function.Bijective fun f : M ⟶ forget₁.obj Q ↦ L'.map f ≫ c.inv.app Q ≫ forget₂.map ε := by
  have key : (adj₂.homEquiv _ _ ∘ (asIso (freeComparison adj₁ adj₂ L L' c M)).symm.homFromEquiv) ∘
      (fun g : free₁.obj M ⟶ Q ↦ L.map g ≫ ε) =
      (fun f : M ⟶ forget₁.obj Q ↦ L'.map f ≫ c.inv.app Q ≫ forget₂.map ε) ∘
        adj₁.homEquiv _ _ := by
    ext g
    have := c.inv.naturality g
    dsimp at this
    simp only [Function.comp_apply]
    rw [Iso.homFromEquiv_apply, Iso.symm_inv, asIso_hom, homEquiv_naturality_right,
      freeComparison, Equiv.apply_symm_apply, homEquiv_unit]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% this]
  rw [← Function.Bijective.of_comp_iff' ((adj₂.homEquiv _ _).bijective.comp
    (asIso (freeComparison adj₁ adj₂ L L' c M)).symm.homFromEquiv.bijective), key,
    Function.Bijective.of_comp_iff _ (adj₁.homEquiv _ _).bijective]

end Adjunction

end CategoryTheory

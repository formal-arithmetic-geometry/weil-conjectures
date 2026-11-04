/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit

/-!
# Naturality of the free comparison

For adjunctions `free₁ ⊣ forget₁`, `free₂ ⊣ forget₂` and `c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`, the
free comparison `free₂ (L' M) ⟶ L (free₁ M)` is characterized by its adjoint `L' (η_M) ≫ c⁻¹`
(`CategoryTheory.Adjunction.unit_app_comp_map_freeComparison`) and is natural in `M`
(`CategoryTheory.Adjunction.freeComparisonNatTrans`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  {free₁ : C' ⥤ C} {forget₁ : C ⥤ C'} (adj₁ : free₁ ⊣ forget₁)
  {free₂ : D' ⥤ D} {forget₂ : D ⥤ D'} (adj₂ : free₂ ⊣ forget₂)
  (L : C ⥤ D) (L' : C' ⥤ D') (c : L ⋙ forget₂ ≅ forget₁ ⋙ L')

/-- The free comparison is the adjoint of `L' (η_M) ≫ c⁻¹`. -/
@[reassoc]
lemma unit_app_comp_map_freeComparison (M : C') :
    adj₂.unit.app (L'.obj M) ≫ forget₂.map (freeComparison adj₁ adj₂ L L' c M) =
      L'.map (adj₁.unit.app M) ≫ c.inv.app (free₁.obj M) :=
  (adj₂.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The free comparison is natural in `M`. -/
@[reassoc]
lemma freeComparison_naturality {M M' : C'} (f : M ⟶ M') :
    free₂.map (L'.map f) ≫ freeComparison adj₁ adj₂ L L' c M' =
      freeComparison adj₁ adj₂ L L' c M ≫ L.map (free₁.map f) := by
  apply (adj₂.homEquiv _ _).injective
  have h := c.inv.naturality (free₁.map f)
  dsimp at h
  rw [homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_unit, homEquiv_unit,
    Category.assoc, unit_app_comp_map_freeComparison, unit_app_comp_map_freeComparison_assoc, ← h,
    ← L'.map_comp_assoc, ← L'.map_comp_assoc, unit_naturality]

/-- The free comparisons as a natural transformation `L' ⋙ free₂ ⟶ free₁ ⋙ L`. -/
@[simps]
noncomputable def freeComparisonNatTrans : L' ⋙ free₂ ⟶ free₁ ⋙ L where
  app M := freeComparison adj₁ adj₂ L L' c M
  naturality _ _ f := freeComparison_naturality adj₁ adj₂ L L' c f

end CategoryTheory.Adjunction

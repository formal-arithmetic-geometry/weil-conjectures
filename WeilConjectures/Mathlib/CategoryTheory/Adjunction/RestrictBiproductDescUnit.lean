/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctorBiproductDesc

/-!
# Biproduct decompositions by the unit of an adjunction restricted to full subcategories

Let `L ⊣ R` be an adjunction between `k`-linear categories which restricts to full
subcategories `PA` and `PB` (`CategoryTheory.Adjunction.restrictFullyFaithful`). For scalars
`b : Fin d → k`, the maps `K ⟶ R (L K)` given by the unit followed by the multiplication by
`bᵢ` exhibit `R (L K)` as `Kᵈ` in the full subcategory if and only if they do so in the ambient
category (`CategoryTheory.Adjunction.isIso_biproductDesc_restrictFullyFaithful_unit_smul_iff`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {PA : ObjectProperty A} {PB : ObjectProperty B}
  (hL : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ L).obj K))
  (hR : ∀ K : PB.FullSubcategory, PA ((PB.ι ⋙ R).obj K))
  {k : Type*} [Semiring k] [Linear k B] {d : ℕ} (b : Fin d → k)

/-- For an adjunction `L ⊣ R` restricted to full subcategories, the maps `K ⟶ R (L K)` given by
the unit followed by the multiplication by scalars `bᵢ` exhibit `R (L K)` as `Kᵈ` in the full
subcategory if and only if they do in the ambient category. -/
lemma isIso_biproductDesc_restrictFullyFaithful_unit_smul_iff (K : PA.FullSubcategory)
    [HasBiproduct fun _ : Fin d ↦ K] [HasBiproduct fun _ : Fin d ↦ K.obj] :
    IsIso (biproduct.desc fun i : Fin d ↦
      (adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
          (PB.liftCompιIso (PA.ι ⋙ L) hL).symm (PA.liftCompιIso (PB.ι ⋙ R) hR).symm).unit.app K ≫
        (PA.lift (PB.ι ⋙ R) hR).map (b i • 𝟙 ((PB.lift (PA.ι ⋙ L) hL).obj K))) ↔
    IsIso (biproduct.desc fun i : Fin d ↦ adj.unit.app K.obj ≫ R.map (b i • 𝟙 (L.obj K.obj))) := by
  have hu : ((adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
      (PB.liftCompιIso (PA.ι ⋙ L) hL).symm (PA.liftCompιIso (PB.ι ⋙ R) hR).symm).unit.app K).hom =
        adj.unit.app K.obj := by
    simpa [ObjectProperty.liftCompιIso] using map_restrictFullyFaithful_unit_app adj
      PA.fullyFaithfulι PB.fullyFaithfulι
      (PB.liftCompιIso (PA.ι ⋙ L) hL).symm (PA.liftCompιIso (PB.ι ⋙ R) hR).symm K
  rw [← isIso_iff_of_reflects_iso _ PA.ι, Functor.isIso_map_biproduct_desc_iff]
  simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, hu,
    ObjectProperty.lift_map, ObjectProperty.homMk_hom, Functor.comp_map]
  rfl

end CategoryTheory.Adjunction

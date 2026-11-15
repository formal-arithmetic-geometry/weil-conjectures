/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition

/-! # Composition coherence for Picard pullback comparisons

## References

* Stacks Project, Tags 0095 and 0096
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse tensor comparison respects pullback composition (Stacks, Tags 0095 and 0096). -/
@[reassoc]
theorem picardTensorObjIso_comp_inv
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) (M N : X.Modules) :
    (picardTensorObjIso k ((tensorPullback l).obj M) ((tensorPullback l).obj N)).inv ≫
      (tensorPullback k).map (picardTensorObjIso l M N).inv ≫
        (picardTensorCompIso k l (M ⊗ N)).hom =
    ((picardTensorCompIso k l M).hom ⊗ₘ (picardTensorCompIso k l N).hom) ≫
      (picardTensorObjIso (k ≫ l) M N).inv := by
  simp only [picardTensorObjIso, picardTensorCompIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, tensorIso_inv, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  simp only [Iso.app_inv]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [(picardTensorComparison k).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  simp only [Functor.Monoidal.μIso_hom]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [← (picardTensorComparison k).hom.naturality
      ((picardTensorComparison l).hom.app M),
    ← (picardTensorComparison k).hom.naturality ((picardTensorComparison l).hom.app N)]
  rw [← tensorHom_comp_tensorHom_assoc]
  have hc := pullbackComp_tensor_assoc k l M N
    ((picardTensorComparison (k ≫ l)).inv.app (M ⊗ N))
  simp only [Functor.Monoidal.μIso_hom] at hc
  rw [hc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]

end AlgebraicGeometry.Scheme.Modules

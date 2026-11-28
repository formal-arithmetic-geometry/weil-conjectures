/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Transposes along the derived equivalence of an equivalence

For an equivalence `E : C ≌ D` of abelian categories, the Hom bijection of the derived
equivalence `E.mapDerivedCategory` is computed on localized cochain maps by the Hom bijection
of `E` on complexes.

## Implementation details

The unit of `Equivalence.mapDerivedCategory` is adjointified, so the computation goes
through its counit, which is the composite of the canonical exact-functor isomorphisms.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Equivalence.mapDerivedCategory

namespace CategoryTheory.Equivalence
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The derived equivalence transposes a localized cochain map out of `E(K)` to the
localization of its ordinary transpose. -/
theorem mapDerivedCategory_homEquiv_Q (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive]
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (E.functor.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    E.mapDerivedCategory.toAdjunction.homEquiv _ _
        (E.functor.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((E.toAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv K L f) ≫
        E.inverse.mapDerivedCategoryFactors.inv.app L := by
  apply (E.mapDerivedCategory.toAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  change _ = E.functor.mapDerivedCategory.map _ ≫
    ((Functor.mapDerivedCategoryCompIso E.inverse E.functor).hom.app _ ≫
      (Functor.mapDerivedCategoryNatIso E.counitIso).hom.app _ ≫
      (Functor.mapDerivedCategoryIdIso D).hom.app _)
  rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj,
    Functor.mapDerivedCategoryIdIso_hom_app]
  have hu := Functor.mapDerivedCategoryNatIso_fac E.counitIso L
  have hn := E.functor.mapDerivedCategoryFactors.hom.naturality
    ((E.toAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv K L f)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc E.functor.mapDerivedCategory
    (E.inverse.mapDerivedCategoryFactors.inv.app L), Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp, reassoc_of% hn]
  erw [reassoc_of% hu, Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp]
  congr 2
  ext i
  simp [Adjunction.homEquiv_unit]

end CategoryTheory.Equivalence

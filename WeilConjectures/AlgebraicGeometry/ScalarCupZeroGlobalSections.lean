/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.ScalarTensorGlobalSectionsMorphism

/-! # Internal cup in degree zero on global sections

## References

* [Stacks Project, Tag 01DZ](https://stacks.math.columbia.edu/tag/01DZ)
* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
/-- The internal degree-zero cup evaluates to the tensor of the two global sections. -/
theorem scalarCohomologyCup_zero_globalSections
    (k : Type w) [Field k] (X : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules)
    (a : scalarCohomology f F 0) (b : scalarCohomology f G 0) :
    scalarGlobalSectionsEquiv f (F ⊗ G) (scalarCohomologyCup f F G 0 0 a b) =
      tmulSection (scalarGlobalSectionsEquiv f F a) (scalarGlobalSectionsEquiv f G b) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
      let : HasExt.{w + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
      let : MonoidalCategory (SheafOfModules.{w} X.ringCatSheaf) :=
        SheafOfModules.monoidalCategory X.sheaf
      let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      have hc : scalarCohomologyCup f F G 0 0 a b =
          (scalarGlobalSectionsEquiv f (F ⊗ G)).symm
            (tmulSection (scalarGlobalSectionsEquiv f F a)
              (scalarGlobalSectionsEquiv f G b)) := by
        apply (scalarCohomologyExtEquiv f (F ⊗ G) 0).injective
        unfold scalarCohomologyCup
        rw [AddEquiv.apply_symm_apply]
        rw [scalarCohomologyExtEquiv_zero_globalSections]
        rw [scalarCohomologyExtEquiv_zero_globalSections,
          scalarCohomologyExtEquiv_zero_globalSections]
        unfold scalarExtCup
        simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀,
          curriedTensor_obj_map, tensorRight, Functor.flip_obj_map,
          curriedTensor_map_app, Category.assoc]
        rw [← tensorHom_def_assoc]
        rw [scalarTensorCoefficient_globalSections_morphism]
        simp only [LinearEquiv.apply_symm_apply]
      rw [hc, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules

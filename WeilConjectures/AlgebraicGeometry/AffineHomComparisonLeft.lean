/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineHomComparisonGeneratorExtension

/-! # Contravariant naturality of the affine Hom comparison

## References

* Stacks Project, Tags 01HV and 0BQZ
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Generator normalization implies this affine comparison property (Stacks, Tag 01HV). -/
theorem affineHomComparison_chart_left {Y : Scheme.{u}} (U : Y.affineOpens)
    :
    ∀ (M M' N : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (f : M' ⟶ M),
        (affineHomComparison U) M N ≫ SheafOfModules.homObjMap (R :=
          U.1.toScheme.toRingedSpace.sheaf)
          ((affineHomComparisonFunctor U).map f) (𝟙 ((affineHomComparisonFunctor U).obj N)) =
        (affineHomComparisonFunctor U).map (ModuleCat.ofHom (Linear.leftComp (Γ(Y, U.1) : Type u)
          N f)) ≫ (affineHomComparison U) M' N := by
  intro M M' N f
  apply affineHomGenerator_ext U (ModuleCat.of Γ(Y, U.1) (M ⟶ N))
  intro h
  rw [← Category.assoc, affineHomComparison_generator]
  rw [affineHomSection_comp (R := U.1.toScheme.toRingedSpace.sheaf)
    ((affineHomComparisonFunctor U).map h) ((affineHomComparisonFunctor U).map f)
    (𝟙 ((affineHomComparisonFunctor U).obj N))]
  rw [Category.comp_id, ← Functor.map_comp]
  rw [← Category.assoc, affineHomGenerator_map, affineHomComparison_generator]
  rfl

end AlgebraicGeometry

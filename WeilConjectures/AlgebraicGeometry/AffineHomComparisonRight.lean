/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineHomComparisonGeneratorExtension

/-! # Covariant naturality of the affine Hom comparison

Source: Stacks Project, Tag 01HV (4)-(5), and Tag 0BQZ. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Generator normalization implies this affine comparison property (Stacks, Tag 01HV). -/
theorem affineHomComparison_chart_right {Y : Scheme.{u}} (U : Y.affineOpens)
    :
    ∀ (M N N' : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (g : N ⟶ N'),
        (affineHomComparison U) M N ≫ SheafOfModules.homObjMap (R :=
          U.1.toScheme.toRingedSpace.sheaf)
          (𝟙 ((affineHomComparisonFunctor U).obj M)) ((affineHomComparisonFunctor U).map g) =
        (affineHomComparisonFunctor U).map (ModuleCat.ofHom (Linear.rightComp (Γ(Y, U.1) : Type u)
          M g)) ≫ (affineHomComparison U) M N' := by
  intro M N N' g
  apply affineHomGenerator_ext U (ModuleCat.of Γ(Y, U.1) (M ⟶ N))
  intro h
  rw [← Category.assoc, affineHomComparison_generator]
  rw [affineHomSection_comp (R := U.1.toScheme.toRingedSpace.sheaf)
    ((affineHomComparisonFunctor U).map h)
    (𝟙 ((affineHomComparisonFunctor U).obj M)) ((affineHomComparisonFunctor U).map g)]
  rw [Category.id_comp, ← Functor.map_comp]
  rw [← Category.assoc, affineHomGenerator_map, affineHomComparison_generator]
  rfl

end AlgebraicGeometry

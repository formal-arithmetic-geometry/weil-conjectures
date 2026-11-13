/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality

/-! # Module-to-abelian comparison for structure-sheaf pullbacks

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open Modules

/-- The module-to-abelian comparisons for unit coefficients can be chosen compatibly
with pullback along every morphism over the field. No cup product is involved. -/
theorem scalar_unit_cohomology_pullback_comparison (k : Type u) [Field k] :
    ∃ e : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)),
      scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1 ≃+
        Sheaf.H (structureSheafAb X) 1,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
        (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
        (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1),
        e Y g (scalarCohomologyMap g (tensorPullbackObjUnitToUnit a) 1
          (scalarCohomologyPullback f g a h (SheafOfModules.unit X.ringCatSheaf) 1 x)) =
            structureSheafCohomologyPullback a 1 (e X f x) := by
  let e := fun (X : Scheme.{u}) (_f : X ⟶ Spec (CommRingCat.of k)) ↦
    AddEquiv.ofBijective (scalarUnitAbelianComparison X)
      (scalar_unit_abelian_comparison_bijective X)
  refine ⟨e, ?_⟩
  intro X Y f g a h x
  exact scalar_unit_cohomology_pullback_naturality k f g a h x

end AlgebraicGeometry.Scheme

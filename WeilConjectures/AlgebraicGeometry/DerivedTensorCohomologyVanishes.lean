/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Single

/-! # Vanishing of derived tensor cohomology on a scheme

## References

* Stacks Project, Tags 06YS, 06YU and 08EA
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 256 in
/-- Vanishing of `H^i(E ⊗ᴸ F)`, expressed by a K-flat representative `P` of `E` whose total
tensor with `F` in degree zero has zero cohomology in degree `i`
(Stacks, Tags 06YS, 06YU and 08EA). -/
def schemeDerivedTensorCohomologyVanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ E) ∧
      IsZero ((CochainComplex.mapBifunctor P
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (curriedTensor _)).homology i)

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # Vanishing of derived tensor cohomology for two derived objects

## References

* Stacks Project, Tags 06YS, 06YU and 09M4
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 256 in
/-- Vanishing of `H^i(E ⊗ᴸ L)` for two objects of `D(𝒪_X)`: there are a K-flat representative
`K` of `E` and a complex `N` representing `L` such that `Tot(K ⊗ N)` has zero cohomology in
degree `i` (Stacks, Tags 06YS, 06YU and 09M4). -/
def schemeDerivedTensorComplexCohomologyVanishes (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E L : schemeDerivedCategory X) (i : ℤ) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  ∃ K N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) K ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      Nonempty (DerivedCategory.Q.obj N ≅ L) ∧
      IsZero ((CochainComplex.mapBifunctor K N (curriedTensor _)).homology i)

end AlgebraicGeometry

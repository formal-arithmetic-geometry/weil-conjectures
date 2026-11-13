/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.UniformInverseAffineSectionsBound
import WeilConjectures.AlgebraicGeometry.DirectImageHomologyAffineDetection
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Uniform upper cohomological bound for quasi-coherent derived direct image

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Uniform vanishing for nonpositive quasi-coherent derived objects. -/
theorem uniform_bound_core
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, 0 < N ∧
      ∀ E : schemeDerivedQCohCategory X,
        (∀ m : ℤ, 0 < m → IsZero
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj)) →
        ∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj) := by
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  obtain ⟨N, hpos, hN⟩ := exists_uniform_inverse_affine_sections_bound f
  refine ⟨(N : ℤ), by omega, ?_⟩
  intro E hE m hm
  apply isZero_schemeHigherDirectImage_of_affine_sections f E.obj m
  intro U hU
  let F := RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ U)
  let : PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp [F, RingedSpace.openModuleSections]
    infer_instance
  exact isZero_homology_rightDerivedFunctor_of_cohomological_bound
    X F N (hN U hU) 0 E.obj E.property hE m (by omega)

end AlgebraicGeometry

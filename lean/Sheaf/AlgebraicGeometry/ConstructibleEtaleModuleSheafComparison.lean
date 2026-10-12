/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-!
# Comparing constructibility of etale module sheaves

Source: Stacks Project, Tags 095E (3), 03RU and 09XZ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The finite-constant-value and finite-stalk definitions of constructibility agree
for module sheaves over a finite commutative ring.

Source: Stacks Project, Tags 095E (3), 03RU and 09XZ, and the global stratification
convention of `IsConstructibleEtaleModuleSheaf` and `IsConstructibleSheaf`.
(blueprint: lem-weil-pbc-constructible-etale-module-sheaf-comparison).

Proof:
Copy the identical partition, domains, immersions and range equalities between the
two stratification records. Constructibility of the strata is already a field of the
underlying topological stratification. On each stratum apply the first equivalence of
`finite_locally_constant_module_values_iff` (blueprint dependency
`lem-weil-pbc-finite-locally-constant-module-values`), which identifies the existence
of finite constant-value trivializations with `IsFiniteLocallyConstantSheaf`.
Package the converted witnesses in each direction. Empty strata and the empty
scheme are covered by the same equivalence. -/
theorem isConstructibleEtaleModuleSheaf_iff
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModuleSheaf F ↔
      IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ => M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ => M) F := by
  constructor
  · rintro ⟨S, _, hF⟩
    let T : Stratification X :=
      { toStratification := S.toStratification
        domain := S.domain
        immersion := S.immersion
        isImmersion := S.isImmersion
        range_immersion := S.range_immersion }
    refine ⟨T, fun k => ?_⟩
    exact (finite_locally_constant_module_values_iff _).1.mp (hF k)
  · rintro ⟨S, hF⟩
    let T : LocallyClosedStratification X :=
      { toStratification := S.toStratification
        domain := S.domain
        immersion := S.immersion
        isImmersion := S.isImmersion
        range_immersion := S.range_immersion }
    refine ⟨T, fun k => S.isConstructible_stratum k, fun k => ?_⟩
    exact (finite_locally_constant_module_values_iff _).1.mpr (hF k)

end AlgebraicGeometry.Scheme

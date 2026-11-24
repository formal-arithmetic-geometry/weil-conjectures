/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Finite geometric stalks of constructible module sheaves

## References

* Stacks Project, Tags 095N, 03RU, 03RW and 03Q1
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- If a sheaf of modules on the small étale site is constructible, each geometric stalk is
finite, and hence finitely generated as a module over the finite coefficient ring. -/
theorem constructibleModule_finite_geometric_stalk
    {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ T) :
    Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) ∧
      Module.Finite Λ (((pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F) := by
  obtain ⟨S, hS⟩ := hF
  have ht : s.base (default : Spec (.of Ω)) ∈ ⋃ k, S.stratum k := by
    rw [S.iUnion_stratum_eq_univ]
    exact Set.mem_univ _
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
  rw [← S.range_immersion k] at hk
  obtain ⟨z, hz⟩ := hk
  have : IsImmersion (S.immersion k) := S.isImmersion k
  obtain ⟨s', hs', _⟩ :=
    ((fieldPoint_factorsThrough_immersion (S.immersion k) z).2 Ω s hz.symm).1
  have hG := (finite_locally_constant_module_values_iff
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F)).1.mp (hS k)
  have hfin := hG.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s'
  have e := (Etale.upperStarCompSheafFiberIso
    (ModuleCat.{u + 1} Λ) (S.immersion k) s').app F
  have hstalk := hfin.of_iso e
  rw [hs'] at hstalk
  have : Module.Finite Λ (((pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F) :=
    (ModuleCat.isFinitelyGenerated_iff _).mp hstalk
  exact ⟨Module.finite_of_finite Λ, inferInstance⟩

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteFibreCokernelTensor
import WeilConjectures.AlgebraicGeometry.ClosedImmersionOfLocalizedSectionMap
import Mathlib.RingTheory.LocalRing.Module

/-!
# Spreading a closed immersion of a finite fibre

## References

* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite morphism whose fibre at `s` is a closed immersion is a closed immersion
on some open neighbourhood of `s`. (Stacks, Tag 04DG.) -/
theorem exists_isClosedImmersion_restrict_of_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) [IsFinite f]
    (hf : IsClosedImmersion (f.fiberToSpecResidueField s)) :
    ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (f ∣_ U) := by
  obtain ⟨U, hU, hsU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := s) (U := ⊤) (by trivial)
  let := (f.app U).hom.toAlgebra
  let φ := Algebra.linearMap Γ(S, U) Γ(X, f ⁻¹ᵁ U)
  let Q := Γ(X, f ⁻¹ᵁ U) ⧸ φ.range
  let p := hU.primeIdealOf ⟨s, hsU⟩
  have hfinite : Module.Finite Γ(S, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  let := hfinite
  have hzero : Subsingleton (TensorProduct Γ(S, U) p.asIdeal.ResidueField Q) :=
    IsFinite.subsingleton_residueField_tensor_cokernel f U hU ⟨s, hsU⟩ hf
  have hp : p ∉ Module.support Γ(S, U) Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hzero
  have hlocal : Subsingleton (LocalizedModule p.asIdeal.primeCompl Q) := by
    rw [Module.mem_support_iff] at hp
    exact not_nontrivial_iff_subsingleton.mp hp
  have hsurj : Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) :=
    (φ.localizedMap_surjective_iff_subsingleton_localized_coker _).mpr hlocal
  obtain ⟨a, ha, hsa⟩ :=
    Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
      p.asIdeal φ hsurj
  refine ⟨S.basicOpen a, ?_,
    isClosedImmersion_restrict_basicOpen_of_localizedMap_surjective f U hU a hsa⟩
  have hmem : p ∈ hU.fromSpec ⁻¹ᵁ S.basicOpen a := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact ha
  change hU.fromSpec p ∈ S.basicOpen a at hmem
  simpa only [p, hU.fromSpec_primeIdealOf] using hmem

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.CompleteLocalGRing
import Sheaf.RingTheory.JTwoResidueFieldCriterion
import Sheaf.RingTheory.RegularRingUniversallyCatenary

/-!
# Excellence of fields

Source: Stacks Project, More on Algebra, Proposition 07QW, clause (1)
(blueprint: lem-exc-fields-excellent).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every field, regarded as a commutative ring, is excellent.

Source: Stacks Project, More on Algebra, Tags 07PS, 07PJ, and 07QW, clause (1);
Algebra, Tags 00NQ and 00NM (blueprint: lem-exc-fields-excellent).

Proof:
1. A field is Noetherian and local, with maximal ideal zero. The zero-adic completeness
   instance makes it complete for its maximal-ideal topology. Apply the complete-local
   G-ring theorem `lem-weil-pbc-complete-local-g-ring`.
2. Apply `lem-exc-j2-residue-field-criterion`. A prime of a field is maximal, so its
   residue field is module-finite over the field. For each finite purely inseparable
   residue-field extension L, take the top subalgebra B = L. Module finiteness is
   transitive. Every element is a fraction with denominator one, and the whole spectrum
   is a nonempty regular open since B is isomorphic to a field. This gives J-2.
3. A field is a regular ring by the Mathlib instances, so
   `lem-trf-regular-ring-universally-catenary` gives universal catenarity.
4. Combine Noetherianity, the G-ring condition, J-2 and universal catenarity using
   the definition of excellence.
-/
theorem isExcellent_of_field (k : Type u) [Field k] : IsExcellent k := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  refine ⟨⟨inferInstance, isGRing_of_isNoetherianRing_of_isAdicComplete k, ?_⟩,
    IsRegularRing.isUniversallyCatenary k⟩
  intro A _ _ _
  apply isOpen_regularLocus_of_residueField_finite_models k ?_ A
  intro p hp L _ _ _ _ _ _
  let : p.IsMaximal := by simpa [p.eq_bot_of_prime] using Ideal.bot_isMaximal (K := k)
  let : Module.Finite k L := Module.Finite.trans p.ResidueField L
  let B : Subalgebra k L := ⊤
  let e : B ≃ₐ[k] L := Subalgebra.topEquiv
  let : Module.Finite k B := Module.Finite.equiv e.symm.toLinearEquiv
  let : IsRegularRing B := IsRegularRing.of_ringEquiv e.symm.toRingEquiv
  refine ⟨B, inferInstance, ?_, Set.univ, isOpen_univ, ?_, ?_⟩
  · intro x
    exact ⟨⟨x, Algebra.mem_top⟩, 1, one_ne_zero, (div_one x).symm⟩
  · exact ⟨⟨⊥, inferInstance⟩, Set.mem_univ _⟩
  · intro q _
    infer_instance

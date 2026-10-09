/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Profinite

/-!
# The Galois group of a Galois extension acting on an integral closure

Let `R` be a ring, `K` an `R`-algebra which is a field and `Ω / K` a Galois extension. The Galois
group `Gal(Ω / K)`, with its Krull topology, acts continuously on the integral closure `B` of `R`
in `Ω`, `B` being discrete (`Algebra.continuousSMul_integralClosure`). If `R` is integrally closed
in `K`, then `R` is the ring of invariants (`Algebra.isInvariant_integralClosure`), so the results
on profinite groups acting on rings apply: the decomposition group `D` of a prime `Q` of `B` over
`P` surjects onto the automorphism group of `(B ⧸ Q) / (R ⧸ P)` with kernel the inertia group, and
`D / I ≅ Aut((B ⧸ Q) / (R ⧸ P))` (`Ideal.Quotient.stabilizerQuotientInertiaEquivOfProfinite`).
-/

@[expose] public section

open scoped Pointwise

namespace Algebra

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- The fixed points of a subgroup `H` form a subalgebra over which the action of `H` is
invariant. -/
instance isInvariant_fixedPoints_subalgebra (H : Subgroup G) :
    IsInvariant (FixedPoints.subalgebra A B H) B H :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩

end Algebra

section Galois

variable (R K Ω : Type*) [CommRing R] [Field K] [Field Ω] [Algebra R K] [Algebra K Ω]
  [Algebra R Ω] [IsScalarTower R K Ω]

instance AlgEquiv.smulCommClass_of_isScalarTower : SMulCommClass Gal(Ω/K) R Ω where
  smul_comm σ r x := by
    rw [algebra_compatible_smul K r, algebra_compatible_smul K r]
    exact smul_comm σ (algebraMap R K r) x

namespace Algebra

/-- The Galois group of an algebraic extension `Ω / K`, with its Krull topology, acts
continuously on the integral closure of `R` in `Ω`, with the discrete topology. -/
theorem continuousSMul_integralClosure [Algebra.IsIntegral K Ω]
    [TopologicalSpace (integralClosure R Ω)] [DiscreteTopology (integralClosure R Ω)] :
    ContinuousSMul Gal(Ω/K) (integralClosure R Ω) := by
  refine ⟨continuous_prod_of_discrete_right.mpr fun b ↦ continuous_discrete_rng.mpr fun c ↦ ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • (MulAction.stabilizer Gal(Ω/K) (b : Ω) : Set Gal(Ω/K)), ?_,
    (stabilizer_isOpen_of_isIntegral (b : Ω)).smul σ, ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hσ ⊢
  rw [← hσ]
  apply Subtype.ext
  change (σ * τ) • (b : Ω) = σ • (b : Ω)
  rw [mul_smul, show τ • (b : Ω) = b from hτ]

/-- If `R` is integrally closed in `K` and `Ω / K` is Galois, then `R` is the ring of invariants
of `Gal(Ω / K)` acting on the integral closure of `R` in `Ω`. -/
theorem isInvariant_integralClosure [IsGalois K Ω] [IsIntegrallyClosedIn R K] :
    IsInvariant R (integralClosure R Ω) Gal(Ω/K) := by
  refine ⟨fun b hb ↦ ?_⟩
  have hfix : (b : Ω) ∈ IntermediateField.fixedField (⊥ : IntermediateField K Ω).fixingSubgroup :=
    fun σ ↦ congrArg Subtype.val (hb σ)
  rw [InfiniteGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hfix
  obtain ⟨k, hk⟩ := hfix
  have hint : IsIntegral R k := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R K Ω) (algebraMap K Ω).injective]
    have := b.2
    rw [mem_integralClosure_iff, ← hk] at this
    exact this
  obtain ⟨r, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  exact ⟨r, Subtype.ext (by simp [← hk, ← IsScalarTower.algebraMap_apply])⟩

end Algebra

namespace Ideal.Quotient

variable {R K Ω} [IsGalois K Ω] [IsIntegrallyClosedIn R K] (P : Ideal R)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver P]

/-- The decomposition group in `Gal(Ω / K)` of a prime `Q` of the integral closure of `R` in `Ω`
surjects onto the automorphism group of the residue extension. -/
theorem stabilizerHom_surjective_integralClosure :
    Function.Surjective (stabilizerHom Q P Gal(Ω/K)) := by
  let : TopologicalSpace (integralClosure R Ω) := ⊥
  have : DiscreteTopology (integralClosure R Ω) := ⟨rfl⟩
  have := Algebra.continuousSMul_integralClosure R K Ω
  have := Algebra.isInvariant_integralClosure R K Ω
  exact stabilizerHom_surjective_of_profinite P Q

/-- **Decomposition modulo inertia.** The decomposition group of `Q` modulo the inertia group is
the automorphism group of the residue extension `(B ⧸ Q) / (R ⧸ P)`. -/
noncomputable def stabilizerQuotientInertiaEquivIntegralClosure :
    MulAction.stabilizer Gal(Ω/K) Q ⧸ Q.inertia (MulAction.stabilizer Gal(Ω/K) Q) ≃*
      ((integralClosure R Ω ⧸ Q) ≃ₐ[R ⧸ P] (integralClosure R Ω ⧸ Q)) :=
  QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer Gal(Ω/K) Q))
    (stabilizerHom_surjective_integralClosure P Q) (ker_stabilizerHom Q P Gal(Ω/K)).symm

end Ideal.Quotient

end Galois

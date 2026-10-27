module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.FieldTheory.InertiaRestrictionSurjective

/-!
# Open normal subgroups containing inertia have unramified finite fixed fields

Source: Stacks Project, Tags 0BTD and 0BSX, `lemma-normal-pione-quotient-inertia`
and `lemma-one-orbit-geometric-galois-compare`
(blueprint: lem-dl-a1-open-normal-inertia-fixed-field).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open IntermediateField

namespace Ideal

/-- An open normal subgroup containing all integral-closure inertia groups has a finite
Galois fixed field, and the induced finite extension is unramified at every prime.

Source: Stacks Project, Tag 0BTD, `lemma-normal-pione-quotient-inertia`, second proof
paragraph through triviality of finite-level inertia; Tag 0BSX,
`lemma-one-orbit-geometric-galois-compare`.
(blueprint: lem-dl-a1-open-normal-inertia-fixed-field)

Proof:
1. The separable closure is Galois, and the open subgroup criterion gives finite-dimensional
   separability of the fixed field and identifies its fixing subgroup with the subgroup
   (`lem-weil-pbc-separable-closure-exists-galois` and
   `lem-exc-etale-open-subgroup-fixed-field-galois`). Normality gives that the fixed field
   is Galois by `lem-dl-a1-normal-fixing-subgroup-galois`.
2. The integral-closure inclusion is integral and injective, so lying over gives a prime of
   the larger closure above each prime of the finite-level closure
   (`lem-weil-pbc-integral-injective-lying-over`).
3. Inertia restriction is surjective (`lem-dl-a1-inertia-restriction-surjective`). A lift of
   a finite-level inertia element lies in the given subgroup and therefore fixes the fixed
   field, so the finite-level inertia is trivial.

Here `Ideal.inertia` means that every difference g(b) - b lies in the prime. This forces
prime stabilization and identity on its quotient, equivalently identity on the quotient's
fraction field. No Noetherianity or module finiteness of either integral closure is assumed.
-/
theorem fixedField_finite_galois_of_isOpen_normal_inertia_le
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (Ω : Type w) [Field Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (U : Subgroup (Ω ≃ₐ[K] Ω))
    (hUopen : IsOpen (U : Set (Ω ≃ₐ[K] Ω)))
    (hUnormal : U.Normal)
    (hUinertia : ∀ r : Ideal (integralClosure A Ω), r.IsPrime →
      r.inertia (Ω ≃ₐ[K] Ω) ≤ U)
    : FiniteDimensional K (IntermediateField.fixedField U) ∧
      IsGalois K (IntermediateField.fixedField U) ∧
      U = (IntermediateField.fixedField U).fixingSubgroup ∧
      (∀ q : Ideal (integralClosure A (IntermediateField.fixedField U)), q.IsPrime →
        (∃ r : Ideal (integralClosure A Ω), r.IsPrime ∧
          r.comap
            (((IntermediateField.fixedField U).val.restrictScalars A).mapIntegralClosure.toRingHom)
            = q) ∧
        q.inertia
          ((IntermediateField.fixedField U) ≃ₐ[K] (IntermediateField.fixedField U)) = ⊥) := by
  sorry

end Ideal

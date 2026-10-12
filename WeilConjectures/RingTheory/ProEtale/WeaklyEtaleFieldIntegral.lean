/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
public import WeilConjectures.RingTheory.ProEtale.WeakDimension

/-!
# Weakly étale algebras over fields and integral closure

We record two consequences of the flatness of the diagonal of a weakly étale algebra:

* `Algebra.WeaklyEtale.field_spec`: a weakly étale algebra over a field is a filtered union of
  finite étale subalgebras, is reduced, and has separable algebraic residue fields
  (blueprint `lem-weil-pbc-weak-etale-field`).
* `Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct_fractionRing`: if `A` is an integrally
  closed domain with fraction field `K` and `B` is weakly étale over `A`, then `B` is integrally
  closed in `B ⊗[A] K` (blueprint `lem-weil-pbc-weak-etale-integral-closure`).
-/

@[expose] public section

universe u

open TensorProduct

namespace Algebra.WeaklyEtale

/-- **Blueprint `lem-weil-pbc-weak-etale-field`**: if `k` is a field and `R` is a weakly étale
`k`-algebra, every finitely generated `k`-subalgebra of `R` is finite étale. In particular `R` is
ind-étale, reduced, and all its residue fields are separable algebraic over `k`. -/
theorem field_spec {k R : Type u} [Field k] [CommRing R] [Algebra k R] [WeaklyEtale k R] :
    (∀ A : Subalgebra k R, A.FG → Module.Finite k A ∧ Algebra.Etale k A) ∧
      Algebra.IndEtale k R ∧ IsReduced R ∧
      ∀ (q : Ideal R) [q.IsPrime],
        Algebra.IsSeparable k q.ResidueField ∧ Algebra.IsAlgebraic k q.ResidueField := by
  have : Algebra.IndEtale k R := indEtale_field k R
  have : Ring.AbsolutelyFlat R := .of_flat_lmul' k R (flat_lmul' k R)
  refine ⟨fun A hA ↦ ?_, inferInstance, inferInstance, fun q _ ↦ ?_⟩
  · have := etale_of_fg A hA
    exact ⟨Algebra.FormallyUnramified.finite_of_free k A, this⟩
  · have := Algebra.IndEtale.isSeparable_residueField_of_field (K := k) q
    exact ⟨this, inferInstance⟩

/-- **Blueprint `lem-weil-pbc-weak-etale-integral-closure`**: let `A` be an integrally closed
domain with fraction field `K` and let `B` be a weakly étale `A`-algebra. Then `B` is integrally
closed in `B ⊗[A] K`. -/
theorem isIntegrallyClosedIn_tensorProduct_fractionRing (A B K : Type*) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B] [Algebra.WeaklyEtale A B]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    IsIntegrallyClosedIn B (B ⊗[A] K) := by
  have : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).mpr (IsFractionRing.injective A K)
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have : IsIntegrallyClosedIn A K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp ‹_›
  exact isIntegrallyClosedIn_tensorProduct A B K

end Algebra.WeaklyEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.TensorOppositeMatrixLifts

/-!
# Tensor lifts with the quotient scalar defect

If central simple algebras `A` and `B` have scalar-defect classes `x` and `y`, then
`A ⊗[K] Bᵐᵒᵖ` admits a splitting over the separable closure with locally constant lifts whose
scalar defect is the quotient of the two defects.

## Main results

- `Field.exists_tensor_opposite_scalarDefect_lifts`

## Implementation details

The splitting combines the two given splittings with the transpose anti-isomorphism and the
Kronecker isomorphism, reindexing `Fin n × Fin m` as `Fin (n * m)`. The lifts are Kronecker
products of the lifts for `A` with the inverse transposes of the lifts for `B`. Only a splitting
over the separable closure is produced, not one over `K`.

## References

* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7), injectivity argument
* [Stacks Project, Section 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- If `A` and `B` have scalar-defect classes `x` and `y`, represented by cocycles `z` and `w`,
then `A ⊗[K] Bᵐᵒᵖ` has a splitting over the separable closure with locally constant lifts
whose scalar defect is the quotient `z / w`. -/
theorem exists_tensor_opposite_scalarDefect_lifts (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y) :
    ∃ (n : ℕ) (_ : n ≠ 0)
      (e : (SeparableClosure K ⊗[K] (A ⊗[K] Bᵐᵒᵖ)) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K))
      (b : Gal(SeparableClosure K/K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
      (z w : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2),
      IsLocallyConstant b ∧
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z = x ∧
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom w = y ∧
      (∀ (g : Gal(SeparableClosure K/K)) (a : A ⊗[K] Bᵐᵒᵖ),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n)
          (galoisUnitsCocycleValue K z g h / galoisUnitsCocycleValue K w g h) *
            b (g * h))  := by
  obtain ⟨n, hn, eA, a, hla, z, hz, ha, hda⟩ := hx
  obtain ⟨m, hm, eB, b, hlb, w, hw, hb, hdb⟩ := hy
  obtain ⟨e, he⟩ := exists_tensor_opposite_matrix_conjugation K A B n m eA eB a b ha hb
  refine ⟨n * m, Nat.mul_ne_zero hn hm, e,
    fun g ↦ tensorOppositeMatrixLift (a g) (b g), z, w, ?_, hz, hw, he, ?_⟩
  · exact hla.comp₂ hlb tensorOppositeMatrixLift
  · intro g h
    change tensorOppositeMatrixLift (a g) (b g) *
      Matrix.GeneralLinearGroup.map g.toRingHom (tensorOppositeMatrixLift (a h) (b h)) = _
    obtain ⟨hmap, hmul, hscalar⟩ :=
      tensorOppositeMatrixLift_properties g.toRingHom (a h) (a h) (b h) (b h) 1 1
    have hmul' := (tensorOppositeMatrixLift_properties (R := SeparableClosure K)
      (S := SeparableClosure K)
      (RingHom.id _) (a g) (Matrix.GeneralLinearGroup.map g.toRingHom (a h))
        (b g) (Matrix.GeneralLinearGroup.map g.toRingHom (b h)) 1 1).2.1
    rw [← hmap, ← hmul', hda, hdb]
    obtain ⟨_, hmul2, hscalar2⟩ :=
      tensorOppositeMatrixLift_properties (R := SeparableClosure K) (S := SeparableClosure K)
        (RingHom.id _) (Matrix.GeneralLinearGroup.scalar (Fin n)
          (galoisUnitsCocycleValue K z g h)) (a (g * h))
        (Matrix.GeneralLinearGroup.scalar (Fin m)
          (galoisUnitsCocycleValue K w g h)) (b (g * h))
        (galoisUnitsCocycleValue K z g h) (galoisUnitsCocycleValue K w g h)
    rw [hmul2, hscalar2]


end Field

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectLifts
import WeilConjectures.FieldTheory.BrauerScalarDefectCocycle

/-!
# Existence of the scalar-defect class

We show that a splitting of a central simple algebra over the separable closure admits locally
constant matrix lifts of the Galois action whose scalar defect is a continuous `2`-cocycle
(`Field.exists_brauerScalarDefect_lifts`).

## Implementation details

The lifts come from `Field.exists_locallyConstant_brauer_lift`. The scalar defect
`b g * g(b h) * (b (g * h))⁻¹` is central, hence a scalar unit; associativity gives the
multiplicative cocycle identity, which is converted to an invariant homogeneous cocycle and curried
to Mathlib's continuous cochains via the compact-open exponential law.

## References

* [Stacks Project, Lemma 03R6](https://stacks.math.columbia.edu/tag/03R6), the construction
  preceding Theorem 03R7, and Section 0DVG
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- Given a splitting `e : K^sep ⊗[K] A ≃ Mₙ(K^sep)` of a central simple algebra, there is a
locally constant family of invertible matrices `b g`, indexed by the absolute Galois group, with
`g(e(1 ⊗ a)) = (b g)⁻¹ * e(1 ⊗ a) * b g` for all `a`, together with a continuous `2`-cocycle `z`
with values in the units of `K^sep` such that `b g * g(b h) = z(g, h) • b (g * h)`. -/
theorem exists_brauerScalarDefect_lifts (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K)) :
    ∃ b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      IsLocallyConstant b ∧
      ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
        (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
          (e (1 ⊗ₜ[K] a)).map g =
            ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
        (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
          Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
            b (g * h)) := by
  obtain ⟨b, hb, hdesc⟩ := exists_locallyConstant_brauer_lift K A n hn e
  obtain ⟨z, hdefect⟩ := exists_brauerScalarDefect_cocycle K A n hn e b hb hdesc
  exact ⟨b, hb, z, hdesc, hdefect⟩

end Field

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectScalarData
import WeilConjectures.FieldTheory.BrauerScalarDefectCocycleRealization

/-!
# The continuous scalar-defect cocycle

Given a splitting `e` of `K^sep ⊗[K] A` as a matrix algebra and locally constant matrix lifts
`b` of the associated projective descent datum, the scalar defect `b_g g(b_h) b_(gh)⁻¹` is a
scalar matrix whose entries form a continuous homogeneous two-cocycle with values in the units
of the separable closure.

## Main results

- `Field.exists_brauerScalarDefect_cocycle`

## Implementation details

The quotient `b_g g(b_h) b_(gh)⁻¹` commutes with every matrix and is therefore scalar, say
`c(g,h)`. Associativity gives the cocycle identity, and local constancy of `b` gives local
constancy of `c`. The homogeneous cochain is `f(g₀,g₁,g₂) = g₀(c(g₀⁻¹g₁, g₁⁻¹g₂))`, curried via
the compact-open exponential law into Mathlib's continuous cochains; evaluation at `(1,g,gh)`
recovers `c(g,h)`. No normalization of `b` or `c` is needed.

## References

* [Stacks Project, Lemma 03R6](https://stacks.math.columbia.edu/tag/03R6) and the construction
  before Theorem 03R7
* [Stacks Project, Section 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section
universe u
namespace Field

open scoped TensorProduct
/-- If the locally constant lifts `b` satisfy `g(e(1 ⊗ a)) = b_g⁻¹ e(1 ⊗ a) b_g`, then there is
a continuous two-cocycle `z` with values in the units of the separable closure such that
`b_g g(b_h) = c_z(g,h) b_(gh)` for all `g, h`, where `c_z(g,h)` is the value of `z`. -/
theorem exists_brauerScalarDefect_cocycle (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) :
    ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
      ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
          b (g * h) := by
  obtain ⟨c, hlc, hrel, hc⟩ := exists_brauerScalarDefect_scalar_data K A n hn e b hb hdesc
  obtain ⟨z, hz⟩ := exists_galoisUnits_cocycle_of_scalar_cocycle K c hlc hc
  refine ⟨z, ?_⟩
  intro g h
  simpa [hz g h] using hrel g h
end Field

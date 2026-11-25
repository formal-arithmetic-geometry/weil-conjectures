/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.FiniteGaloisCocycleData
import Mathlib.Algebra.Group.Action.End

/-!
# Finite monomial coefficient data for a continuous two-cocycle

A continuous two-cocycle with values in the units of the separable closure admits finite,
locally constant monomial coefficient data.

## Main results

- `Field.exists_cocycle_monomial_coefficients`

## Implementation details

The data come from a finite quotient `q` of the Galois group with a group law on `Fin n` and
coefficients `d` with `c(g,h) = d(q(g),q(h))`. The permutation `p(g)` is left multiplication by
`q(g)` and `w(g,j) = d(q(g),j)`. No normalization of the cocycle is used.

## References

* [Stacks Project, Theorem 03R7](https://stacks.math.columbia.edu/tag/03R7), surjectivity
* [Stacks Project, Section 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section

universe u

namespace Field

/-- A continuous two-cocycle `z` admits finite, locally constant monomial coefficient data: a
homomorphism `p` from the absolute Galois group to the permutations of `Fin n`, `n ≠ 0`, and
units `w(g,j)` with `(p, w)` locally constant and
`w(g, p(h)j) g(w(h,j)) = z(g,h) w(gh, j)`. -/
theorem exists_cocycle_monomial_coefficients (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2) :
    ∃ (n : ℕ) (_ : n ≠ 0)
      (p : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* Equiv.Perm (Fin n))
      (w : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Fin n → (SeparableClosure K)ˣ),
      IsLocallyConstant (fun g ↦ (p g, w g)) ∧
      ∀ g h j, w g (p h j) * Units.map g.toRingHom (w h j) =
        galoisUnitsCocycleValue K z g h * w (g * h) j := by
  classical
  obtain ⟨n, hn, grp, q, d, hq, hc, hd⟩ := exists_finite_galois_cocycle_data K z
  let regular := @MulAction.toPermHom (Fin n) (Fin n) grp
    (@Monoid.toMulAction (Fin n) grp.toMonoid)
  let p := regular.comp q
  let w := fun g j ↦ d (q g) j
  refine ⟨n, hn, p, w, ?_, ?_⟩
  · exact hq.comp (fun a ↦ (regular a, d a))
  · intro g h j
    have hp : p h j = @Mul.mul (Fin n) grp.toMul (q h) j := by rfl
    change d (q g) (p h j) * Units.map g.toRingHom (d (q h) j) = _
    rw [hp, hc g h]
    exact hd g h j

end Field

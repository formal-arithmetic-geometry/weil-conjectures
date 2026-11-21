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

Source: Stacks Project, Theorem 03R7, surjectivity, and Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

/-- A continuous two-cocycle admits finite, locally constant monomial coefficient data.

Source: Stacks Project, Theorem 03R7 surjectivity sketch and Section 0DVG. -/
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

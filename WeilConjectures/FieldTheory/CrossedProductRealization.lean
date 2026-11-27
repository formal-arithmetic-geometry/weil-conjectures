/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.CrossedProductForCocycle

/-!
# Crossed-product realization data for continuous degree-two classes

Every class in `H²(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)ˣ)` is the scalar defect of a crossed-product central
simple algebra.

## References

* [Stacks Project, Tags 03R6 and 03R7](https://stacks.math.columbia.edu/tag/03R7)
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- For every class `x`, there is a central simple algebra `A` with a splitting over the
separable closure and locally constant matrix lifts of its Galois descent datum whose scalar
defect is a homogeneous cocycle representing `x`. -/
theorem exists_crossedProduct_realization_data (K : Type u) [Field K]
    (x : GaloisUnitsH2 K) :
    ∃ (A : CSA.{u, u} K) (n : ℕ) (_hn : n ≠ 0)
      (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K))
      (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)),
      IsLocallyConstant b ∧
      ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
        (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z = x ∧
        (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
          (e (1 ⊗ₜ[K] a)).map g =
            ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
        (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
          Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
            b (g * h)) := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2))).mp inferInstance x
  obtain ⟨A, n, hn, e, b, hb, hdesc, hdefect⟩ :=
    exists_crossedProduct_data_for_cocycle K z
  exact ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩

end Field

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

Source: Stacks Project, Lemma 03R6, construction before Theorem 03R7, and Section 0DVG.
-/

@[expose] public section
universe u
namespace Field

open scoped TensorProduct
/-- The scalar defect of locally constant lifts is represented by a homogeneous cocycle.

Source: Stacks Project, scalar-defect construction preceding Theorem 03R7 and Section 0DVG. -/
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

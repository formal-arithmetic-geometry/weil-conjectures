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

Source: Stacks Project, Lemma 03R6 and the construction preceding Theorem 03R7.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- A splitting admits locally constant matrix lifts and an actual scalar-defect cycle.

Source: Stacks Project, Lemma 03R6 and the scalar-defect construction immediately before Theorem
03R7, with homogeneous coordinates as in Section 0DVG. -/
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

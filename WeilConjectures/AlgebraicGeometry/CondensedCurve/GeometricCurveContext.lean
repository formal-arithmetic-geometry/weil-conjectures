/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
import Mathlib.Algebra.CharP.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The geometric domain of the curve monodromy comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedCurve

/-- A curve has the absolute hypotheses needed for the monodromy fibre. -/
theorem geometricCurve_context
    (k : Type u) [Field k] (p ℓ : ℕ)
    [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (C₀ : Over (Spec (.of k))) [IsCurve C₀.hom] :
    ∃ (_hN : IsNoetherian C₀.left) (_hSep : C₀.left.IsSeparated),
      Nonempty (∀ z : C₀.left, Invertible (ℓ : C₀.left.residueField z)) := by
  have : IsLocallyNoetherian C₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian C₀.hom
  have : CompactSpace C₀.left :=
    QuasiCompact.compactSpace_of_compactSpace C₀.hom
  have hN : IsNoetherian C₀.left := {}
  have hSep := Scheme.isSeparated_of_isSeparated_hom C₀.hom
  have hunit : IsUnit (ℓ : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓp.symm).isUnit
  refine ⟨hN, hSep, ⟨fun z ↦ ?_⟩⟩
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ C₀.hom.appTop ≫
    C₀.left.Γevaluation z).hom
  exact (show IsUnit (ℓ : C₀.left.residueField z) by
    simpa using hunit.map φ).invertible

end AlgebraicGeometry.ProEtale.CondensedCurve

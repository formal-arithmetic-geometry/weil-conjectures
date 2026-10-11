/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.Integral

/-!
# Normalizations in algebraic field-valued points are normal

Let `f : X ⟶ Z` be quasi-compact and quasi-separated, with `X` integral and the sections of `X`
over preimages of affine opens fields algebraic over the sections of `Z`. Then the relative
normalization of `Z` in `X` has integrally closed local rings
(`AlgebraicGeometry.Scheme.Hom.isIntegrallyClosed_stalk_normalization`): on an affine open it is
the integral closure of `Γ(Z, U)` in the field `Γ(X, f⁻¹ U)`, whose fraction field is that field.
This is Step 1 of the proof of Stacks 09Z6, with `X = Spec K` for a finite extension `K` of a
residue field.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f] [QuasiSeparated f] [IsIntegral X]

/-- **The relative normalization in an algebraic field-valued point is normal.** -/
theorem isIntegrallyClosed_stalk_normalization (y : f.normalization)
    (h : ∀ U : Z.affineOpens, f.fromNormalization y ∈ U.1 →
      letI := (f.app U.1).hom.toAlgebra
      IsField Γ(X, f ⁻¹ᵁ U.1) ∧ Algebra.IsAlgebraic Γ(Z, U.1) Γ(X, f ⁻¹ᵁ U.1) ∧
        Function.Injective (f.app U.1).hom) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f.fromNormalization y) (U := ⊤) trivial
  obtain ⟨hfield, halg, hinj⟩ := h ⟨U, hU⟩ hyU
  let := (f.app U).hom.toAlgebra
  let : Field Γ(X, f ⁻¹ᵁ U) := hfield.toField
  have hW : IsAffineOpen (f.fromNormalization ⁻¹ᵁ U) := hU.preimage _
  have : IsFractionRing (integralClosure Γ(Z, U) Γ(X, f ⁻¹ᵁ U)) Γ(X, f ⁻¹ᵁ U) :=
    integralClosure.isFractionRing_of_algebraic (fun x hx ↦ hinj (hx.trans (map_zero _).symm))
  have hic : IsIntegrallyClosed (integralClosure Γ(Z, U) Γ(X, f ⁻¹ᵁ U)) :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff Γ(X, f ⁻¹ᵁ U)).mp integralClosure_idem
  have hΓ : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hyU⟩⟩
  let := f.normalization.presheaf.algebra_section_stalk (⟨y, hyU⟩ : f.fromNormalization ⁻¹ᵁ U)
  have := hW.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization
    (R := Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U))
    (f.normalization.presheaf.stalk (⟨y, hyU⟩ : f.fromNormalization ⁻¹ᵁ U)) (hW.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

end AlgebraicGeometry.Scheme.Hom

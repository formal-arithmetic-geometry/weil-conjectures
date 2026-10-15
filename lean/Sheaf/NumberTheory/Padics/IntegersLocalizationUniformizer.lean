/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Inverting a coefficient-field uniformizer

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`, the displayed Hom tensor E formula;
Stacks Project, Tags 00CO and 00CX
(blueprint: lem-weil-l-adic-integers-localization-uniformizer).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Padic

/-- Inverting the chosen uniformizer identifies the integers with the coefficient field
and identifies their tensor products as E-modules. The two module structures in the last
clause are specified on pure tensors: the left action is transported using `φ.symm`, and
the right action is multiplication on the field factor. The additive equivalence `F`
intertwines these actions, which states precisely that it is an E-linear isomorphism.

Source: blueprint `def-weil-rationalization-karoubi`, displayed Hom tensor E formula;
Stacks Project, Tags 00CO and 00CX
(blueprint: lem-weil-l-adic-integers-localization-uniformizer).

Proof: Define the fraction map x/π^n ↦ x π^(-n). Cross multiplication and cancellation
in E show that it is well defined, preserves ring operations and is injective. By
`lem-weil-l-adic-extension-integers-dvr`, π is nonzero and every nonzero field element
is a unit times an integer power of π. Nonnegative powers lie in the integer ring;
negative powers give fractions with denominator π^n. Zero is the image of 0/1.
This proves surjectivity and the localization assertion. For every module M, the
bilinear universal property of `def-weil-pbc-module-tensor-product` gives the maps
m ⊗ t ↦ m ⊗ φ(t) and m ⊗ e ↦ m ⊗ φ.symm(e). They respect balancing since φ fixes
the integers, and their composites fix all pure tensors, hence are identities.
Transport multiplication by e to multiplication by φ.symm(e) on the left localization factor.
On pure tensors the forward map intertwines this action with multiplication by e
on the right field factor; generation by pure tensors proves E-linearity. -/
theorem coefficientExtension_localization_uniformizer (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsLocalization.Away (coefficientExtensionUniformizer l E) E ∧
    ∃ φ : Localization.Away (coefficientExtensionUniformizer l E) ≃ₐ[
        coefficientExtensionIntegers l E] E,
      (∀ (x : coefficientExtensionIntegers l E) (n : ℕ),
        φ (IsLocalization.mk' (Localization.Away (coefficientExtensionUniformizer l E))
          x (⟨coefficientExtensionUniformizer l E ^ n, ⟨n, rfl⟩⟩ :
            Submonoid.powers (coefficientExtensionUniformizer l E))) =
          (x : E) * (coefficientExtensionUniformizer l E : E)⁻¹ ^ n) ∧
      ∀ (M : Type v) [AddCommGroup M] [Module (coefficientExtensionIntegers l E) M],
        ∃ (s : Module E (M ⊗[coefficientExtensionIntegers l E]
            Localization.Away (coefficientExtensionUniformizer l E)))
          (t : Module E (M ⊗[coefficientExtensionIntegers l E] E))
          (F : (M ⊗[coefficientExtensionIntegers l E]
            Localization.Away (coefficientExtensionUniformizer l E)) ≃+
              (M ⊗[coefficientExtensionIntegers l E] E)),
          (∀ (e : E) (m : M) (a : Localization.Away (coefficientExtensionUniformizer l E)),
            s.toSMul.smul e (m ⊗ₜ a) = m ⊗ₜ (φ.symm e * a)) ∧
          (∀ (e : E) (m : M) (a : E),
            t.toSMul.smul e (m ⊗ₜ a) = m ⊗ₜ (e * a)) ∧
          (∀ (m : M) (a : Localization.Away (coefficientExtensionUniformizer l E)),
            F (m ⊗ₜ a) = m ⊗ₜ φ a) ∧
          (∀ (e : E) (z : M ⊗[coefficientExtensionIntegers l E]
              Localization.Away (coefficientExtensionUniformizer l E)),
            F (s.toSMul.smul e z) = t.toSMul.smul e (F z)) := by
  sorry

end Padic

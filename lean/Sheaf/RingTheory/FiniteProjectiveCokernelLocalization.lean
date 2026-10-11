module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

universe u v w

namespace Module

/-!
# Residue-field criteria for finite-projective maps

Source: Stacks Project, Algebra, Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3)
(blueprint: lem-pc-finite-projective-cokernel-localization).
-/

/-- Source: Stacks Project, Algebra, Tag 00O0, Lemma `cokernel-flat`, parts (1) and (3)
(blueprint: lem-pc-finite-projective-cokernel-localization).

Proof: First apply the finite-projective-to-finite-free localization lemma to both modules,
which preserves the residue-field hypotheses. Then apply the finite-free residue-localization
lemma. Composing principal localizations gives the required element. -/
theorem finiteProjectiveCokernel_residue_localization
    {R : Type u} [CommRing R]
    {P₁ : Type v} [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁]
    [Module.Projective R P₁]
    {P₂ : Type w} [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂]
    [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    (Function.Injective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (φ.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f))) ∧
        Module.Projective (Localization.Away f)
          (TensorProduct R (Localization.Away f) P₂ ⧸
            LinearMap.range (φ.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (φ.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (φ.baseChange (Localization.Away f))) := by
  sorry

end Module

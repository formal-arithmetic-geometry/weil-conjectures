/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorCochainData
public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.NativeOpenTensorPrimitives.CoefNativeOpenTensorPrimitives
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorSystemExistence
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorFiniteExistence

/-! # Ordinary native open tensor representatives

Existence of native restriction and projection data for an open immersion, on the sequence
site and for every finite coefficient ring, before derived localization.

## Implementation details

The open pro-étale site is identified with the localization of the ambient site, also after
product with the coefficient index. Uniqueness of adjoints identifies localized extension and
restriction with the fixed native functors; the open object is subterminal, so its adjunction
unit is invertible. Restriction preserves flat sheaves and K-flat complexes. The inverse of
the ordinary projection is the adjoint of the unit tensor identity followed by the inverse
restriction-tensor comparison; it is invertible by the ringed-slice projection formula. This
comparison is totalized using coproduct preservation by the left adjoint extension. The empty
open, zero rings, `n = 0` and unbounded complexes need no special treatment.

## References

* [Stacks, Tag 012Z]
* [Stacks, Tag 0E8I]
* [Stacks, Tag 0G7E]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Sequence-site specialization of ordinary open tensor data. -/
abbrev SystemOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  WeilConjectures.CoefSupportOpenTensor.NativeOpenTensorPrimitives.SystemOpenCochainsData l E j

/-- Finite-coefficient specialization of ordinary open tensor data. -/
abbrev FiniteOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (n : ℕ) :=
  WeilConjectures.CoefSupportOpenTensor.NativeOpenTensorPrimitives.FiniteOpenCochainsData l E j n

set_option linter.unusedVariables false in
/-- Native restriction and projection data before derived localization.
Ordinary open tensor data exist on the sequence site and for every finite coefficient ring. -/
theorem nativeOpenTensor_cochains_exists {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    ∃ (D : SystemOpenCochains l E j) (Dn : ∀ n : ℕ, FiniteOpenCochains l E j n), True := by
  obtain ⟨D, hD⟩ := nativeOpenTensor_system_exists l E j
  have hDn (n : ℕ) : ∃ Dn : FiniteOpenCochains l E j n, True :=
    nativeOpenTensor_finite_exists l E j n
  exact ⟨D, fun n ↦ Classical.choose (hDn n), hD⟩

end WeilConjectures.CoefSupportOpenTensor

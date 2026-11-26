/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.FormallySmoothCompleteDegreePUnitDerivation
import WeilConjectures.AlgebraicGeometry.DegreePExtensionRegular

/-!
# The degree-p step for formally smooth complete local algebras

Regularity of `L ⊗[A] C` ascends along a degree-`p` purely inseparable step `M ⊆ L` of
extensions of the fraction field, for `C` formally smooth and complete over a complete regular
local domain `A`.

## Implementation details

The presentation `L ⊗[A] C ≃ (M ⊗[A] C)[z]/(z^p - f)`, with a derivation `D` such that `D f` is
a unit, comes from `FormallySmoothCompleteDegreePUnitDerivation`. Regularity of the polynomial
quotient follows from Stacks 07PG and is transported along the isomorphism.

## References

* [Stacks, Tag 07PM] (last two paragraphs)
* [Stacks, Tag 07PG]
-/

@[expose] public section

universe u v w

namespace Algebra

attribute [-instance] IntermediateField.module' in
/-- Regularity ascends along a degree-p purely inseparable fraction-field step
for a formally smooth complete local algebra: if `M ⊗[A] C` is regular and `[L : M] = p`, then
`L ⊗[A] C` is regular. -/
theorem isRegularRing_tensorProduct_of_formallySmoothAdic_degree_p
    (A : Type u) (C : Type v) (K : Type u) (L : Type w)
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [CommRing C] [IsLocalRing C] [IsRegularRing C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [Module.Finite K L]
    [IsPurelyInseparable K L]
    [IsLocalHom (algebraMap A C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : IntermediateField K L) [Algebra A M] [IsScalarTower A K M]
    (hdegree : Module.finrank M L = p)
    (hregular : IsRegularRing (TensorProduct A M C))
    (hfs : FormallySmoothAdic A C (IsLocalRing.maximalIdeal C)) :
    IsRegularRing (TensorProduct A L C) := by
  obtain ⟨f, D, hunit, ⟨e⟩⟩ :=
    exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic
      A C K L p M hdegree hfs
  have := hregular
  have : IsRegularRing (Polynomial (TensorProduct A M C) ⧸
      Ideal.span {Polynomial.X ^ p - Polynomial.C f}) :=
    isRegularRing_quotient_X_pow_sub_of_isUnit_derivation
      (TensorProduct A M C) f D hunit p (Nat.Prime.one_le (Fact.out : p.Prime))
  exact IsRegularRing.of_ringEquiv e

end Algebra

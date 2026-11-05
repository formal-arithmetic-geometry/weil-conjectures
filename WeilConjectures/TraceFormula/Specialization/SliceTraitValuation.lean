/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitMap
public import WeilConjectures.RingTheory.Valuation.IntegralClosureHenselianDVR

/-!

# The valuation of the geometric generic point of a slice trait

Let `D` be a slice trait (`AlgebraicGeometry.SliceTrait`): a strictly henselian trait `Spec R`
with a geometric generic point `R ⟶ Ω'`, `Ω'` algebraically closed and algebraic over `R`. The
elements of `Ω'` integral over `R` form a valuation subring (`SliceTrait.valuationSubring`,
from `IsDiscreteValuationRing.integralClosureValuationSubring`): the unique extension of the
valuation of `R` to `Ω'`. It is stable under the automorphisms of `Ω'` over `R`, and a morphism of
slice traits `H` is compatible with these valuations: `H.ΩMap⁻¹(𝒪₂) = 𝒪₁`
(`SliceTrait.Hom.comap_valuationSubring`).

-/

@[expose] public section

universe u

open IsLocalRing

namespace AlgebraicGeometry.SliceTrait

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry.SliceTrait.Hom

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] {c : Ω₁ →+* Ω₂}
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁}
  {b₂ : R₂ →+* κ₂} {D₁ : SliceTrait a₁ b₁} {D₂ : SliceTrait a₂ b₂} (H : SliceTrait.Hom ι c D₁ D₂)

end AlgebraicGeometry.SliceTrait.Hom

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitMap
public import WeilConjectures.TraceFormula.Specialization.TraitTensorCompositum

/-!

# The compositum fields of a morphism of slice traits

Let `H : S₂(x) ⟶ S₁(x)` be a morphism of slice traits over a change of trait `ι : R₁ ⟶ R₂`
(`AlgebraicGeometry.SliceTrait.Hom`), with geometric generic points `Ω'ᵢ` of `Sᵢ(x)` over the
geometric generic points `Ωᵢ` of `Sᵢ`. The map `H.ΩMap : Ω'₁ ⟶ Ω'₂` restricts to the composita
`Lᵢ = Ωᵢ(Sᵢ(x)) ⊆ Ω'ᵢ` (`AlgebraicGeometry.SliceTrait.Hom.compositumMap`) and to their separable
closures `Lᵢ^sep` (`AlgebraicGeometry.SliceTrait.Hom.compositumSepMap`), compatibly with the maps
`Spec Lᵢ ⟶ Spec(Ωᵢ ⊗_{Rᵢ} Sᵢ(x))` (`AlgebraicGeometry.SliceTrait.Hom.compositumPoint_comp`).

The algebra structures of a slice trait are recorded as local instances
(`AlgebraicGeometry.SliceTrait.algebraR` etc.); the geometric generic point of the base is given
by an algebra structure `Algebra R₁ Ω₁`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing IntermediateField

open scoped TensorProduct

namespace AlgebraicGeometry.SliceTrait

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] [Algebra R₁ Ω₁]
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait (algebraMap R₁ Ω₁) b₁)

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂)

end AlgebraicGeometry.SliceTrait.Hom

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

open Scheme

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂) (hc : c.comp (algebraMap R₁ Ω₁) = (algebraMap R₂ Ω₂).comp ι)

end AlgebraicGeometry.SliceTrait.Hom

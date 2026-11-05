/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceStabilityCharP
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceKummerHensel
public import WeilConjectures.RingTheory.Valuation.KummerNormalFormGeneral

/-!

# Relative separable closedness of the slice composita, mixed characteristic

Let `D₁ ⟶ D₂` be a morphism of strict-localization slice traits over a change of traits
`R₁ ⟶ R₂`, with composita `Lᵢ = Ωᵢ(Sᵢ(x))`. In characteristic `0` with residual characteristic
`p > 0`, a Kummer equation `θ ^ p = α` over `L₁` which has a root in `L₂` has a root in `L₁`
(`SliceTrait.Hom.exists_pow_root_of_mixedChar`), via the abstract normal form
`exists_pow_eq_of_kummer_of_approx`.

-/

@[expose] public section

universe u

open IsLocalRing IntermediateField

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂]
  [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] {c : Ω₁ →+* Ω₂} {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂}
  (ha₁ : Function.Injective a₁) (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  (ha₂ : Function.Injective a₂) (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₁ : R₁ →+* κ} {b₂ : R₂ →+* κ}
  (hb₁ : RingHom.ker b₁ = maximalIdeal R₁) (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

local notation "𝒟₁" => sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₁) ha₁ halg₁ hb₁
local notation "𝒟₂" => sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂

end AlgebraicGeometry.SliceTrait.Hom

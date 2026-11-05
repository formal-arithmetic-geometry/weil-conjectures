/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitExists

/-!

# The points of the special fibre reached by the slice

Let `S₂ = Spec R₂` be a trait with separably closed point `b₂ : R₂ ⟶ κ`, `M` a model over `S₂`
with special fibre `X' = 𝒳_M ×_{S₂} Spec κ`, `cM : 𝒳_M ⟶ 𝔸¹_{S₂}` a coordinate over `S₂` and
`cX : X' ⟶ 𝔸¹_κ` the induced coordinate of the special fibre. For a slice trait `S'` over `S₂`
with closed point `Spec κ' ⟶ S'`, the special fibre `W = 𝒳_M ×_{𝔸¹_{S₂}} Spec κ'` of the slice of
`M` along `cM` is the base change of `cX` along the point `ξ : Spec κ' ⟶ 𝔸¹_κ` of the closed point
of `S'` (`NearbyCyclesModel.isPullback_sliceTraitSpecial`).

For the strict localization of `𝔸¹_{S₂}` at the generic point of its special fibre, `ξ` is the
generic point of `𝔸¹_κ`, so that every point of `X'` over the generic point of `𝔸¹_κ` comes from
the special fibre of the slice (`NearbyCyclesModel.mem_range_sliceTraitSpecial_of_isGenericPoint`):
this is how the slice step of Deligne's induction (SGA 4½, [Th. finitude], proof of 3.7) reaches
the points of `X'` over the generic point of a coordinate.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section SliceTrait

variable {R₂ : Type u} [CommRing R₂] {Ω₂ : Type u} [Field Ω₂] {a₂ : R₂ →+* Ω₂}
  {κ : Type u} [Field κ] {b₂ : R₂ →+* κ} {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')
  {q₂ : M.total ⟶ Spec (.of R₂)} {p₂ : X' ⟶ Spec (.of κ)}

variable [IsLocalRing R₂] (D : SliceTrait a₂ b₂)

end SliceTrait

section StrictLocalization

variable {R₂ : Type u} [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {Ω₂ : Type u} [Field Ω₂] {a₂ : R₂ →+* Ω₂}
  (ha₂ : Function.Injective a₂) (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  {κ : Type u} [Field κ] {b₂ : R₂ →+* κ} (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

end StrictLocalization

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

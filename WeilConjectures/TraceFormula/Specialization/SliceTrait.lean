/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!

# Slice traits over a strictly henselian trait

Let `S₁ = Spec R₁` be a strictly henselian trait, with a geometric generic point `a₁ : R₁ ⟶ Ω₁`
and a separably closed point `b₁ : R₁ ⟶ κ₁`. Deligne's proof of the finiteness of nearby cycles
and of their invariance under change of trait (SGA 4½, [Th. finitude], 3.3–3.9) slices along the
strict localization `S₁(x)` of `𝔸¹_{S₁}` at a geometric point over the generic point of its
special fibre: a strictly henselian trait, weakly étale over `𝔸¹_{S₁}`, with the same
uniformizer as `S₁`.

`AlgebraicGeometry.SliceTrait a₁ b₁` packages such a trait `S' = Spec R` with the structure map
`φ : R₁ ⟶ R`, a geometric generic point `a : R ⟶ Ω'` with `Ω'` algebraic over `Frac R`, and a
separably closed point `b : R ⟶ κ'`, compatible with those of `S₁`. Besides the trait, it records
the two properties of the strict localization used to describe the change of generic fibres:
* `φ` maps a uniformizer of `R₁` to a uniformizer of `R`;
* every element of the residue field of `R` which is algebraic over that of `R₁` comes from it.

For a model `N` of `Y` over `S₁` with a map `c : 𝒳_N ⟶ 𝔸¹_{S₁}` over `S₁`, the base change
`X' = 𝒳_N ×_{𝔸¹_{S₁}} S'` is a model over `S'` (`NearbyCyclesModel.sliceTraitModel`), mapped to the
geometric model of `N` by the *slice* morphism of models `σ` (`NearbyCyclesModel.sliceTraitHom`),
whose morphism of total spaces is weakly étale.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

namespace SliceTrait

attribute [instance] commRing isDomain isDiscreteValuationRing isStrictlyHenselianLocalRing
  isLocalHom_φ field_Ω isAlgClosed field_κ isSepClosed weaklyEtale

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)

end SliceTrait

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)
  {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
  (c : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)))

variable {q₁ : N.total ⟶ Spec (.of R₁)}
  (hc : c ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
  {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁)))
  {p₁ : Y' ⟶ Spec (.of κ₁)} (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

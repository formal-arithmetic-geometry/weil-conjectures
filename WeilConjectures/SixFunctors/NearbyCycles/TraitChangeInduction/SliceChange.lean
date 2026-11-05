/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Defs
public import WeilConjectures.TraceFormula.Specialization.SliceTraitMap

/-!

# The change of trait between the slices of a model and of its base change

Let `ι : R₁ ⟶ R₂` be a change of trait, `H : S₂(x) ⟶ S₁(x)` a morphism of slice traits over it
(`AlgebraicGeometry.SliceTrait.Hom`), `φ : M ⟶ N` a morphism of models over `Spec ι`, and
`cN : 𝒳_N ⟶ 𝔸¹_{S₁}`, `cM : 𝒳_M ⟶ 𝔸¹_{S₂}` compatible coordinates. The slices
`N' = 𝒳_N ×_{𝔸¹_{S₁}} S₁(x)` and `M' = 𝒳_M ×_{𝔸¹_{S₂}} S₂(x)`
(`NearbyCyclesModel.sliceTraitModel`) are related by a morphism of models
`NearbyCyclesModel.sliceTraitChangeHom : M' ⟶ N'` over `Spec ψ : S₂(x) ⟶ S₁(x)`; if the square of
total spaces of `φ` is cartesian over `Spec ι`, so is that of `sliceTraitChangeHom` over `Spec ψ`
(`NearbyCyclesModel.isPullback_sliceTraitChangeHom_total`). This is the change of trait to which
the induction hypothesis of Deligne's proof of SGA 4½, [Th. finitude], Prop. 3.7, applies
(`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitChangeHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Hom

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] {c : Ω₁ →+* Ω₂}
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁}
  {b₂ : R₂ →+* κ₂} {D₁ : SliceTrait a₁ b₁} {D₂ : SliceTrait a₂ b₂} (H : SliceTrait.Hom ι c D₁ D₂)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)))
  (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
  (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)

end Hom

section Induction

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁]
  [Field Ω₂] {c : Ω₁ →+* Ω₂} {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁]
  [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}

end Induction

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

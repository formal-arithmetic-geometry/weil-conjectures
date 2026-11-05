/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisSquare
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMapInvariants

/-!

# The slice step of Deligne's induction over a morphism of slice traits

Let `H : S₂(x) ⟶ S₁(x)` be a morphism of slice traits over a change of trait `ι : R₁ ⟶ R₂`,
inducing an isomorphism of closed points, and `φ : M ⟶ N` a morphism of models over `Spec ι` with
compatible coordinates `cN`, `cM`. If Prop. 3.7 holds in chart dimension `m` and the slice of `N`
over `S₁(x)` locally embeds into `𝔸ᵐ`, then the pullback of the exchange of `φ.toGeneric` to the
special fibre of the slice of `M` is invertible at every complex bounded below of étale origin
(`NearbyCyclesModel.isIso_map_pullbackExchange_sliceTraitSpecial`), provided the composita
`Lᵢ = Ωᵢ(Sᵢ(x))` have Galois extensions `Lᵢ^sep / Lᵢ` of degrees invertible in the coefficients and
`L₁` is relatively separably closed in `L₂`.

This is the step (A) of SGA 4½, [Th. finitude], proof of 3.7: the four squares
```
M'  ──φ'──→  N'          N₂ ──τ──→ N₁
 │ρ_M         │ρ_N         │ψ_M      │ψ_N
N₂_{L₂^sep} ─τ'→ N₁_{L₁^sep}   M ──φ──→  N
```
reduce the change of trait on the slice to the change of trait `φ'` of the slices (the induction
hypothesis, `NearbyCyclesModel.isIso_pullbackExchange_sliceTraitChangeHom`), through the change of
Galois layers `τ'` (`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitGaloisLayerMap`), the
invariants under the wild inertia groups
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic`)
and the
Galois-layer models (`NearbyCyclesModel.isIso_map_pullbackExchange_of_sliceTraitGaloisChangeHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme SliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsStrictlyHenselianLocalRing R₁] [CommRing R₂]
  [IsStrictlyHenselianLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂) (hc : c.comp (algebraMap R₁ Ω₁) = (algebraMap R₂ Ω₂).comp ι)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁))) {q₁ : N.total ⟶ Spec (.of R₁)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
  {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
  {p₁ : Y' ⟶ Spec (.of κ₁)} (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
  (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂))) {q₂ : M.total ⟶ Spec (.of R₂)}
  (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
  {g₂ : M.generic ⟶ Spec (.of Ω₂)}
  (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom (algebraMap R₂ Ω₂))))
  {p₂ : X' ⟶ Spec (.of κ₂)} (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
  (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)
  (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

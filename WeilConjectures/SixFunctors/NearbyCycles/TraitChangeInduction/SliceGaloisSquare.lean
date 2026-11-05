/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGalois
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelWeaklyEtale

/-!

# The change of trait on the generic slice from the change of the Galois-layer models

In the situation of `WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGalois`,
the model `N₁` (`NearbyCyclesModel.sliceTraitGaloisModel`) maps to `N` by the nilpotent
thickening `r₂` followed by the weakly étale cartesian part of the slice
(`NearbyCyclesModel.sliceTraitGaloisModelHom`), with invertible pullback exchange
(`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitGaloisModelHom`). The square
```
N₂ ──τ──→ N₁
 │ψ_M      │ψ_N
 M ──φ──→  N
```
then shows that the pullback of the exchange of `φ` to the special fibre of the slice of `M` is
invertible as soon as the exchange of `τ` is
(`NearbyCyclesModel.isIso_map_pullbackExchange_of_sliceTraitGaloisChangeHom`): this is the step
of Deligne's proof of SGA 4½, [Th. finitude], 3.7, which identifies the change of trait on the
generic slice with the change of trait on the invariant summands.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme SliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

section General

variable {R₁ R Ω₁ Ω : Type u} [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (q : M.total ⟶ Spec (.of R)) (q₁ : N.total ⟶ Spec (.of R₁)) (g₁ : N.generic ⟶ Spec (.of Ω₁))
  (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
  (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))

end General

section Single

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)
  {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R))) {q : N.total ⟶ Spec (.of R)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R) = q)
  {g : N.generic ⟶ Spec (.of Ω)}
  (hNj : IsPullback N.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
  {p : Y' ⟶ Spec (.of κ)} (hNi : IsPullback N.i p q (Spec.map (CommRingCat.ofHom b)))

end Single

section Pair

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
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

end Pair

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

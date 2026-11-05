/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceChange
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayer
public import WeilConjectures.SixFunctors.NearbyCycles.UniversalHomeomorphismExchange

/-!

# The change of trait between the Galois layers of two slices

Let `H : S₂(x) ⟶ S₁(x)` be a morphism of slice traits over a change of trait `ι : R₁ ⟶ R₂`,
`φ : M ⟶ N` a morphism of models over `Spec ι` and `cN`, `cM` compatible coordinates, with slices
`σ_N : N' ⟶ N`, `σ_M : M' ⟶ M` over the slice traits
(`NearbyCyclesModel.sliceTraitHom`) and change of trait of the slices `φ' : M' ⟶ N'`
(`NearbyCyclesModel.sliceTraitChangeHom`). The change of geometric generic fibres of `σ_N` is,
up to universal homeomorphisms, the Galois layer of `L₁^sep / L₁` over the model `N₁`
(`NearbyCyclesModel.Hom.traitChangeModel`), and likewise for `σ_M` with `L₂^sep / L₂`. This file
constructs the change of trait `τ : N₂ ⟶ N₁` of these models over `Spec l : Spec L₂ ⟶ Spec L₁`
(`NearbyCyclesModel.sliceGaloisChangeHom`) and checks the two commutative squares
```
M'  ──φ'──→  N'                N₂ ──τ──→ N₁
 │ρ_M         │ρ_N              │ψ_M       │ψ_N
N₂_{L₂^sep} ─τ'→ N₁_{L₁^sep}    M  ──φ──→  N
```
of morphisms of models, with `τ'` the change of Galois layers (`NearbyCyclesModel.galoisLayerMap`),
`ρ` the universal homeomorphisms onto the Galois layers and `ψ` the composites of the nilpotent
thickenings and the weakly étale cartesian parts. These are the squares through which Deligne's
induction (SGA 4½, [Th. finitude], proof of 3.7) reduces the change of trait on the generic slice
to the change of trait of the slices.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme SliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

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

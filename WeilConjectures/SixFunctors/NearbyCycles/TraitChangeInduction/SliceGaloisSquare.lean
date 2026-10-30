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

section Single

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)
  {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R))) {q : N.total ⟶ Spec (.of R)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R) = q)
  {g : N.generic ⟶ Spec (.of Ω)}
  (hNj : IsPullback N.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
  {p : Y' ⟶ Spec (.of κ)} (hNi : IsPullback N.i p q (Spec.map (CommRingCat.ofHom b)))

/-- The morphism of models `ψ : N₁ ⟶ N`: the nilpotent thickening `r₂` of generic fibres followed
by the weakly étale cartesian part of the slice. -/
noncomputable abbrev sliceTraitGaloisModelHom :
    (sliceTraitGaloisModel D N cN hcN hNj hNi).Hom N.toGeneric (𝟙 _ ≫ 𝟙 _)
      (𝟙 _ ≫ sliceTraitSpecial D N cN hcN hNi) :=
  ((sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeModelHom D.Ω (sliceTraitStructure D N cN)
    q g hNj.w (sliceTrait_fst_comp D N cN hcN)).comp
    (sliceTraitGenericHom D N cN hcN hNj hNi).fromCartesian

/-- The pullback exchange of `ψ : N₁ ⟶ N` is invertible: the nilpotent thickening is a universal
homeomorphism, and the cartesian part is weakly étale base change. -/
theorem isIso_pullbackExchange_sliceTraitGaloisModelHom [Subsingleton (PrimeSpectrum (Ω ⊗[R] D.R))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic))) :
    IsIso (((sliceTraitGaloisModelHom D N cN hcN hNj hNi).pullbackExchange Λ).app C) := by
  have : WeaklyEtale (sliceTraitGenericHom D N cN hcN hNj hNi).total :=
    inferInstanceAs (WeaklyEtale (pullback.fst cN D.toAffineLine))
  have h₁ := (sliceTraitGenericHom D N cN hcN hNj hNi).isIso_pullbackExchange_fromCartesian_of_weaklyEtale
    Λ
  have h₂ : IsIso (((sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeModelHom D.Ω
      (sliceTraitStructure D N cN) q g hNj.w (sliceTrait_fst_comp D N cN hcN)).pullbackExchange Λ |>.app
        (L((𝟙 N.generic)^*⟦Λ⟧).obj C)) :=
    Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ
    (sliceTraitGenericHom D N cN hcN hNj hNi).cartesianModel
    ((sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeThickening D.Ω
      (sliceTraitStructure D N cN) q g hNj.w (sliceTrait_fst_comp D N cN hcN))
    (sliceTraitGaloisModel D N cN hcN hNj hNi) rfl
    ((sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeModelHom D.Ω
      (sliceTraitStructure D N cN) q g hNj.w (sliceTrait_fst_comp D N cN hcN)) HEq.rfl HEq.rfl _
  exact Hom.isIso_pullbackExchange_app_comp Λ _ _ C inferInstance h₂

end Single

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

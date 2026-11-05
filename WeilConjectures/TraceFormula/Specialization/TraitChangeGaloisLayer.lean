/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsTorsion
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit
public import WeilConjectures.TraceFormula.Specialization.TraitTensorCompositum

/-!

# The change of geometric generic fibre over a change of trait, as a Galois layer

Let `φ : M ⟶ N` be a morphism of models, with `M` over `Spec R` and geometric generic point
`Spec Ω` (the square `M.generic ⟶ M.total ⟶ Spec R`, `M.generic ⟶ Spec Ω ⟶ Spec R` is cartesian)
and `N` over `Spec R₁` with geometric generic point `Spec Ω₁`, compatibly with a ring map
`R₁ ⟶ R` and an embedding `Ω₁ ⟶ Ω`. Put `T = Spec(Ω₁ ⊗_{R₁} R)`.

* The generic fibre of the cartesian model of `φ` is `M.total ×_{Spec R} T`
  (`NearbyCyclesModel.Hom.isPullback_cartesianModelTensor`), and the change of geometric generic
  fibre `g = φ.toCartesian.generic` is the base change of `ρ : Spec Ω ⟶ T`
  (`NearbyCyclesModel.Hom.isPullback_toCartesian_generic_cartesianModelTensor`).
* When `T` is a single point, the factorisation `Spec Ω ⟶ Spec L^sep ⟶ Spec L ⟶ T` of `ρ`
  (`AlgebraicGeometry.traitTensorSepPoint_comp_traitTensorCompositumGalois_comp`) gives
  `g = r₁ ≫ q ≫ r₂` with `r₁`, `r₂` universal homeomorphisms and `q` the projection of the
  Galois layer of the model `N₂` with generic fibre `Z₂ = (M.total ×_{Spec R} T) ×_T Spec L`
  along `Z₂ ⟶ Spec L` and the Galois extension `L^sep / L`
  (`NearbyCyclesModel.Hom.traitChangeInsepMap_comp_traitChangeGaloisMap_comp`,
  `NearbyCyclesModel.Hom.traitChangeModel`).
* Consequently, with torsion coefficients `T₀` in which the degrees of the finite Galois
  subextensions of `L^sep / L` are invertible, the pullback exchange of `φ.toCartesian` is a split
  monomorphism at every complex of étale origin
  (`NearbyCyclesModel.Hom.isSplitMono_toCartesian_pullbackExchange_app_of_traitChange`).

This generalises `NearbyCyclesModel.affineSpaceSliceHom_toCart_generic_factor` (SGA 4½,
[Th. finitude], 3.4).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme

variable {R₁ R Ω₁ Ω : Type u} [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (q : M.total ⟶ Spec (.of R)) (g : M.generic ⟶ Spec (.of Ω))
  (q₁ : N.total ⟶ Spec (.of R₁)) (g₁ : N.generic ⟶ Spec (.of Ω₁))

variable {φ q g q₁ g₁}

section Factor

variable (Ω φ q g q₁ g₁)
variable (hN : N.j ≫ q₁ = g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
  (hq : φ.total ≫ q₁ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ R)))

variable {Ω φ q g q₁ g₁}

variable (Ω φ q g q₁ g₁)

end Factor

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect

/-!

# The zero-section map on the unit

For the constant complex `Λ`, the zero-section map `ε_{X,Z}(Λ)` is compared with the specialization
units through the unit law of the pullback exchange (blueprint `sk-lem-tf-nearby-mate-coherences`
(2)): `ε_{X,Z}(Λ) ∘ Le^* σ_{𝒟_Z X} = Ψ_{Z × S}(ε_i) ∘ σ_{Z × S} ∘ ε_e⁻¹`. Hence `ε_{X,Z}(Λ)` is an
isomorphism as soon as the specialization unit of the constant family `Z × S` and the restriction
of the specialization unit of `𝒟_Z X` to the zero section are
(`ProEtale.CondensedRing.isIso_zeroSectionMap_unit`; the constant-coefficient step of blueprint
`det-sp-thick-origin`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The zero-section map on the unit** (constant-coefficient step of blueprint
`det-sp-thick-origin`): if the specialization unit `σ_{Z × S}` of the constant family of the
centre is an isomorphism, and so is the restriction `Le^* σ_{𝒟_Z X}` of the specialization unit of
the deformation to the zero section, then the zero-section map `ε_{X,Z}(Λ)` is an isomorphism. -/
theorem isIso_zeroSectionMap_unit
    [hM : IsIso ((deformationModel (centre X I) ⊥ k').unit Λ)]
    [hN : IsIso (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
      ((deformationModel X I k').unit Λ))] :
    IsIso (zeroSectionMap X I k' Λ (𝟙_ _)) := by
  have h := (zeroSectionDeformationModelHom X I k').map_unit_comp_pullbackExchange_app Λ
  have h' : zeroSectionMap X I k' Λ (𝟙_ _) =
      inv (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
        ((deformationModel X I k').unit Λ)) ≫
        ((leftDerivedUpperStarUnitIso Λ (zeroSectionSpecialFibreMap X I k').left).hom ≫
          (deformationModel (centre X I) ⊥ k').unit Λ ≫
          ((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).map
            (leftDerivedUpperStarUnitIso Λ (centreι X I).left).inv) := by
    rw [← h, IsIso.inv_hom_id_assoc]
    rfl
  rw [h']
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionConstantComplexCompat

/-!
# The transposes of `Ψ Λ ≅ Λ'` and the derived pullbacks

The transposes `Λ ⟶ Res Λ'` under `Ψ ⊣ Res` of the counits `η : Ψ Λ ≅ Λ'` of the derived
extension of scalars are compatible with the derived pullback along `t : X ⟶ S`
(`leftDerivedUpperStar_map_unit_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom`),
as soon as the canonical maps `Λ ⟶ Res Λ'` of the homotopy categories are compatible with
`t^*` (`AlgebraicGeometry.Etale.HomotopyUnitRestrictScalarsCompat`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Pullback

variable {X S : Scheme.{u}} (t : X ⟶ S)

set_option maxHeartbeats 1600000 in
-- the kernel compares the units of the monoidal homotopy and derived categories
/-- The transposes `Λ ⟶ Res Λ'` of the identifications `Ψ Λ ≅ Λ'` are compatible with the
derived pullback along `t`. -/
lemma leftDerivedUpperStar_map_unit_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom
    (H : HomotopyUnitRestrictScalarsCompat ρ t) :
    (L((t)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedExtendScalarsAdjunction hρ ha S).unit.app (constantComplex Λ S) ≫
          (Sheaf.derivedRestrictScalars S.smallEtaleTopology ρ).map
            (derivedExtendScalarsConstantComplexEtaIso hρ ha S).hom) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app _ ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        (leftDerivedUpperStarConstantComplexIso Λ' t).hom =
    (leftDerivedUpperStarConstantComplexIso Λ t).hom ≫
      (derivedExtendScalarsAdjunction hρ ha X).unit.app (constantComplex Λ X) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  have := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  have hf : (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (DerivedCategory.Qh.map
      (η ((t)^*[ModuleCat.{u + 1} Λ'].mapHomotopyCategory (.up ℤ)))) =
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).map (η ((t)^*[ModuleCat.{u + 1} Λ'].mapHomotopyCategory (.up ℤ)))) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app _ :=
    (NatIso.naturality_2 (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh
      _).symm
  have hc : (L((t)^*[ModuleCat.{u + 1} Λ])).map
        (DerivedCategory.Qh.map (homotopyUnitRestrictScalars ρ S)) ≫
      (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit.app _ =
      (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit.app _ ≫
      DerivedCategory.Qh.map (((t)^*[ModuleCat.{u + 1} Λ].mapHomotopyCategory (.up ℤ)).map
        (homotopyUnitRestrictScalars ρ S)) :=
    (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit.naturality _
  have H' := congrArg (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).map H
  simp only [Functor.map_comp] at H'
  rw [unit_app_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom,
    unit_app_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom,
    leftDerivedUpperStarConstantComplexIso_hom_eq_counit,
    leftDerivedUpperStarConstantComplexIso_hom_eq_counit]
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc]
  rw [hf, Category.assoc, Category.assoc]
  erw [reassoc_of% leftDerivedUpperStarRestrictScalarsIso_hom_app_unit ρ t]
  rw [← Functor.map_comp_assoc (L((t)^*[ModuleCat.{u + 1} Λ]))
    ((Sheaf.restrictScalars S.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app _),
    Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hc, reassoc_of% H']

end Pullback

end Etale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangeSingle

/-!
# The unit comparison of the reduction of coefficients is the change of coefficients

The unit comparison `Ψ Λ_X ≅ Λ'_X` of the derived extension of scalars is the adjoint of the
change of coefficients `Λ_X ⟶ Res Λ'_X` of the constant complexes
(`derivedExtendScalarsUnitIso_hom_eq_homEquiv_symm_constantComplexChangeMap`):
the latter is, on homotopy categories, the unit map `𝟙 ⟶ Res 𝟙`
(`AlgebraicGeometry.Etale.constantComplexChangeMap_comp_mapDerivedCategoryFactorsh`).
-/

@[expose] public section

universe u


open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

variable (ρ) in
/-- The change of coefficients `Λ_X ⟶ Res Λ'_X` of the constant complexes
(`AlgebraicGeometry.Etale.constantComplexChangeMap`) is induced on homotopy categories by the unit
map `𝟙 ⟶ Res 𝟙`. -/
lemma constantComplexChangeMap_comp_mapDerivedCategoryFactorsh [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] :
    constantComplexChangeMap ρ X ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map (extendScalarsHomotopyUnitMap ρ X) := by
  rw [extendScalarsHomotopyUnitMap_eq, ← singleFunctorObjUnitIso_inv_comp_map_comp_factorsh,
    constantComplexChangeMap_eq, extendScalarsConstantZModIso_inv_comp_extendScalarsChangeMap_app]
  simp only [Category.assoc]

/-- Blueprint `det-sp-purity-coefficient-change` (the unit comparison of the reduction).

**The unit comparison `Ψ Λ_X ≅ Λ'_X` is the adjoint of the change of coefficients**
`Λ_X ⟶ Res Λ'_X` of the constant complexes (`AlgebraicGeometry.Etale.constantComplexChangeMap`). -/
lemma derivedExtendScalarsUnitIso_hom_eq_homEquiv_symm_constantComplexChangeMap
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] :
    (derivedExtendScalarsUnitIso hρ ha X).hom =
      ((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).symm
        (constantComplexChangeMap ρ X) :=
  derivedExtendScalarsUnitIso_hom_eq_homEquiv_symm hρ ha X _
    (constantComplexChangeMap_comp_mapDerivedCategoryFactorsh ρ X)

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.CompactifiedProjection
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Id

/-!
# The compactified projection formula for the identity compactification

Let `f : X ⟶ Y` be a proper morphism and `c = Compactification.ofIsProper f` its identity
compactification `X ⟶[𝟙] X ⟶[f] Y`. The extension by zero along `𝟙 X` is identified with the
identity functor (`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekIdIso`), hence
`Rf_!^{(1,f)} = Rf_* ∘ (𝟙 X)_!` with `Rf_*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationOfIsProperIso`). Under
this identification the open-piece isomorphism `θ_1` of the identity is the identity
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionMap_id_comp`), the
compactified projection map `PF_c` is the projection map `π_{f,E,Q}`
(`AlgebraicGeometry.ProEtale.projectionMapOfCompactification_ofIsProper`), and its inverse is
`ρ_{f,E,Q}` (`AlgebraicGeometry.ProEtale.projectionMapOfCompactificationInv_ofIsProper`). This is
blueprint `lemma-weil-pbc-projection-formula-identity-compactification`.

## Implementation notes

The identification `(𝟙 X)_! ≅ 𝟭` is taken to be the one conjugate, along the adjunction
`(𝟙 X)_! ⊣ (𝟙 X)^*`, to the identification `(𝟙 X)^* ≅ L(𝟙 X)^* ≅ 𝟭`; with this choice the unit
of the adjunction becomes the identity. That `θ_1` is then the identity rests on the
monoidality of `L(𝟙 X)^* ≅ 𝟭` (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_id_comp`)
and the comparison of the composition isomorphism `L(𝟙 X ≫ f)^* ≅ Lf^* ⋙ L(𝟙 X)^*` with it
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp_hom_app_comp_leftDerivedUpperStarId_hom_app`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

section Id

variable (X : Scheme.{u})

/-- The identification `D((𝟙 X)^*) ≅ L(𝟙 X)^* ≅ 𝟭` of the pullback along the identity on
derived categories. -/
noncomputable def mapDerivedCategoryUpperStarIdIso :
    D((𝟙 X)^*[A]) ≅ 𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  (leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 X)).symm ≪≫ leftDerivedUpperStarId A X

/-- The identification `D((𝟙 X)_!) ≅ 𝟭` of the extension by zero along the identity: the
conjugate of `AlgebraicGeometry.ProEtale.mapDerivedCategoryUpperStarIdIso` along the
adjunction `D((𝟙 X)_!) ⊣ D((𝟙 X)^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekIdIso :
    D((𝟙 X)_!open[A]) ≅ 𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  (conjugateIsoEquiv Adjunction.id
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A (𝟙 X))).symm
      (mapDerivedCategoryUpperStarIdIso A X).symm

/-- The unit of `D((𝟙 X)_!) ⊣ D((𝟙 X)^*)` is the identity under the identifications
`D((𝟙 X)_!) ≅ 𝟭` and `D((𝟙 X)^*) ≅ 𝟭`. -/
@[reassoc]
lemma unit_app_comp_map_derivedOpenImmersionLowerShriekIdIso_hom_app
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A (𝟙 X)).unit.app E ≫
        D((𝟙 X)^*[A]).map ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E) =
      (mapDerivedCategoryUpperStarIdIso A X).inv.app E := by
  have h := unit_conjugateEquiv_symm Adjunction.id
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A (𝟙 X))
    (mapDerivedCategoryUpperStarIdIso A X).inv E
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp] at h
  exact h.symm

variable [ProEtale.UpperStarPreservesFlat A]

/-- **The open piece of the identity compactification is the identity**: under
`D((𝟙 X)_!) ≅ 𝟭` and `L(𝟙 X)^* ≅ 𝟭`, the projection isomorphism
`θ : (𝟙 X)_!(E ⊗ᴸ L(𝟙 X)^*M) ≅ (𝟙 X)_!E ⊗ᴸ M`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionMap`) is the identity of
`E ⊗ᴸ M`. -/
lemma derivedOpenImmersionLowerShriekProjectionMap_id_comp
    (E M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedOpenImmersionLowerShriekProjectionMap A (𝟙 X)).app E).app M ≫
        ((-⊗ᴸ-(X)[A]).map ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E)).app M =
      D((𝟙 X)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj E).map
          ((leftDerivedUpperStarId A X).hom.app M)) ≫
        (derivedOpenImmersionLowerShriekIdIso A X).hom.app (((-⊗ᴸ-(X)[A]).obj E).obj M) := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction A (𝟙 X)
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  -- the right hand side
  have hR := adj.unit.naturality_assoc (((-⊗ᴸ-(X)[A]).obj E).map
    ((leftDerivedUpperStarId A X).hom.app M))
    (D((𝟙 X)^*[A]).map ((derivedOpenImmersionLowerShriekIdIso A X).hom.app
      (((-⊗ᴸ-(X)[A]).obj E).obj M)))
  simp only [Functor.id_map, Functor.comp_map] at hR
  erw [← hR, unit_app_comp_map_derivedOpenImmersionLowerShriekIdIso_hom_app]
  -- the left hand side
  erw [Adjunction.unit_app_comp_map_projectionMap_app_app_assoc]
  have hτ := NatTrans.congr_app ((mapDerivedCategoryUpperStarDerivedTensorIso A (𝟙 X)).hom.naturality
    ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E)) M
  simp only [NatTrans.comp_app] at hτ
  dsimp only [Adjunction.projectionMapTranspose, NatTrans.comp_app]
  erw [Category.assoc, ← hτ]
  dsimp only [Functor.whiskeringLeft₂, Functor.postcompose₂]
  trace_state
  sorry

end Id

end ProEtale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapTrivial
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifiedProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Id

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
monoidality of `L(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_id_comp`)
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
  refine Adjunction.projectionMap_app_app_comp_map_of_trivial
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A (𝟙 X)) L((𝟙 X)^*[A]) (-⊗ᴸ-(X)[A])
    (mapDerivedCategoryUpperStarDerivedTensorIso A (𝟙 X)).hom
    (derivedOpenImmersionLowerShriekIdIso A X).hom (mapDerivedCategoryUpperStarIdIso A X).inv
    (leftDerivedUpperStarId A X).hom
    (unit_app_comp_map_derivedOpenImmersionLowerShriekIdIso_hom_app A X) (fun K N ↦ ?_) E M
  dsimp [mapDerivedCategoryUpperStarIdIso, mapDerivedCategoryUpperStarDerivedTensorIso]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono ((leftDerivedUpperStarId A X).hom.app _), Category.assoc, Category.assoc,
    Iso.inv_hom_id_app]
  erw [← leftDerivedUpperStarTensorComparison_id_comp A K N]
  rw [← leftDerivedUpperStarTensorNatIso_hom, Iso.inv_hom_id_app_app_assoc]
  erw [Category.comp_id, tensorHom_def, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id_app, id_whiskerRight, Category.id_comp]
  rfl

omit [ProEtale.UpperStarPreservesFlat A] in
/-- The transport `eqToHom` of the derived pullback along an equality `a = b` of morphisms is the
transport isomorphism `AlgebraicGeometry.ProEtale.leftDerivedUpperStarCongr`. -/
lemma eqToHom_app_eq_leftDerivedUpperStarCongr_hom_app {Y : Scheme.{u}} {a b : X ⟶ Y}
    (h : a = b) (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (eqToHom (congrArg (fun h ↦ L((h)^*[A])) h)).app Q =
      (leftDerivedUpperStarCongr A h).hom.app Q := by
  subst h
  simp

end Id

section OfIsProper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- For the identity compactification `X ⟶[𝟙] X ⟶[f] Y` of a proper morphism `f`, the
isomorphism `L(𝟙 X)^* Lf^* ≅ Lf^*` of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarCompactificationIso` is the identity
isomorphism `L(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarCompactificationIso_ofIsProper_hom_app
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarCompactificationIso A (Compactification.ofIsProper f)).hom.app Q =
      (leftDerivedUpperStarId A X).hom.app (L((f)^*[A]).obj Q) := by
  dsimp only [leftDerivedUpperStarCompactificationIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom]
  rw [eqToHom_app_eq_leftDerivedUpperStarCongr_hom_app, ← leftDerivedUpperStarComp_id_left_app]
  · exact Iso.inv_hom_id_app_assoc _ _ _
  · exact Category.id_comp f

/-- The identification `Rf_!^{(1,f)} = Rf_* ∘ (𝟙 X)_! ≅ Rf_*` of the compactly supported direct
image computed with the identity compactification of a proper morphism `f` with the derived
direct image, induced by `D((𝟙 X)_!) ≅ 𝟭`
(`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekIdIso`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationOfIsProperIso :
    rightDerivedLowerShriekOfCompactification A (Compactification.ofIsProper f) ≅
      R((f)_*[A]) :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekIdIso A X) R((f)_*[A]) ≪≫
    Functor.leftUnitor _

@[simp]
lemma rightDerivedLowerShriekOfCompactificationOfIsProperIso_hom_app
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (rightDerivedLowerShriekOfCompactificationOfIsProperIso A f).hom.app E =
      R((f)_*[A]).map ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E) := by
  simp [rightDerivedLowerShriekOfCompactificationOfIsProperIso]

variable [ProEtale.UpperStarPreservesFlat A]

/-- Under `D((𝟙 X)_!) ≅ 𝟭` and `L(𝟙 X)^* ≅ 𝟭`, the inverse open-piece isomorphism
`θ⁻¹ : (𝟙 X)_!E ⊗ᴸ M ≅ (𝟙 X)_!(E ⊗ᴸ L(𝟙 X)^*M)`, followed by the identification
`L(𝟙 X)^*Lf^* ≅ Lf^*` of the identity compactification, is the identity of `E ⊗ᴸ Lf^*Q`. -/
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_ofIsProper
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((derivedOpenImmersionLowerShriekProjectionIso A (𝟙 X)).inv.app E).app
          (L((f)^*[A]).obj Q) ≫
        D((𝟙 X)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj E).map
          ((leftDerivedUpperStarCompactificationIso A (Compactification.ofIsProper f)).hom.app
            Q)) ≫
        (derivedOpenImmersionLowerShriekIdIso A X).hom.app
          (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj Q)) =
      ((-⊗ᴸ-(X)[A]).map ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E)).app
        (L((f)^*[A]).obj Q) := by
  rw [leftDerivedUpperStarCompactificationIso_ofIsProper_hom_app,
    ← derivedOpenImmersionLowerShriekProjectionMap_id_comp, ← NatTrans.comp_app_assoc,
    ← NatTrans.comp_app, ← derivedOpenImmersionLowerShriekProjectionIso_hom, Iso.inv_hom_id_app,
    Category.id_comp]

/-- **The identity compactification recovers the projection map** (blueprint
`lemma-weil-pbc-projection-formula-identity-compactification`). For a proper morphism `f`, under
`Rf_!^{(1,f)} ≅ Rf_*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationOfIsProperIso`) the
compactified projection map `PF_c` of the identity compactification is the projection map
`π_{f,E,Q}`. -/
lemma projectionMapOfCompactification_ofIsProper
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((projectionMapOfCompactification A (Compactification.ofIsProper f)).app E).app Q ≫
        (rightDerivedLowerShriekOfCompactificationOfIsProperIso A f).hom.app
          (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj Q)) =
      ((-⊗ᴸ-(Y)[A]).map ((rightDerivedLowerShriekOfCompactificationOfIsProperIso A f).hom.app
          E)).app Q ≫
        ((rightDerivedLowerStarProjectionMap A f).app E).app Q := by
  have h2 : ((rightDerivedLowerStarProjectionMap A f).app (D((𝟙 X)_!open[A]).obj E)).app Q ≫
      R((f)_*[A]).map (((-⊗ᴸ-(X)[A]).map
        ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E)).app (L((f)^*[A]).obj Q)) =
      ((-⊗ᴸ-(Y)[A]).map (R((f)_*[A]).map
        ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E))).app Q ≫
        ((rightDerivedLowerStarProjectionMap A f).app E).app Q :=
    (congr_app ((rightDerivedLowerStarProjectionMap A f).naturality
      ((derivedOpenImmersionLowerShriekIdIso A X).hom.app E)) Q).symm
  have key : ((projectionMapOfCompactification A (Compactification.ofIsProper f)).app E).app Q ≫
        (rightDerivedLowerShriekOfCompactificationOfIsProperIso A f).hom.app
          (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj Q)) =
      ((rightDerivedLowerStarProjectionMap A f).app (D((𝟙 X)_!open[A]).obj E)).app Q ≫
        R((f)_*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A (𝟙 X)).inv.app E).app
          (L((f)^*[A]).obj Q)) ≫
        R((f)_*[A]).map (D((𝟙 X)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj E).map
          ((leftDerivedUpperStarCompactificationIso A (Compactification.ofIsProper f)).hom.app
            Q))) ≫
        R((f)_*[A]).map ((derivedOpenImmersionLowerShriekIdIso A X).hom.app
          (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj Q))) := by
    rw [projectionMapOfCompactification_app_app,
      rightDerivedLowerShriekOfCompactificationOfIsProperIso_hom_app, Category.assoc,
      Category.assoc]
    have hπ : rightDerivedLowerStarProjectionMap A (Compactification.ofIsProper f).g =
      rightDerivedLowerStarProjectionMap A f := rfl
    rw [hπ]
    rfl
  rw [key, ← Functor.map_comp, ← Functor.map_comp,
    derivedOpenImmersionLowerShriekProjectionIso_inv_ofIsProper A f E Q, h2,
    rightDerivedLowerShriekOfCompactificationOfIsProperIso_hom_app]

/-- **The identity compactification recovers `ρ`** (blueprint
`lemma-weil-pbc-projection-formula-identity-compactification`). For a proper morphism `f` and a
complex `F` with a strict-perfect package, under `Rf_!^{(1,f)} ≅ Rf_*`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationOfIsProperIso`) the
inverse of the compactified projection map of the identity compactification
(`AlgebraicGeometry.ProEtale.projectionMapOfCompactificationInv`) is
`ρ_{f,E,F} = AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionInv`. -/
lemma projectionMapOfCompactificationInv_ofIsProper
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ}
    (P : F.StrictPerfectPackage (𝟙_ (Sheaf (Scheme.ProEt.topology Y) A))) :
    projectionMapOfCompactificationInv A (Compactification.ofIsProper f) E P ≫
        ((-⊗ᴸ-(Y)[A]).map ((rightDerivedLowerShriekOfCompactificationOfIsProperIso A f).hom.app
          E)).app (DerivedCategory.Q.obj F) =
      (rightDerivedLowerShriekOfCompactificationOfIsProperIso A f).hom.app
          (((-⊗ᴸ-(X)[A]).obj E).obj (L((f)^*[A]).obj (DerivedCategory.Q.obj F))) ≫
        rightDerivedLowerStarProjectionInv A f E P := by
  have := isIso_projectionMapOfCompactification_app_app_of_strictPerfectPackage A
    (Compactification.ofIsProper f) E P
  have := isIso_rightDerivedLowerStarProjectionMap_of_strictPerfectPackage A f E P
  rw [← cancel_epi (((projectionMapOfCompactification A (Compactification.ofIsProper f)).app
      E).app (DerivedCategory.Q.obj F)), projectionMapOfCompactification_comp_inv_assoc,
    ← cancel_mono (((rightDerivedLowerStarProjectionMap A f).app E).app
      (DerivedCategory.Q.obj F)), Category.assoc, Category.assoc,
    rightDerivedLowerStarProjectionInv_comp, Category.comp_id]
  exact (projectionMapOfCompactification_ofIsProper A f E _).symm

end OfIsProper

end ProEtale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility

/-!
# The extension of scalars `𝒪_E ⟶ E` as a coefficient change

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. This
file shows that the extension of scalars `T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧`, with the comparisons
(Pull) (`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`), (Shriek) for open
immersions and (Push) (the mate of (Pull)) of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility`, is
a coefficient change of the bounded constructible six functors
(`ProEtale.CondensedRing.extendScalarsCoefficientChange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

lemma boundedConstructibleExtendScalars_obj_obj (X : Scheme.{u})
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((boundedConstructibleExtendScalars X ℓ E).obj K).obj =
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj K.obj :=
  rfl

lemma boundedConstructibleExtendScalars_map_hom (X : Scheme.{u})
    {K L : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧} (φ : K ⟶ L) :
    ((boundedConstructibleExtendScalars X ℓ E).map φ).hom =
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.map φ.hom :=
  rfl

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section Components

variable (f : X ⟶ Y)

lemma boundedConstructibleUpperStarExtendScalarsIso_hom_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((boundedConstructibleUpperStarExtendScalarsIso ℓ E f).hom.app K).hom =
      (derivedPullIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left).hom.app K.obj := by
  simp [boundedConstructibleUpperStarExtendScalarsIso, boundedConstructibleExtendScalarsCompatibility,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleExtendScalars_obj_obj]

lemma boundedConstructibleUpperStarExtendScalarsIso_inv_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((boundedConstructibleUpperStarExtendScalarsIso ℓ E f).inv.app K).hom =
      (derivedPullIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarExtendScalarsIso, boundedConstructibleExtendScalarsCompatibility,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleExtendScalars_obj_obj]

end Components

section OpenImmersion

variable (j : X ⟶ Y) [IsOpenImmersion j.left]

lemma boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E j).hom.app K).hom =
      (derivedOpenImmersionShriekIso (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        j.left).hom.app K.obj := by
  simp [boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso,
    boundedConstructibleExtendScalarsCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleExtendScalars_obj_obj, boundedConstructibleOpenImmersionLowerShriek_obj_obj]

lemma boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso_inv_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E j).inv.app K).hom =
      (derivedOpenImmersionShriekIso (padicIntegersRingObjToContinuousMapRingObj ℓ E)
        j.left).inv.app K.obj := by
  simp [boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso,
    boundedConstructibleExtendScalarsCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleExtendScalars_obj_obj, boundedConstructibleOpenImmersionLowerShriek_obj_obj]

end OpenImmersion

variable (k) in
/-- The extension of scalars `𝒪_E ⟶ E` as a coefficient change of the bounded constructible six
functors. -/
noncomputable def extendScalarsCoefficientChange :
    BoundedConstructibleCoefficientChange (Profinite.padicIntegersRingObj ℓ E.1)
      (Profinite.continuousMapRingObj E.1) ℓ k where
  T X _ _ _ := boundedConstructibleExtendScalars X.left ℓ E
  pull f := boundedConstructibleUpperStarExtendScalarsIso ℓ E f
  pull_comp f g := by
    intro K
    ext1
    have h := squareCompatible_leftDerivedUpperStarComp
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left g.left K.obj
    simp only [Functor.pasteSquareIso_hom_app] at h
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.pasteSquareIso_hom_app,
      boundedConstructibleUpperStarComp_hom_app_hom, boundedConstructibleUpperStar_map_hom,
      boundedConstructibleUpperStarExtendScalarsIso_hom_app_hom,
      boundedConstructibleExtendScalars_map_hom, boundedConstructibleExtendScalars_obj_obj,
      boundedConstructibleUpperStar_obj_obj, Over.comp_left]
    dsimp only [Functor.comp_obj] at h ⊢
    with_reducible exact h
  shriek j _ := boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E j
  isMateSquare_shriek_pull j _ := by
    intro K
    ext1
    have h := isMateSquare_derivedOpenImmersionShriekIso_derivedPullIso
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) j.left K.obj
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      boundedConstructibleUpperStarExtendScalarsIso_hom_app_hom,
      boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso_inv_app_hom,
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom,
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
      boundedConstructibleUpperStar_map_hom, boundedConstructibleExtendScalars_map_hom,
      boundedConstructibleExtendScalars_obj_obj, boundedConstructibleUpperStar_obj_obj,
      boundedConstructibleOpenImmersionLowerShriek_obj_obj]
    dsimp only [Functor.comp_obj] at h ⊢
    with_reducible exact h
  push p _ := boundedConstructibleLowerStarExtendScalarsIso ℓ E p
  isMateSquare_pull_push p _ := by
    rw [Adjunction.isMateSquare_iff]
    rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma extendScalarsCoefficientChange_T :
    (extendScalarsCoefficientChange ℓ E k).T Y = boundedConstructibleExtendScalars Y.left ℓ E :=
  rfl

lemma extendScalarsCoefficientChange_pull (f : X ⟶ Y) :
    (extendScalarsCoefficientChange ℓ E k).pull f = boundedConstructibleUpperStarExtendScalarsIso ℓ E f :=
  rfl

set_option maxRecDepth 8000 in
/-- (Shriek) along the chosen compactification is the comparison pasted from (Shriek) for the open
immersion and (Push) for the proper morphism of the coefficient change `𝒪_E ⟶ E`. -/
lemma boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification (f : X ⟶ Y) :
    boundedConstructibleLowerShriekExtendScalarsIso ℓ E f =
      (extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
        (compactificationOverField f) :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

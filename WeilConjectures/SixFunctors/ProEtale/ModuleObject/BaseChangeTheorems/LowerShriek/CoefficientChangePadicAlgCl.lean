/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.LiftSquareIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility

/-!
# The extension of scalars `E ⟶ ℚ̄_ℓ` as a coefficient change

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. This file shows that the
extension of scalars `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`, with the comparisons (Pull), (Shriek) and
(Push) of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility`, is
a coefficient change of the bounded constructible six functors
(`ProEtale.CondensedRing.toPadicAlgClCoefficientChange`). The required compatibilities are
restrictions of those on the ambient derived categories
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

lemma boundedConstructibleToPadicAlgCl_map_hom (X : Scheme.{u})
    {K L : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧} (φ : K ⟶ L) :
    ((boundedConstructibleToPadicAlgCl X ℓ E).map φ).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map φ.hom :=
  rfl

lemma boundedConstructibleToPadicAlgCl_obj_obj (X : Scheme.{u})
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleToPadicAlgCl X ℓ E).obj K).obj =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K.obj :=
  rfl

section Components

variable (f : X ⟶ Y)

lemma boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.app K).hom =
      (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left).hom.app K.obj := by
  simp [boundedConstructibleUpperStarToPadicAlgClIso, boundedConstructibleToPadicAlgClCompatibility,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleToPadicAlgCl_obj_obj]

lemma boundedConstructibleUpperStarToPadicAlgClIso_inv_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).inv.app K).hom =
      (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left).inv.app K.obj := by
  simp [boundedConstructibleUpperStarToPadicAlgClIso, boundedConstructibleToPadicAlgClCompatibility,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleToPadicAlgCl_obj_obj]

end Components

section OpenImmersion

variable (j : X ⟶ Y) [IsOpenImmersion j.left]

lemma boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).hom.app K).hom =
      (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        j.left).hom.app K.obj := by
  simp [boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso,
    boundedConstructibleToPadicAlgClCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleOpenImmersionLowerShriek_obj_obj]

lemma boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso_inv_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).inv.app K).hom =
      (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        j.left).inv.app K.obj := by
  simp [boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso,
    boundedConstructibleToPadicAlgClCompatibility,
    boundedConstructibleOpenImmersionLowerShriekCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleOpenImmersionLowerShriek_obj_obj]

end OpenImmersion

section Proper

variable (p : X ⟶ Y) [IsProper p.left]

lemma boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStarToPadicAlgClIso ℓ E p).hom.app K).hom =
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K.obj := by
  simp [boundedConstructibleLowerStarToPadicAlgClIso, boundedConstructibleToPadicAlgClCompatibility,
    boundedConstructibleLowerStarCompatibility,
    ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleLowerStar_obj_obj,
    ContinuousMapRingObj.boundedConstructibleLowerStar_obj_obj]

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing

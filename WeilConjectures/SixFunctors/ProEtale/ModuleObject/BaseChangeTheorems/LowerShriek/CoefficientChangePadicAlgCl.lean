/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClLowerStarHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility

/-!
# The extension of scalars `E ⟶ ℚ̄_ℓ` as a coefficient change

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. This file shows that the
extension of scalars `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`, with the comparisons (Pull), (Shriek) and
(Push) of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility`, is
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

section Components

variable (f : X ⟶ Y)

lemma boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.app K).hom =
      (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left).hom.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleToPadicAlgCl_obj_obj,
    boundedConstructibleUpperStar_obj_obj, boundedConstructibleUpperStarToPadicAlgClIso,
    Functor.whiskeringRight_obj_obj, boundedConstructibleToPadicAlgClCompatibility,
    ObjectProperty.liftCompιIso, boundedConstructibleUpperStarCompatibility,
    Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

lemma boundedConstructibleUpperStarToPadicAlgClIso_inv_app_hom
    (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).inv.app K).hom =
      (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left).inv.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleUpperStar_obj_obj,
    boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleUpperStarToPadicAlgClIso,
    Functor.whiskeringRight_obj_obj, boundedConstructibleToPadicAlgClCompatibility,
    ObjectProperty.liftCompιIso, boundedConstructibleUpperStarCompatibility,
    Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Iso.refl_hom, Category.assoc, Functor.isoWhiskerRight_inv, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

end Components

section OpenImmersion

variable (j : X ⟶ Y) [IsOpenImmersion j.left]

lemma boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).hom.app K).hom =
      (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        j.left).hom.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleToPadicAlgCl_obj_obj,
    boundedConstructibleOpenImmersionLowerShriek_obj_obj,
    boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso, Functor.whiskeringRight_obj_obj,
    boundedConstructibleToPadicAlgClCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleOpenImmersionLowerShriekCompatibility,
    Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

lemma boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso_inv_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).inv.app K).hom =
      (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        j.left).inv.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleOpenImmersionLowerShriek_obj_obj,
    boundedConstructibleToPadicAlgCl_obj_obj,
    boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso, Functor.whiskeringRight_obj_obj,
    boundedConstructibleToPadicAlgClCompatibility, ObjectProperty.liftCompιIso,
    boundedConstructibleOpenImmersionLowerShriekCompatibility,
    Functor.FullyFaithful.preimageIso_inv, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Iso.refl_hom, Category.assoc, Functor.isoWhiskerRight_inv, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing

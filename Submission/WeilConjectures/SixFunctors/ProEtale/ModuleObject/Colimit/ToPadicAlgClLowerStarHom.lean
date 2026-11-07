/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The extension of scalars `E ⟶ ℚ̄_ℓ` and the proper direct image on underlying complexes

The comparison `boundedConstructibleLowerStarToPadicAlgClIso` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility`, computed
on the underlying complexes (`boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom`).
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

section Proper

variable (p : X ⟶ Y) [IsProper p.left]

lemma boundedConstructibleLowerStarToPadicAlgClIso_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStarToPadicAlgClIso ℓ E p).hom.app K).hom =
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p.left).app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleToPadicAlgCl_obj_obj,
    ContinuousMapRingObj.boundedConstructibleLowerStar_obj_obj,
    boundedConstructibleLowerStar_obj_obj, boundedConstructibleLowerStarToPadicAlgClIso,
    Functor.whiskeringRight_obj_obj, boundedConstructibleToPadicAlgClCompatibility,
    ObjectProperty.liftCompιIso, ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility,
    boundedConstructibleLowerStarCompatibility, Functor.FullyFaithful.preimageIso_hom,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, asIso_hom, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing

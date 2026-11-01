/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingIntrinsicRestrictionUnit

/-! # Coherence of finite-coefficient realization restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fd_ordinaryRestrictionUnit (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    (ProEtale.pbcComparisonRestrict T (RingHom.id R)).inv =
      Functor.whiskerRight
        (ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl).hom
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).leftUnitor.hom ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).rightUnitor.inv ≫
      Functor.whiskerLeft (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T)
        (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology T)
          (RingHom.id R) rfl).inv := by
  let a := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) T
  let b := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology (RingHom.id R)
  let c := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) (RingHom.id R)
  change (conjugateEquiv (a.comp c) (b.comp a)).symm (𝟙 _) = _
  apply (conjugateEquiv (a.comp c) (b.comp a)).injective
  rw [Equiv.apply_symm_apply]
  symm
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _ a]
  rw [← conjugateEquiv_comp _ (a.comp Adjunction.id)]
  rw [← conjugateEquiv_comp _ (Adjunction.id.comp a)]
  rw [conjugateEquiv_whiskerLeft c Adjunction.id a,
    conjugateEquiv_whiskerRight Adjunction.id b a,
    conjugateEquiv_leftUnitor_hom a]
  have hr : conjugateEquiv (a.comp Adjunction.id) a
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).rightUnitor.inv =
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) T).leftUnitor.hom := by
    ext X
    simp
  rw [hr]
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.assoc]
  dsimp only [b, c, ProEtale.normalizedOriginRestrictionUnit,
    Sheaf.restrictCoextendScalarsAdj]
  simp only [Functor.comp_obj, sheafCompose_obj_obj, Functor.id_obj,
    conjugateEquiv_apply_app, Adjunction.id_unit, NatTrans.id_app, Functor.id_map,
    Category.id_comp, Functor.map_comp, Adjunction.id_counit, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    sheafCompose_map_hom, NatTrans.comp_app, Functor.whiskerRight_app, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, ObjectProperty.FullSubcategory.id_hom,
    ModuleCat.hom_id]
  rename_i U x
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro r
  let M := ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) T).obj X).obj.obj U
  let z : (ModuleCat.coextendScalars (RingHom.id R)).obj M := x
  change r • (ModuleCat.CoextendScalars.equiv (RingHom.id R) M z) (1 : R) =
    (ModuleCat.CoextendScalars.equiv (RingHom.id R) M z) r
  have h := (ModuleCat.CoextendScalars.equiv (RingHom.id R) M z).map_smul r (1 : R)
  simpa [ModuleCat.restrictScalars.smul_def, mul_one] using h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fd_derivedRestrictionUnit (T : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] :
    (ProEtale.pbcDerivedComparisonRestrict T (RingHom.id R)).inv =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ≫
      Functor.whiskerLeft
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology T)
            (RingHom.id R) rfl) ≪≫ Functor.mapDerivedCategoryIdIso _).inv := by
  have ho (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      (ProEtale.pbcComparisonRestrict T (RingHom.id R)).hom.app X ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).map
          ((ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology
            (RingHom.id R) rfl).hom.app X) =
      (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology T)
        (RingHom.id R) rfl).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).obj X) := by
    apply (cancel_epi ((ProEtale.pbcComparisonRestrict T (RingHom.id R)).inv.app X)).1
    rw [Iso.inv_hom_id_app_assoc, fd_ordinaryRestrictionUnit]
    simp
  ext K
  have h := Functor.mapDerivedCategorySquareIso_hom_app_id
    (ProEtale.pbcComparisonRestrict T (RingHom.id R))
    (ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl)
    (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology T)
      (RingHom.id R) rfl) ho K
  change (ProEtale.pbcDerivedComparisonRestrict T (RingHom.id R)).hom.app K ≫ _ = _ at h
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply (cancel_epi ((ProEtale.pbcDerivedComparisonRestrict T (RingHom.id R)).hom.app K)).1
  rw [Iso.hom_inv_id_app]
  rw [← Category.assoc, h, Iso.hom_inv_id_app]
  rfl

private theorem fd_derivedRestrictionUnit' (T : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    (ProEtale.pbcDerivedComparisonRestrict T φ).inv =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit T.smallEtaleTopology φ hφ) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ≫
      Functor.whiskerLeft
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit (Scheme.ProEt.topology T) φ hφ) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv := by
  subst φ
  exact fd_derivedRestrictionUnit T R

/-- Realization identifies the canonical identity restriction maps.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
the identity part of lem-coef-dualizing-scalar-realization, proof step 1
(blueprint: lem-coef-dualizing-realization-restriction-unit).

Proof: before deriving, the intrinsic comparison is fixed by its value on the
scalar-unit sections. For the identity ring map both paths act identically on
every such section, so the uniqueness in finiteDualizingRestriction_existsUnique
identifies them. The comparison-site restriction square has the same identity
normalization. Apply exact localization to these two commuting squares. The
identity constraint of mapDerivedCategory identifies localization of the ordinary
identity with normalizedDVRResUnit. Pasting the two localized squares gives the
displayed equality. This includes n = 0 (the first positive quotient), and the
identity ring or sheaf on the empty scheme requires no separate assumption. -/
theorem finiteDualizingRealizationRestriction_unit (n : ℕ)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X) :
    (finiteDualizingRealizationRestriction l E X (le_refl n)).inv.app K ≫
        (normalizedDVRResUnit l E X n).hom.app
          ((finiteDualizingRealization l E X n).obj K) =
      (finiteDualizingRealization l E X n).map
        ((Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit X.smallEtaleTopology _
            (finiteDualizingQuotient_id l E n)) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K) := by
  unfold finiteDualizingRealizationRestriction finiteDualizingRealization
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [fd_derivedRestrictionUnit' X _ _ (finiteDualizingQuotient_id l E n)]
  let U := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).mapDerivedCategory
  have hi := congrArg (fun e => e.hom.app (U.obj K))
    (finiteDualizingIntrinsicRestriction_unit l E X n)
  dsimp at hi
  simp only [Functor.comp_obj, Functor.id_obj, Functor.associator_inv_app, Iso.trans_hom,
    Functor.whiskerRight_comp, Iso.trans_inv, Functor.whiskerLeft_comp, Category.assoc,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.id_comp, Functor.associator_hom_app, Category.comp_id,
    Functor.comp_map]
  have hi' := hi
  simp only [Category.comp_id] at hi'
  rw [hi']
  simp only [Functor.map_comp]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  simp

end WeilConjectures

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Identity open normalization and scalar restriction

Source: Stacks Tags 03DI and 03CY; the finite proper-normalization proof, step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open CategoryTheory.Functor Opposite

attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction

private theorem inverse_realization_counit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (e : C ≌ D) (f : E ≌ F) (R : E ⥤ C) (S : F ⥤ D)
    (a : f.functor ⋙ S ≅ R ⋙ e.functor) (M : F) :
    e.functor.map
        (e.inverse.map (S.map (f.counitIso.inv.app M)) ≫
          e.inverse.map (a.hom.app (f.inverse.obj M)) ≫
          e.unitIso.inv.app (R.obj (f.inverse.obj M))) ≫
      a.inv.app (f.inverse.obj M) ≫ S.map (f.counitIso.hom.app M) =
    e.counitIso.hom.app (S.obj M) := by
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
  rw [← e.counit_app_functor]
  rw [e.counit_naturality_assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [e.counit_naturality_assoc, ← S.map_comp, Iso.inv_hom_id_app, S.map_id,
    Category.comp_id]
  rfl

private theorem transported_identity_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (e : C ≌ D) (f : E ≌ F) (R : E ⥤ C) (S : F ⥤ D)
    (α : f.functor ⋙ S ≅ R ⋙ e.functor)
    (β : S ⋙ e.inverse ≅ f.inverse ⋙ R)
    (J : C ⥤ C) (K : E ⥤ E) (q : R ⋙ J ≅ K ⋙ R)
    (a : J ≅ 𝟭 C) (b : K ≅ 𝟭 E)
    (hq : ∀ N, q.hom.app N ≫ R.map (b.hom.app N) = a.hom.app (R.obj N))
    (hc : ∀ M, e.functor.map (β.hom.app M) ≫
      α.inv.app (f.inverse.obj M) ≫ S.map (f.counitIso.hom.app M) =
      e.counitIso.hom.app (S.obj M)) (M : F) :
    (isoWhiskerRight β (J ⋙ e.functor) ≪≫
      isoWhiskerLeft f.inverse (isoWhiskerRight q e.functor) ≪≫
      isoWhiskerLeft (f.inverse ⋙ K) α.symm).hom.app M ≫
      S.map ((isoWhiskerLeft f.inverse (isoWhiskerRight b f.functor) ≪≫
        f.counitIso).hom.app M) =
    (isoWhiskerLeft e.inverse (isoWhiskerRight a e.functor) ≪≫ e.counitIso).hom.app
      (S.obj M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  have hn := α.inv.naturality (b.hom.app (f.inverse.obj M))
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  slice_lhs 2 3 => rw [← e.functor.map_comp, hq]
  slice_lhs 1 2 => rw [← e.functor.map_comp, a.hom.naturality]
  simp only [Functor.id_map, Functor.map_comp, Category.assoc]
  rw [hc]

private noncomputable def fixedRestrictionId (X : Scheme.{u})
    (R : Type u) [CommRing R] :
    ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} R))
      (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) X) _ _

private theorem fixedRestrictionId_unit (X : Scheme.{u})
    (R : Type u) [CommRing R]
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) :
    (ProEtale.openImmersionRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)).unit.app M ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)).map
          ((fixedRestrictionId X R).hom.app M) =
      (ProEtale.lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).inv.app M := by
  apply (sheafToPresheaf _ _).map_injective
  apply NatTrans.ext
  funext V
  erw [ProEtale.lowerStarId_inv_app_hom_app]
  change M.obj.map _ ≫ M.obj.map _ = M.obj.map _
  rw [← M.obj.map_comp]
  congr 1

private theorem fixedUpperStarId (X : Scheme.{u})
    (R : Type u) [CommRing R] :
    ProEtale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X) ≪≫ fixedRestrictionId X R =
      ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id (ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X))).injective
  rw [ProEtale.conjugateEquiv_upperStarId_hom]
  apply conjugateEquiv_eq_of_unit
  intro M
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X))
    (ProEtale.openImmersionRestrictionLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, ← Category.assoc]
  change (ProEtale.lowerStarId _ X).inv.app M = _
  change (ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)).unit.app M ≫
      (ProEtale.lowerStar _ (𝟙 X)).map
        ((ProEtale.upperStarIsoOpenImmersionRestriction _ (𝟙 X)).hom.app M) = _ at h
  rw [h]
  exact (fixedRestrictionId_unit X R M).symm

private noncomputable def intrinsicRestrictionId (X : Scheme.{u})
    (R : Type u) [CommRing R] [Finite R] :
    sfIntrinsicOpenRestriction (𝟙 X) R ≅ 𝟭 _ :=
  isoWhiskerLeft (sfIntrinsicModuleEquivalence X R).inverse
    (isoWhiskerRight (fixedRestrictionId X R) (sfIntrinsicModuleEquivalence X R).functor) ≪≫
      (sfIntrinsicModuleEquivalence X R).counitIso

private theorem intrinsic_identity_unit (X : Scheme.{u})
    (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleRingModules X (proEtaleConstantRing X R)) :
    (sfIntrinsicExtensionByZeroAdjunction (𝟙 X) R).unit.app M ≫
        (intrinsicRestrictionId X R).hom.app ((sfIntrinsicExtensionByZero (𝟙 X) R).obj M) ≫
        (sfIntrinsicOpenId R X).hom.app M = 𝟙 M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((sfIntrinsicOpenAdjunction R (𝟙 X)).ofNatIsoRight (sfIntrinsicPullbackId R X))
    Adjunction.id M
  change (sfIntrinsicOpenAdjunction R (𝟙 X)).unit.app M ≫
    (sfIntrinsicPullbackId R X).hom.app ((sfIntrinsicExtensionByZero (𝟙 X) R).obj M) ≫
    (sfIntrinsicOpenId R X).hom.app M = 𝟙 M at h
  have hu :
      (sfIntrinsicExtensionByZeroAdjunction (𝟙 X) R).unit.app M ≫
        (intrinsicRestrictionId X R).hom.app ((sfIntrinsicExtensionByZero (𝟙 X) R).obj M) =
      (sfIntrinsicOpenAdjunction R (𝟙 X)).unit.app M ≫
        (sfIntrinsicPullbackId R X).hom.app
          ((sfIntrinsicExtensionByZero (𝟙 X) R).obj M) := by
    simp only [sfIntrinsicOpenAdjunction, sfIntrinsicExtensionByZeroAdjunction,
      Adjunction.comp_unit_app, sfIntrinsicPullbackId, sfIntrinsicTransportIso,
      intrinsicRestrictionId, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
    simp only [ProEtale.openImmersionLowerShriekUpperStarAdjunction,
      ProEtale.localizationLowerShriekUpperStarAdjunction, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app, whiskerLeft_app, Iso.symm_hom,
      Functor.comp_map, Functor.map_comp, Category.assoc]
    simp only [Equivalence.symm_inverse, Equivalence.symm_functor]
    have hn := (ProEtale.upperStarIsoOpenImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)).inv.naturality
      ((sfIntrinsicModuleEquivalence X R).toAdjunction.unit.app
        (((sfIntrinsicModuleEquivalence X R).symm.functor ⋙
          ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)).obj M))
    have ht (N : Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) :
        (ProEtale.upperStarIsoOpenImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) (𝟙 X)).inv.app N ≫
          (ProEtale.upperStarId _ X).hom.app N = (fixedRestrictionId X R).hom.app N := by
      rw [← fixedUpperStarId]
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.inv_hom_id_app_assoc]
    dsimp only [ProEtale.upperStarIsoOpenImmersionRestriction, Functor.id_obj,
      Functor.comp_obj, Equivalence.symm_functor] at hn
    dsimp only [ProEtale.upperStarIsoOpenImmersionRestriction] at ht
    dsimp only [sfIntrinsicExtensionByZero, Functor.comp_obj]
    slice_rhs 3 4 =>
      rw [← (sfIntrinsicModuleEquivalence X R).functor.map_comp, ← hn,
        (sfIntrinsicModuleEquivalence X R).functor.map_comp]
    slice_rhs 4 5 =>
      rw [← (sfIntrinsicModuleEquivalence X R).functor.map_comp]
      erw [ht]
    unfold ProEtale.openImmersionLowerShriekAdjunction
    rfl
  rw [← Category.assoc, hu, Category.assoc]
  exact h

private theorem intrinsic_restriction_square
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    (sfOpenRestrictionCoefficientSquare (𝟙 X) φ).hom.app M ≫
        (proEtaleCoefficientRestrictScalars X φ).map
          ((intrinsicRestrictionId X B).hom.app M) =
      (intrinsicRestrictionId X A).hom.app
        ((proEtaleCoefficientRestrictScalars X φ).obj M) := by
  apply transported_identity_square (sfIntrinsicModuleEquivalence X A)
    (sfIntrinsicModuleEquivalence X B) (sfFixedRestriction X φ)
    (proEtaleCoefficientRestrictScalars X φ) (sfRealizationRestriction X φ)
    (sfInverseRealizationRestriction X φ)
    (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (𝟙 X))
    (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) (𝟙 X))
    (Iso.refl _) (fixedRestrictionId X A) (fixedRestrictionId X B)
  · intro N
    ext V x
    rfl
  · intro N
    exact inverse_realization_counit (sfIntrinsicModuleEquivalence X A)
      (sfIntrinsicModuleEquivalence X B) (sfFixedRestriction X φ)
      (proEtaleCoefficientRestrictScalars X φ) (sfRealizationRestriction X φ) N

private theorem sheaf_identity
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    (sfOpenRestriction (𝟙 X) φ).hom.app M ≫
        (proEtaleCoefficientRestrictScalars X φ).map
          ((sfIntrinsicOpenId B X).hom.app M) =
      (sfIntrinsicOpenId A X).hom.app
        ((proEtaleCoefficientRestrictScalars X φ).obj M) := by
  apply ((sfIntrinsicExtensionByZeroAdjunction (𝟙 X) A).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono ((intrinsicRestrictionId X A).hom.app
    ((proEtaleCoefficientRestrictScalars X φ).obj M))).mp
  have hn := (intrinsicRestrictionId X A).hom.naturality
    ((proEtaleCoefficientRestrictScalars X φ).map ((sfIntrinsicOpenId B X).hom.app M))
  have hn' := (intrinsicRestrictionId X A).hom.naturality
    ((sfIntrinsicOpenId A X).hom.app
      ((proEtaleCoefficientRestrictScalars X φ).obj M))
  dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hn hn'
  simp only [Category.assoc]
  rw [hn, hn']
  rw [intrinsic_identity_unit]
  rw [← intrinsic_restriction_square X φ
    ((sfIntrinsicExtensionByZero (𝟙 X) B).obj M)]
  slice_lhs 1 3 => exact (sfOpenRestriction_normalized_unique (𝟙 X) φ).1 M
  rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, intrinsic_identity_unit]
  exact CategoryTheory.Functor.map_id _ _

/-- The canonical identity-open identification respects the prescribed coefficient square.
Source: Stacks Tags 03DI and 03CY; blueprint proper-coincidence proof, first paragraph,
expanded in the proof of lem-weil-proper-finite-normalization, step 4
(blueprint: lem-weil-identity-open-scalar-restriction).

Proof: before sheafification, extension by zero along the identity has every site object
as a nonzero summand. The canonical identity-open identification is the unique extension
of the identity on this presheaf, characterized by the unit of the open adjunction.
The published open scalar comparison has the same normalization, by
sfOpenRestriction_normalized_unique. Consequently its composite with restriction of
the identity-open identification over B equals the identity-open identification over A
at the restricted sheaf. Apply this equality termwise to cochain complexes and descend
through quasi-isomorphisms. The composition and identity comparisons of exact derived
functors identify the resulting maps with precisely the displayed transformations. -/
theorem sfIdentityOpenRestriction
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) :
    Functor.whiskerLeft (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory
        (sfIntrinsicDerivedOpenId A X).hom =
      (sfOpenRestrictionDerived (𝟙 X) φ).hom ≫
        Functor.whiskerRight (sfIntrinsicDerivedOpenId B X).hom
          (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory := by
  apply NatTrans.ext
  funext K
  have h := Functor.mapDerivedCategorySquareIso_hom_app_id
    (sfOpenRestriction (𝟙 X) φ)
    (sfIntrinsicOpenId B X) (sfIntrinsicOpenId A X)
    (fun M ↦ sheaf_identity X φ M) K
  simpa only [sfIntrinsicDerivedOpenId, sfOpenRestrictionDerived, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] using h.symm

end AlgebraicGeometry.Scheme

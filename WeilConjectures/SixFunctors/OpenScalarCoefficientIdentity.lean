/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarTensorData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! The identity field for scalar pullback coefficient coherence.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6.
(blueprint: lem-sp-open-scalar-coefficient-coherence-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

set_option synthInstance.maxSize 4096

private theorem ordinaryIdentity
    {U X : Scheme.{u}} (j : U ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (comm : c.hom ≫ 𝟙 S =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map (𝟙 R) ≫ c.hom) :
    proEtaleRingRestrictionPullbackInv j R R S S (𝟙 R) (𝟙 S) c c comm =
      𝟙 (proEtaleRingModulePullback j R S c) := by
  have h (N : proEtaleRingModules U S) :
      (proEtaleRingRestrictionDirectImage j R R S S (𝟙 R) (𝟙 S) c c comm).hom.app N =
        𝟙 ((proEtaleRingModuleDirectImage j R S c).obj N) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext n
    exact (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
      j R R S S (𝟙 R) (𝟙 S) c c comm)).1 N W n
  apply NatTrans.ext
  funext N
  change (proEtaleRingRestrictionPullbackApp j R R S S (𝟙 R) (𝟙 S) c c comm N) = 𝟙 _
  unfold proEtaleRingRestrictionPullbackApp
  rw [h]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (proEtaleRingModuleAdjunction j R S c).left_triangle_components N

-- Keep the chosen pullback intact during the formal comparison calculations.
attribute [local irreducible] proEtaleRingModulePullback

private theorem derivedIdentitySquare
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) (R : C ⥤ C) (S : D ⥤ D)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ≅ 𝟭 C) (f : S ≅ 𝟭 D) (q : R ⋙ P ≅ P ⋙ S)
    (hq : ∀ M, q.hom.app M ≫ f.hom.app (P.obj M) = P.map (e.hom.app M))
    (N : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso q).hom.app N ≫
        (Functor.mapDerivedCategoryNatIso f ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (P.mapDerivedCategory.obj N) =
      P.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
          N) := by
  have heq : q ≪≫ Functor.isoWhiskerLeft P f ≪≫ Functor.rightUnitor P =
      Functor.isoWhiskerRight e P ≪≫ Functor.leftUnitor P := by
    apply Iso.ext
    ext M
    change q.hom.app M ≫ f.hom.app (P.obj M) ≫ 𝟙 _ = P.map (e.hom.app M) ≫ 𝟙 _
    simpa only [Category.comp_id] using hq M
  have hiL : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor P)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hiR : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor P)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app N) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app,
    hiL, hiR, Category.comp_id] at hd
  have hnR := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e P) N
  have hnL := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft P f) N
  have huL := congr_app (Functor.mapDerivedCategoryCompIso_id_comp P) N
  have huR := congr_app (Functor.mapDerivedCategoryCompIso_comp_id P) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hnR hnL huL huR
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R P).hom.app N)).1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, ← reassoc_of% hnL, huR]
  erw [Category.comp_id]
  rw [hd, ← reassoc_of% hnR, huL]
  erw [Category.comp_id]

private theorem normalizedId_unit
    {C : Type*} [Category C] {S R : C ⥤ C} (a : S ⊣ R) (e : R ≅ 𝟭 C) (N : C) :
    a.unit.app N ≫ R.map
        (((a.ofNatIsoRight e).leftAdjointUniq Adjunction.id).hom.app N) =
      e.inv.app N := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (a.ofNatIsoRight e) Adjunction.id N
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj] at h
  apply (cancel_mono (e.hom.app N)).1
  rw [Iso.inv_hom_id_app]
  exact h

-- Naming the component equation prevents transport from normalizing localization data.
private def identitySquare
    {C D : Type*} [Category C] [Category D] {R : C ⥤ C} {S : D ⥤ D}
    (P : C ⥤ D) (e : R ≅ 𝟭 C) (f : S ≅ 𝟭 D)
    (q : R ⋙ P ⟶ P ⋙ S) (N : C) : Prop :=
  q.app N ≫ f.hom.app (P.obj N) = P.map (e.hom.app N)

private theorem identityMate
    {C D : Type*} [Category C] [Category D]
    {S R : C ⥤ C} {T V : D ⥤ D} (a : S ⊣ R) (b : T ⊣ V)
    (e : R ≅ 𝟭 C) (f : V ≅ 𝟭 D) (P : C ⥤ D)
    (q : R ⋙ P ⟶ P ⋙ V)
    (hq : ∀ N, identitySquare P e f q N) (N : C) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ q)).natTrans.app N ≫
        P.map (((a.ofNatIsoRight e).leftAdjointUniq Adjunction.id).hom.app N) =
      ((b.ofNatIsoRight f).leftAdjointUniq Adjunction.id).hom.app (P.obj N) := by
  change ∀ N, q.app N ≫ f.hom.app (P.obj N) = P.map (e.hom.app N) at hq
  let l := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ q)).natTrans
  let i := ((a.ofNatIsoRight e).leftAdjointUniq Adjunction.id).hom
  let k := ((b.ofNatIsoRight f).leftAdjointUniq Adjunction.id).hom
  change l.app N ≫ P.map (i.app N) = k.app (P.obj N)
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hm := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ q) N
  change P.map (a.unit.app N) ≫ q.app (S.obj N) =
    b.unit.app (P.obj N) ≫ V.map (l.app N) at hm
  rw [← Category.assoc, ← hm, Category.assoc]
  have hn := q.naturality (i.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← P.map_comp_assoc, normalizedId_unit a e N]
  rw [normalizedId_unit b f (P.obj N)]
  apply (cancel_mono (f.hom.app (P.obj N))).1
  dsimp only [Functor.id_obj]
  rw [Category.assoc, hq N, ← P.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Iso.inv_hom_id_app]
  rfl

private theorem normalizedId_transport
    {C : Type*} [Category C] {α : Sort*} (S R : α → C ⥤ C)
    (a : ∀ x, S x ⊣ R x) {x y : α} (h : x = y) (e : R y ≅ 𝟭 C) :
    eqToIso (congrArg S h) ≪≫ ((a y).ofNatIsoRight e).leftAdjointUniq Adjunction.id =
      ((a x).ofNatIsoRight (eqToIso (congrArg R h) ≪≫ e)).leftAdjointUniq
        Adjunction.id := by
  subst y
  simp only [eqToIso_refl, Iso.refl_trans]

private def restrictionId (A : Type u) [CommRing A] (T : Scheme.{u}) :
    scalarRestriction (RingHom.id A) T ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  eqToIso (congrArg (fun a ↦ (proEtaleRingRestrictScalars a).mapDerivedCategory)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))) ≪≫
    scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} (proEtaleConstantRing T A)

private theorem scalarId_normalized (m : Models.{u}) (A : Type u) [CommRing A]
    (T : Scheme.{u}) :
    scalarId m A T =
      ((scalarPair m (RingHom.id A) T).adjunction.ofNatIsoRight
        (restrictionId A T)).leftAdjointUniq Adjunction.id := by
  rw [scalarId_eq]
  exact normalizedId_transport
    (fun a ↦ ((m T).scalar a).derived) (fun a ↦ scalarDerivedRestriction.{u + 1, u, u + 1, u + 2} a)
    (fun a ↦ ((m T).scalar a).adjunction)
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A)))
    (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} (proEtaleConstantRing T A))

private theorem scalarId_comparison (m : Models.{u}) (A : Type u) [CommRing A]
    (T : Scheme.{u}) (N : proEtaleDerivedCategory T A) :
    (scalarId m A T).hom.app N = (scalarIso m (RingHom.id A) T).hom.app N ≫
      (((proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) (RingHom.id A))).ofNatIsoRight
          (restrictionId A T)).leftAdjointUniq Adjunction.id).hom.app N := by
  let a := (scalarPair m (RingHom.id A) T).adjunction
  let b := proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) (RingHom.id A))
  apply (a.homEquiv _ _).injective
  rw [scalarId_normalized]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [normalizedId_unit]
  change (restrictionId A T).inv.app N =
    a.unit.app N ≫ (scalarDerivedRestriction.{u + 1, u, u + 1, u + 2}
      (proEtaleConstantRingMap (T := T) (RingHom.id A))).map
        ((a.leftAdjointUniq b).hom.app N) ≫ _
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  exact (normalizedId_unit b (restrictionId A T) N).symm

private theorem ordinaryIdentityNormalized
    {U X : Scheme.{u}} (j : U ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (comm : c.hom ≫ 𝟙 S =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map (𝟙 R) ≫ c.hom)
    (M : proEtaleRingModules X R) :
    (proEtaleRingRestrictionPullbackInv j R R S S (𝟙 R) (𝟙 S) c c comm).app M ≫
      (scalarHomOrdinaryRestrictionId.{u + 1, u, u + 1} S).hom.app
        ((proEtaleRingModulePullback j R S c).obj M) =
      (proEtaleRingModulePullback j R S c).map
        ((scalarHomOrdinaryRestrictionId.{u + 1, u, u + 1} R).hom.app M) := by
  change (proEtaleRingRestrictionPullbackInv j R R S S (𝟙 R) (𝟙 S) c c comm).app M ≫
    𝟙 _ = (proEtaleRingModulePullback j R S c).map (𝟙 M)
  have hOrd := congr_app (ordinaryIdentity j R S c comm) M
  change (proEtaleRingRestrictionPullbackInv j R R S S (𝟙 R) (𝟙 S) c c comm).app M =
    𝟙 ((proEtaleRingModulePullback j R S c).obj M) at hOrd
  rw [hOrd]
  erw [Category.comp_id, CategoryTheory.Functor.map_id]

private theorem restrictionIdentitySquare_id
    {U X : Scheme.{u}} (j : U ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (comm₀ : c.hom ≫ 𝟙 S =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map (𝟙 R) ≫ c.hom)
    (N : DerivedCategory (proEtaleRingModules X R)) :
    identitySquare (proEtaleRingDerivedPullback j R S c)
      (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} R)
      (scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} S)
      (proEtaleRingRestrictionDerivedPullback j R R S S (𝟙 R) (𝟙 S) c c comm₀).inv N := by
  unfold identitySquare
  let := proEtaleRingRestrictionPullbackInv_isIso j R R S S (𝟙 R) (𝟙 S) c c comm₀
  let q := asIso (proEtaleRingRestrictionPullbackInv j R R S S (𝟙 R) (𝟙 S) c c comm₀)
  have hq (M : proEtaleRingModules X R) := ordinaryIdentityNormalized j R S c comm₀ M
  have h := derivedIdentitySquare (proEtaleRingModulePullback j R S c)
    (proEtaleRingRestrictScalars (𝟙 R)) (proEtaleRingRestrictScalars (𝟙 S))
    (scalarHomOrdinaryRestrictionId.{u + 1, u, u + 1} R)
    (scalarHomOrdinaryRestrictionId.{u + 1, u, u + 1} S) q hq N
  have he (z : proEtaleRingRestrictScalars (𝟙 R) ⋙ proEtaleRingModulePullback j R S c ≅
      proEtaleRingModulePullback j R S c ⋙ proEtaleRingRestrictScalars (𝟙 S)) :
      (Functor.mapDerivedCategoryNatIso z.symm).inv =
        (Functor.mapDerivedCategoryNatIso z).hom := by
    simpa only [Iso.symm_symm_eq] using (Functor.mapDerivedCategoryNatIso_symm z.symm).symm
  simpa only [proEtaleRingRestrictionDerivedPullback,
    Functor.mapDerivedCategorySquareIso, q, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, he,
    scalarHomRestrictionId, Category.assoc] using h

private theorem restrictionIdentityTransport_refl
    {X : Scheme.{u}} (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    eqToIso (congrArg
        (fun a : R ⟶ R ↦ (proEtaleRingRestrictScalars a).mapDerivedCategory)
        (rfl : (𝟙 R) = (𝟙 R))) ≪≫
      scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} R =
        scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} R := by
  exact Iso.refl_trans _

-- This predicate is the motive for elimination of the two ring-map equalities.
private def restrictionIdentityProperty
    {U X : Scheme.{u}} (j : U ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (a : R ⟶ R) (b : S ⟶ S) (ha : a = 𝟙 R) (hb : b = 𝟙 S)
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (comm : c.hom ≫ b =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map a ≫ c.hom)
    (N : DerivedCategory (proEtaleRingModules X R)) : Prop :=
  identitySquare (proEtaleRingDerivedPullback j R S c)
    (eqToIso (congrArg (fun a ↦ (proEtaleRingRestrictScalars a).mapDerivedCategory) ha) ≪≫
      scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} R)
    (eqToIso (congrArg (fun b ↦ (proEtaleRingRestrictScalars b).mapDerivedCategory) hb) ≪≫
      scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} S)
    (proEtaleRingRestrictionDerivedPullback j R R S S a b c c comm).inv N

private theorem restrictionIdentityProperty_refl
    {U X : Scheme.{u}} (j : U ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (comm : c.hom ≫ 𝟙 S =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map (𝟙 R) ≫ c.hom)
    (N : DerivedCategory (proEtaleRingModules X R)) :
    restrictionIdentityProperty j R S (𝟙 R) (𝟙 S) rfl rfl c comm N := by
  unfold restrictionIdentityProperty
  rw [restrictionIdentityTransport_refl R, restrictionIdentityTransport_refl S]
  exact restrictionIdentitySquare_id j R S c comm N

private theorem restrictionIdentitySquare
    {U X : Scheme.{u}} (j : U ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (a : R ⟶ R) (b : S ⟶ S) (ha : a = 𝟙 R) (hb : b = 𝟙 S)
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)
    (comm : c.hom ≫ b =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map a ≫ c.hom)
    (N : DerivedCategory (proEtaleRingModules X R)) :
    restrictionIdentityProperty j R S a b ha hb c comm N := by
  subst a
  subst b
  exact restrictionIdentityProperty_refl j R S c comm N

private theorem restrictionId_square (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) (N : proEtaleDerivedCategory X A) :
    identitySquare (constantPullback (A := A) j) (restrictionId A X) (restrictionId A U)
      (rightSquare (RingHom.id A) j).inv N := by
  let aX := proEtaleConstantRingMap (T := X) (RingHom.id A)
  let aU := proEtaleConstantRingMap (T := U) (RingHom.id A)
  let c := proEtaleConstantRingComparison j A
  have haX : aX = 𝟙 (proEtaleConstantRing X A) :=
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A))
  have haU : aU = 𝟙 (proEtaleConstantRing U A) :=
    (constantSheaf (Scheme.ProEt.topology U) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1, u} A))
  have comm : c.hom ≫ aU =
      (proEtaleSheafInverseImage j CommRingCat.{u + 1}).map aX ≫ c.hom := by
    simpa [c, aU, aX, proEtaleConstantRingComparison, proEtaleConstantRingMap] using
      (proEtaleConstantInverseImageMap_naturality j
        (a := CommRingCat.ofHom (RingHom.ulift (RingHom.id A)))).symm
  have hSquare : rightSquare (RingHom.id A) j =
      proEtaleRingRestrictionDerivedPullback j
        (proEtaleConstantRing X A) (proEtaleConstantRing X A)
        (proEtaleConstantRing U A) (proEtaleConstantRing U A) aX aU c c comm := rfl
  have hX : restrictionId A X =
      eqToIso (congrArg (fun a ↦ (proEtaleRingRestrictScalars a).mapDerivedCategory) haX) ≪≫
        scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} (proEtaleConstantRing X A) := rfl
  have hU : restrictionId A U =
      eqToIso (congrArg (fun a ↦ (proEtaleRingRestrictScalars a).mapDerivedCategory) haU) ≪≫
        scalarHomRestrictionId.{u + 1, u, u + 1, u + 2} (proEtaleConstantRing U A) := rfl
  rw [hSquare, hX, hU]
  exact restrictionIdentitySquare j (proEtaleConstantRing X A) (proEtaleConstantRing U A)
    aX aU haX haU c comm N

/-- Scalar pullback commutes with the recorded identity coefficient unitor.
Source: Stacks 07A4 and 07A6.
(blueprint: lem-sp-open-scalar-coefficient-coherence-identity).

Proof: the ordinary restriction comparison for the identity coefficient map is
identity on sections, so the adjunction triangle identifies its pullback mate.
The exact-derived unit and whiskering laws give the corresponding normalized
restriction square. The unit equation and injectivity of the scalar adjunction's
Hom equivalence identify its left mate with the scalar identity. Finally, the
unit-normalized presentation comparison `scalarIso` transports this equation to
`m`; its inverse cancels in the definition of `lambda`.
-/
theorem scalar_pullback_coefficient_identity (m : Models.{u})
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X)
    (Q : proEtaleDerivedCategory X A) :
    (lambda m (RingHom.id A) j).inv.app Q ≫
        (constantPullback (A := A) j).map ((scalarId m A X).hom.app Q) =
      (scalarId m A U).hom.app ((constantPullback (A := A) j).obj Q) := by
  rw [scalarId_comparison m A X Q,
    scalarId_comparison m A U ((constantPullback (A := A) j).obj Q)]
  simp only [lambda, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← (constantPullback (A := A) j).map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have h := identityMate
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) (RingHom.id A)))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := U) (RingHom.id A)))
    (restrictionId A X) (restrictionId A U) (constantPullback (A := A) j)
    (rightSquare (RingHom.id A) j).inv (restrictionId_square A j) Q
  exact congrArg (fun f ↦ (scalarIso m (RingHom.id A) U).hom.app
    ((constantPullback (A := A) j).obj Q) ≫ f) h

end AlgebraicGeometry.ProEtale.OpenScalarTensor

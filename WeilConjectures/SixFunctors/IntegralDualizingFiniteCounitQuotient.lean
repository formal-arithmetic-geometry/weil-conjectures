/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.IntegralDualizingNativeTransition
public import WeilConjectures.SixFunctors.IntegralDualizingFiniteUnitQuotient

import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportScalarTransport
import all WeilConjectures.AlgebraicGeometry.EtaleOriginExtensionPullbackCube
import all WeilConjectures.AlgebraicGeometry.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteOpenScalarSiteTransport

/-! # Finite exceptional counits under quotient restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Prefer the fixed finite-site size when elaborating exact derived restrictions.
attribute [local instance 6000] finiteDualizingSiteSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem counit_transport
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {Sx : A ⥤ B} {Rx : B ⥤ A} {Sy : C ⥤ D} {Ry : D ⥤ C}
    {Sx' : A' ⥤ B'} {Rx' : B' ⥤ A'} {Sy' : C' ⥤ D'} {Ry' : D' ⥤ C'}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry) (bx : Sx' ⊣ Rx') (by' : Sy' ⊣ Ry')
    (FA : A ⥤ A') (FB : B ⥤ B') (GA : C ⥤ C') (GB : D ⥤ D')
    (HA : A ⥤ C) (HB : B ⥤ D) (IA : A' ⥤ C') (IB : B' ⥤ D')
    (sx : FA ⋙ Sx' ≅ Sx ⋙ FB) (sy : GA ⋙ Sy' ≅ Sy ⋙ GB)
    (cx : FB ⋙ Rx' ≅ Rx ⋙ FA) (cy : GB ⋙ Ry' ≅ Ry ⋙ GA)
    (r : Rx' ⋙ IA ⟶ IB ⋙ Ry')
    (nx : ∀ K, bx.unit.app (FA.obj K) ≫ Rx'.map (sx.hom.app K) =
      FA.map (ax.unit.app K) ≫ cx.inv.app (Sx.obj K))
    (ny : ∀ K, by'.unit.app (GA.obj K) ≫ Ry'.map (sy.hom.app K) =
      GA.map (ay.unit.app K) ≫ cy.inv.app (Sy.obj K))
    (K : A) (L : B) (U : C) (V : D)
    (p : IA.obj (FA.obj K) ≅ GA.obj (HA.obj K))
    (q : IB.obj (FB.obj L) ≅ GB.obj (HB.obj L))
    (u : Sx.obj K ⟶ L) (v : Sy.obj U ⟶ V)
    (e : HA.obj K ⟶ U) (f : HB.obj L ⟶ V)
    (b : Sy.obj (HA.obj K) ⟶ HB.obj (Sx.obj K))
    (he : b ≫ HB.map u ≫ f = Sy.map e ≫ v)
    (hs : (by'.homEquiv _ _).symm
        (IA.map (bx.unit.app (FA.obj K)) ≫ r.app (Sx'.obj (FA.obj K))) ≫
        IB.map (sx.hom.app K ≫ FB.map u) ≫ q.hom =
      Sy'.map p.hom ≫ sy.hom.app (HA.obj K) ≫ GB.map (b ≫ HB.map u)) :
    IA.map (FA.map (ax.homEquiv _ _ u) ≫ cx.inv.app L) ≫
        r.app (FB.obj L) ≫ Ry'.map (q.hom ≫ GB.map f) =
      p.hom ≫ GA.map e ≫ GA.map (ay.homEquiv _ _ v) ≫ cy.inv.app V := by
  have hx : FA.map (ax.homEquiv _ _ u) ≫ cx.inv.app L =
      bx.unit.app (FA.obj K) ≫ Rx'.map (sx.hom.app K ≫ FB.map u) := by
    have hc := cx.inv.naturality u
    dsimp only [Functor.comp_map] at hc
    rw [Adjunction.homEquiv_unit, FA.map_comp, Category.assoc, hc]
    rw [← Category.assoc, ← nx]
    simp only [Functor.map_comp, Category.assoc]
  have hy : by'.homEquiv _ _ (sy.hom.app U ≫ GB.map v) =
      GA.map (ay.homEquiv _ _ v) ≫ cy.inv.app V := by
    have hc := cy.inv.naturality v
    dsimp only [Functor.comp_map] at hc
    rw [Adjunction.homEquiv_unit, Ry'.map_comp, ← Category.assoc, ny]
    simp only [Adjunction.homEquiv_unit, GA.map_comp, Category.assoc]
    rw [← hc]
  have hn := sy.hom.naturality e
  dsimp only [Functor.comp_map] at hn
  have hs' := congrArg (fun t ↦ t ≫ GB.map f) hs
  simp only [Category.assoc, ← GB.map_comp] at hs'
  rw [he, GB.map_comp, ← reassoc_of% hn] at hs'
  have h := congrArg (by'.homEquiv _ _) hs'
  rw [by'.homEquiv_naturality_left, by'.homEquiv_naturality_left, hy] at h
  simp only [by'.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc] at h
  rw [hx, IA.map_comp, Category.assoc]
  have hr := r.naturality (sx.hom.app K ≫ FB.map u)
  dsimp only [Functor.comp_map] at hr
  rw [reassoc_of% hr]
  simpa only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] using h

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem ordinaryRestriction_eq (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    (finiteDualizingRestriction_existsUnique Y φ).choose = sfRealizationRestriction Y φ := by
  apply ((finiteDualizingRestriction_existsUnique Y φ).choose_spec.2 _ ?_).symm
  intro M W x
  have ht := (sfRealizationRestriction_existsUnique Y φ).exists.choose_spec M W
    (sfIntrinsicRealizationUnit Y B M W x)
  exact (heq_of_eq ht).trans (by rfl)

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem supportComparison_eq (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    FiniteCompactScalar.compactRealizationIso A c =
      ProEtale.sfIntrinsicCompactSupportComparison A c := by
  apply Iso.ext
  ext K
  simp only [FiniteCompactScalar.compactRealizationIso,
    ProEtale.sfIntrinsicCompactSupportComparison,
    ProEtale.sfIntrinsicOpenExtensionComparison, Equivalence.funInvIdAssoc,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.trans_hom, Iso.symm_hom, Category.id_comp,
    Category.comp_id]

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem genericRestriction_eq (Y : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    finiteDualizingGenericDerivedRestriction Y φ =
      Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2, u + 2,
        u + 1, u + 2, u + 1, u + 1, u + 1, u + 1, u + 1}
        (F₁ := (sfIntrinsicModuleEquivalence Y B).functor)
        (F₂ := proEtaleCoefficientRestrictScalars Y φ)
        (G₂ := (sfIntrinsicModuleEquivalence Y A).functor)
        (G₁ := sfFixedRestriction.{u, u + 1, u + 1} Y φ) (sfRealizationRestriction Y φ) := by
  unfold finiteDualizingGenericDerivedRestriction
  erw [ordinaryRestriction_eq]
  rfl

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem derivedRestriction_transport
    (Y : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (U : proEtaleRingModules Y (proEtaleConstantRing Y B) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A))
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (hU : U = proEtaleCoefficientRestrictScalars Y φ)
    (e : (sfIntrinsicDerivedEquivalence Y B).functor ⋙ U.mapDerivedCategory ≅
      Sheaf.derivedRestrictScalars.{u} (ProEt.topology Y) φ.ulift ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor)
    (he : HEq e (finiteDualizingGenericDerivedRestriction Y φ)) :
    e = Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence Y B).functor
        (Functor.mapDerivedCategoryNatIso (eqToIso hU)) ≪≫
      Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2, u + 2,
        u + 1, u + 2, u + 1, u + 1, u + 1, u + 1, u + 1}
        (F₁ := (sfIntrinsicModuleEquivalence Y B).functor)
        (F₂ := proEtaleCoefficientRestrictScalars Y φ)
        (G₂ := (sfIntrinsicModuleEquivalence Y A).functor)
        (G₁ := sfFixedRestriction.{u, u + 1, u + 1} Y φ) (sfRealizationRestriction Y φ) := by
  subst U
  have he' := eq_of_heq he
  subst e
  rw [genericRestriction_eq]
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, eqToIso_refl, Functor.mapDerivedCategoryNatIso_refl,
    NatTrans.id_app]
  erw [Category.id_comp]

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
attribute [local irreducible] Functor.mapDerivedCategory sfIntrinsicModuleEquivalence in
private theorem intrinsicRestriction_eq (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    finiteDualizingIntrinsicRestriction l E Y h =
      Functor.isoWhiskerLeft
        (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor
        (integralDualizingNativeRestriction l E Y h) ≪≫
      Functor.mapDerivedCategorySquareIso.{u + 2, u + 2, u + 2, u + 2, u + 2,
        u + 1, u + 2, u + 1, u + 1, u + 1, u + 1, u + 1}
        (F₁ := (sfIntrinsicModuleEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).functor)
        (F₂ := proEtaleCoefficientRestrictScalars Y (finiteDualizingQuotientBase l E h))
        (G₂ := (sfIntrinsicModuleEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor)
        (G₁ := sfFixedRestriction.{u, u + 1, u + 1} Y
          (finiteDualizingQuotientBase l E h))
        (sfRealizationRestriction Y (finiteDualizingQuotientBase l E h)) := by
  have := (normalizedDVRModuleRes_exact l E Y h).1
  have := (normalizedDVRModuleRes_exact l E Y h).2
  exact derivedRestriction_transport Y (finiteDualizingQuotientBase l E h)
    (normalizedDVRModuleRes l E Y h) (compactSupportModuleRes_eq l E Y h)
    (finiteDualizingIntrinsicRestriction l E Y h)
    (finiteDualizingIntrinsicRestriction_existsUnique l E Y h).choose_spec.1


open FiniteCompactScalar
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem realizationRestriction_native (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) Y) :
    (finiteDualizingRealizationRestriction l E Y h).inv.app K ≫
      (integralDualizingNativeRestriction l E Y h).hom.app
        ((finiteDualizingRealization l E Y n).obj K) =
    (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (m + 1)) Y).inv.app
        ((Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology
          (finiteDualizingQuotient l E h)).obj K) ≫
      (ProEtale.properOriginRestrictionIso (finiteDualizingQuotientBase l E h) Y).inv.app K ≫
      (proEtaleCoefficientRestrictScalars Y
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
        ((intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1)) Y).hom.app K) := by
  rw [finiteDualizingRealizationRestriction, intrinsicRestriction_eq]
  dsimp only [finiteDualizingRealization, Functor.comp_obj]
  simp only [ProEtale.properOriginRestrictionIso,
    Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, NatTrans.comp_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have hc :
      (ProEtale.scalarMateRestriction (finiteDualizingQuotientBase l E h) Y).mapDerivedCategory.map
          ((intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1)) Y).inv.app K) ≫
        (proEtaleCoefficientRestrictScalars Y
          (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1)) Y).hom.app K) =
      𝟙 _ := by
    change (proEtaleCoefficientRestrictScalars Y
      (finiteDualizingQuotientBase l E h)).mapDerivedCategory.map _ ≫
        (proEtaleCoefficientRestrictScalars Y
          (finiteDualizingQuotientBase l E h)).mapDerivedCategory.map _ = _
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    exact (proEtaleCoefficientRestrictScalars Y
      (finiteDualizingQuotientBase l E h)).mapDerivedCategory.map_id _
  erw [hc, Category.comp_id]
  rfl


attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private def fullOrigin (n : ℕ) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison X
      (Padic.coefficientExtensionRing l E (n + 1))).obj
        (finiteDualizingEtaleTerm l E D X n) ≅ integralDualizingFiniteTerm l E D X n :=
  (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1)) X).app
    (finiteDualizingEtaleTerm l E D X n) ≪≫ finiteDualizingOrigin l E D X n

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private def rawCounit (n : ℕ) :
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X
          (Padic.coefficientExtensionRing l E (n + 1))).obj
            (finiteDualizingEtaleTerm l E D X n)) ⟶
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))).obj
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))) :=
  (compactSiteIso (Padic.coefficientExtensionRing l E (n + 1))
    (finiteDualizingCompactification D X)
    ⟨finiteDualizingEtaleTerm l E D X n, integralDualizingFiniteEtalePlus D l E X n⟩).inv ≫
  (ProEtale.finiteCoefficientIntrinsicDerivedComparison (Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))).map
    (finiteDualizingEtaleCounit l E D X n)

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem counit_coordinates (n : ℕ) :
    integralDualizingFiniteSystemCounit D l E X n =
      (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
        (Padic.coefficientExtensionRing l E (n + 1))).map (fullOrigin l E D X n).inv ≫
      rawCounit l E D X n ≫
      (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1))
        (Spec (.of D.k))).hom.app
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))) := by
  simp only [fullOrigin, rawCounit, compactSiteIso, Iso.trans_inv, Iso.app_inv,
    Iso.app_hom, Iso.symm_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  have hn :=
    (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1))
      (Spec (.of D.k))).hom.naturality (finiteDualizingEtaleCounit l E D X n)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Category.comp_id,
    Iso.inv_hom_id_app_assoc]
  rw [supportComparison_eq]
  rfl

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem transition_coordinates (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    integralDualizingExceptionalTransition l E D X hl h ≫
      (integralDualizingNativeRestriction l E X h).hom.app
        (integralDualizingFiniteTerm l E D X n) =
    (fullOrigin l E D X m).inv ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison X
        (Padic.coefficientExtensionRing l E (m + 1))).map
        (finiteDualizingEtaleTransition l E D X h) ≫
      (ProEtale.properOriginRestrictionIso (finiteDualizingQuotientBase l E h) X).inv.app
        (finiteDualizingEtaleTerm l E D X n) ≫
      (proEtaleCoefficientRestrictScalars X
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
        (fullOrigin l E D X n).hom := by
  unfold integralDualizingExceptionalTransition
  simp only [Category.assoc]
  rw [(integralDualizingNativeRestriction l E X h).hom.naturality
    (finiteDualizingOrigin l E D X n).hom]
  rw [reassoc_of% realizationRestriction_native l E X h]
  simp only [fullOrigin, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  have hn :=
    (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (m + 1)) X).inv.naturality
      (finiteDualizingEtaleTransition l E D X h)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem unit_coordinates (Y : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    integralDualizingFiniteUnitQuotient l E Y h ≫
      (integralDualizingNativeRestriction l E Y h).hom.app
        ((finiteDualizingRealization l E Y n).obj
          (Etale.constantComplex (finiteDualizingCoeff l E n) Y)) =
    (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (m + 1)) Y).inv.app
        (Etale.constantComplex (finiteDualizingCoeff l E m) Y) ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y
        (Padic.coefficientExtensionRing l E (m + 1))).map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology
          (finiteDualizingQuotient l E h))).homEquiv _ _
            (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) Y).hom) ≫
      (ProEtale.properOriginRestrictionIso (finiteDualizingQuotientBase l E h) Y).inv.app
        (Etale.constantComplex (finiteDualizingCoeff l E n) Y) ≫
      (proEtaleCoefficientRestrictScalars Y
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
        ((intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1)) Y).hom.app
          (Etale.constantComplex (finiteDualizingCoeff l E n) Y)) := by
  unfold integralDualizingFiniteUnitQuotient
  rw [Category.assoc, realizationRestriction_native]
  have hn :=
    (intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (m + 1)) Y).inv.naturality
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology
        (finiteDualizingQuotient l E h))).homEquiv _ _
          (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h) Y).hom)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rfl

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem compactScalar_eq {m n : ℕ} (h : n ≤ m)
    [IsNoetherian (finiteDualizingCompactification D X).Z]
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E m) X) :
    (Etale.FiniteCompactScalar.compactScalarIso (finiteDualizingQuotient l E h)
      (finiteDualizingCompactification D X)).hom.app K =
      Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h)
        (finiteDualizingCompactification D X) K := by
  unfold Etale.FiniteCompactScalar.compactScalarIso
  erw [etale_open_iso_eq (finiteDualizingQuotientBase l E h)
    (finiteDualizingCompactification D X).i,
    ← Etale.compactScalarOpen_eq (finiteDualizingQuotient l E h)
      (finiteDualizingCompactification D X).i]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app, asIso_hom,
    Category.id_comp, Category.comp_id]
  rfl

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem scalarSite_unit {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (Y : Scheme.{u})
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y) :
    (pbcDerivedScalarAdjunction.{u} (scalarRingMap φ Y)).unit.app
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).obj K) ≫
      (pbcDerivedRestrict.{u} (scalarRingMap φ Y)).map ((siteScalarIso φ Y).hom.app K) =
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
          Y.smallEtaleTopology φ.ulift)).unit.app K) ≫
      (ProEtale.properOriginRestrictionIso φ Y).inv.app
        ((Etale.scalarExtension φ.ulift Y).obj K) := by
  have ht := unit_mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology φ.ulift))
    (pbcDerivedScalarAdjunction.{u} (scalarRingMap φ Y))
    (TwoSquare.mk _ _ _ _ (siteScalarIso φ Y).hom) K
  have hm := NatTrans.congr_app (ProEtale.site_scalar_mate φ Y)
    ((Etale.scalarExtension φ.ulift Y).obj K)
  rw [← hm]
  exact ht.symm

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem rawCounit_square (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    let A := Padic.coefficientExtensionRing l E (m + 1)
    let B := Padic.coefficientExtensionRing l E (n + 1)
    let φ := finiteDualizingQuotientBase l E h
    let c := finiteDualizingCompactification D X
    let GA : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))) :=
      ⟨finiteDualizingEtaleTerm l E D X m, integralDualizingFiniteEtalePlus D l E X m⟩
    let GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
      ⟨finiteDualizingEtaleTerm l E D X n, integralDualizingFiniteEtalePlus D l E X n⟩
    (sfIntrinsicCompactSupport c A).map
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).map
          (finiteDualizingEtaleTransition l E D X h) ≫
            (ProEtale.properOriginRestrictionIso φ X).inv.app GB.obj) ≫
      (sfCompactSupportRestriction c φ).hom.app
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj GB.obj) ≫
      (pbcDerivedRestrict.{u} (scalarRingMap φ (Spec (.of D.k)))).map
        ((compactSiteIso B c GB).inv ≫
          (ProEtale.finiteCoefficientIntrinsicDerivedComparison (Spec (.of D.k)) B).map
            (finiteDualizingEtaleCounit l E D X n)) =
    (compactSiteIso A c GA).inv ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison (Spec (.of D.k)) A).map
        (finiteDualizingEtaleCounit l E D X m) ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison (Spec (.of D.k)) A).map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
          (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))).homEquiv _ _
            (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
              (Spec (.of D.k))).hom) ≫
      (ProEtale.properOriginRestrictionIso φ (Spec (.of D.k))).inv.app
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))) := by
  classical
  dsimp only
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let φ := finiteDualizingQuotientBase l E h
  let c := finiteDualizingCompactification D X
  let GA : DerivedCategory.Plus _ :=
    ⟨finiteDualizingEtaleTerm l E D X m, integralDualizingFiniteEtalePlus D l E X m⟩
  let GB : DerivedCategory.Plus _ :=
    ⟨finiteDualizingEtaleTerm l E D X n, integralDualizingFiniteEtalePlus D l E X n⟩
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  obtain ⟨hb, hu, he⟩ := (finiteDualizingCoefficientComparisons l E D X hl).1 h
  have := hu
  have := hb
  let u := asIso (finiteDualizingEtaleComparison l E D X h)
  have he' : finiteDualizingCompactComparison l E D X h ≫
      (finiteDualizingEtaleSupport l E D X n).map u.hom ≫
        finiteDualizingEtaleCounit l E D X n =
      (Etale.scalarExtension (finiteDualizingQuotient l E h) (Spec (.of D.k))).map
        (finiteDualizingEtaleCounit l E D X m) ≫
      (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
        (Spec (.of D.k))).hom := by
    simp only [u, asIso_hom]
    erw [he]
    have hi : Etale.ExceptionalCoefficients.comparisonInverse (finiteDualizingQuotient l E h)
        c GA.obj = inv (finiteDualizingCompactComparison l E D X h) := by
      unfold Etale.ExceptionalCoefficients.comparisonInverse
      change (if _ : IsIso (finiteDualizingCompactComparison l E D X h) then _ else _) = _
      rw [dif_pos hb]
      rfl
    erw [hi, IsIso.hom_inv_id_assoc]
  apply counit_transport
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ.ulift))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} (Spec (.of D.k)).smallEtaleTopology φ.ulift))
    (pbcDerivedScalarAdjunction.{u} (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction.{u} (scalarRingMap φ (Spec (.of D.k))))
    _ _ _ _ _ _ _ _ (siteScalarIso φ X) (siteScalarIso φ (Spec (.of D.k)))
    (ProEtale.properOriginRestrictionIso φ X)
    (ProEtale.properOriginRestrictionIso φ (Spec (.of D.k)))
    (sfCompactSupportRestriction c φ).hom
    (scalarSite_unit φ X) (scalarSite_unit φ (Spec (.of D.k)))
    GA.obj GB.obj _ _ (compactSiteIso A c GA).symm (compactSiteIso B c GB).symm
    u.hom _ _ _ (finiteDualizingCompactComparison l E D X h) he'
  have hc :
      (sfIntrinsicCompactSupport c B).map
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).map u.inv ≫
          (siteScalarIso φ X).inv.app GA.obj) ≫
      (sfAmbientCompactSupportCandidate B c).map
        ((siteScalarIso φ X).hom.app GA.obj ≫
          (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).map u.hom) = 𝟙 _ := by
    change (sfIntrinsicCompactSupport c B).map _ ≫
      (sfIntrinsicCompactSupport c B).map _ = _
    rw [← Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have ht := intrinsicCompactScalarIsoOfOrigin_hom φ c GA GB u
  erw [ht]
  simp only [intrinsicCompactScalarIsoOfOrigin, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  erw [reassoc_of% hc]
  erw [Iso.hom_inv_id, Category.comp_id]
  erw [compactScalar_eq l E D X h]
  simp only [Functor.map_comp]
  rfl


attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
private theorem counit_coordinates_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ C) (G : B ⥤ D) (R : B ⥤ A) (S : D ⥤ C)
    (r : R ⋙ F ⟶ G ⋙ S)
    {K K' : A} {L L' : B} {U U' : C} {V V' : D}
    (o : K ≅ K') (p : L ≅ L') (a : U ≅ U') (b : V ≅ V')
    (t : K ⟶ R.obj L) (c : F.obj K ⟶ U) (d : G.obj L ⟶ V) (v : U ⟶ S.obj V)
    (h : F.map t ≫ r.app L ≫ S.map d = c ≫ v) :
    F.map (o.inv ≫ t ≫ R.map p.hom) ≫ r.app L' ≫
        S.map (G.map p.inv ≫ d ≫ b.hom) =
      (F.map o.inv ≫ c ≫ a.hom) ≫ (a.inv ≫ v ≫ S.map b.hom) := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  have hn := r.naturality p.hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← S.map_comp_assoc, Iso.map_hom_inv_id_assoc]
  rw [← reassoc_of% h]

attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived in
/-- The fixed exceptional counit is compatible with the finite scalar-adjunction unit.
This involves only the two finite levels, without a sequence object or tensor model.
Source: prop-coef-integral-dualizing, paragraph 2; finite coefficient counit identity.
(blueprint: lem-coef-finite-counit-quotient).
Proof: write the finite exceptional transition as the realization of the scalar adjunct
of finiteDualizingEtaleComparison, conjugated by finiteDualizingOrigin. Cancel the
origin at level n against the first factor of the finite system counit. The normalized
compact-support restriction square and the canonical site comparison carry this word
to the ordinary etale scalar-adjunction word. Naturality of the scalar unit writes it
as the scalar unit at compact support followed by restriction of the compact-support
coefficient comparison, support of the dualizing comparison, and the level n counit.
The finiteDualizingCoefficientComparisons counit equation cancels the coefficient
comparison with its inverse. Scalar-unit naturality moves the level m counit to the
left; the remaining unit comparison is integralDualizingFiniteUnitQuotient. Transport
back through the same site comparisons. Exact restriction suffices, including m=n,
n=0, and the zero complex; no quotient-flatness is used. -/
theorem integralDualizingFiniteCounit_quotient (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) :
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (m + 1))).map
        (integralDualizingExceptionalTransition l E D X hl h ≫
          (integralDualizingNativeRestriction l E X h).hom.app
            (integralDualizingFiniteTerm l E D X n)) ≫
      (sfCompactSupportRestriction (finiteDualizingCompactification D X)
        (compactSupportLevelQuotient l E m n h)).hom.app
          (integralDualizingFiniteTerm l E D X n) ≫
      (proEtaleCoefficientRestrictScalars (Spec (.of D.k))
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          (integralDualizingFiniteSystemCounit D l E X n) =
    integralDualizingFiniteSystemCounit D l E X m ≫
      integralDualizingFiniteUnitQuotient l E (Spec (.of D.k)) h ≫
      (integralDualizingNativeRestriction l E (Spec (.of D.k)) h).hom.app
        ((finiteDualizingRealization l E (Spec (.of D.k)) n).obj
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))) := by
  rw [transition_coordinates]
  rw [counit_coordinates, counit_coordinates]
  simp only [Category.assoc]
  rw [unit_coordinates]
  simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, finiteDualizingRealization]
    using counit_coordinates_paste
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (m + 1)))
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleCoefficientRestrictScalars X
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    (proEtaleCoefficientRestrictScalars (Spec (.of D.k))
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    (sfCompactSupportRestriction (finiteDualizingCompactification D X)
      (compactSupportLevelQuotient l E m n h)).hom
    (fullOrigin l E D X m) (fullOrigin l E D X n)
    ((intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (m + 1))
      (Spec (.of D.k))).app _)
    ((intrinsicSiteFunctorIso (Padic.coefficientExtensionRing l E (n + 1))
      (Spec (.of D.k))).app _)
    ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X
      (Padic.coefficientExtensionRing l E (m + 1))).map
        (finiteDualizingEtaleTransition l E D X h) ≫
      (ProEtale.properOriginRestrictionIso (finiteDualizingQuotientBase l E h) X).inv.app
        (finiteDualizingEtaleTerm l E D X n))
    (rawCounit l E D X m) (rawCounit l E D X n)
    ((ProEtale.finiteCoefficientIntrinsicDerivedComparison (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (m + 1))).map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u}
          (Spec (.of D.k)).smallEtaleTopology (finiteDualizingQuotient l E h))).homEquiv _ _
            (Etale.ExceptionalCoefficients.unitIso (finiteDualizingQuotient l E h)
              (Spec (.of D.k))).hom) ≫
      (ProEtale.properOriginRestrictionIso (finiteDualizingQuotientBase l E h)
        (Spec (.of D.k))).inv.app
          (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))))
    (by
      dsimp only [rawCounit]
      have hs := rawCounit_square l E D X hl h
      dsimp only at hs
      simpa only [Category.assoc, pbcDerivedRestrict, pbcRestrict, scalarRingMap,
        proEtaleCoefficientRestrictScalars, proEtaleConstantRingMap,
        finiteDualizingQuotientBase, compactSupportLevelQuotient] using hs)

end WeilConjectures

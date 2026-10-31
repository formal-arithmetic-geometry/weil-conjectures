/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSpanModuleComparisonData
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses

/-! # Ordinary finite-span scalar comparison data

Source: Stacks Project, Modules on Sites, Tags 03D6 and 03D7.
(blueprint: lem-sf-finite-span-scalar-ordinary). -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
open scoped CategoryTheory.Obj
open SheafOfModules
  (grothendieckAbelian_and_functorial_kInjective_resolutionsMixedUniverses)

namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

private theorem ordinaryNativeComm (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (theta : condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [IsMonHom theta.hom] : IsCommMonObj (nativeAb l X) := by
  constructor
  apply (cancel_epi (theta.hom ⊗ₘ theta.hom)).mp
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
    ← IsMonHom.mul_hom, ← Category.assoc, IsCommMonObj.mul_comm]

private abbrev ordinaryNativeMap (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    nativeAb l Y ⟶ (lowerStar Ab.{u + 1} f).obj (nativeAb l X) :=
  (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)

private theorem ordinaryNativeCoefficientMon (l : ℕ) [Fact l.Prime]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsMonHom (ordinaryNativeMap l f) := by
  have h : ordinaryNativeMap l f =
      (theta Y).inv ≫ condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom := by
    rw [hcoeff X Y f, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [h]
  infer_instance

private def ordinaryCoefficientMap (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsMonHom (ordinaryNativeMap l f)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring l Y ⟶ ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring l X) :=
  (InternalModuleOperations.sectionRingMap_existsUnique
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (InternalModuleOperations.siteMap f) (nativeAb l X) (nativeAb l Y)
    (ordinaryNativeMap l f)).exists.choose

private theorem ordinaryCoefficientMap_apply (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsMonHom (ordinaryNativeMap l f)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEtᵒᵖ) (r : (ring l Y).obj.obj V) :
    ((ordinaryCoefficientMap l f).hom.app V).hom r =
      (((weilCoefficientsForgetAb l Y).map
        (adicConstantSheafToLowerStar l f)).hom.app V).hom r := by
  exact (InternalModuleOperations.sectionRingMap_existsUnique
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (InternalModuleOperations.siteMap f) (nativeAb l X) (nativeAb l Y)
    (ordinaryNativeMap l f)).exists.choose_spec V r

private theorem ordinaryCoefficientMap_sections (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsMonHom (ordinaryNativeMap l f)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEtᵒᵖ) (r : (ring l Y).obj.obj V)
    (x : ((InternalModuleOperations.siteMap f).obj V.unop).left) :
    ((((ordinaryCoefficientMap l f).hom.app V).hom r).down.1 x) =
      r.down.1 ((Limits.pullback.fst V.unop.hom f).base x) := by
  rw [ordinaryCoefficientMap_apply]
  rfl

private theorem ordinaryEquivalence_smul (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)]
    (theta : condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [IsMonHom theta.hom] (M : internal l X) (V : X.ProEtᵒᵖ)
    (r : (ring l X).obj.obj V)
    (m : ((equivalence l X theta).functor.obj M).val.obj V) :
    r • m =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X) M.X).app V ≫
        (Mod.act M.X).hom.app V).hom ((theta.inv.hom.app V).hom r ⊗ₜ[ℤ] m) := by
  let I := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  have hn := congr_app (Functor.LaxMonoidal.μ_natural_left I theta.inv M.X) V
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t ≫ (Mod.act M.X).hom.app V) hn) (r ⊗ₜ[ℤ] m)
  simp only [NatTrans.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hh
  erw [Monoidal.whiskerRight_app,
    AddCommGrpCat.MonoidalCategory.whiskerRight_tmul] at hh
  exact hh.symm

private theorem ordinarySheafSquare_apply
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    {AX BX : Sheaf K Ab.{u + 1}} {AY BY : Sheaf J Ab.{u + 1}}
    (eX : AX ≅ BX) (eY : AY ≅ BY)
    (eta : AY ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj AX)
    (psi : BY ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj BX)
    (h : eta ≫ (F.sheafPushforwardContinuous Ab.{u + 1} J K).map eX.hom =
      eY.hom ≫ psi) (V : Cᵒᵖ) (r : BY.obj.obj V) :
    (eta.hom.app V).hom ((eY.inv.hom.app V).hom r) =
      (eX.inv.hom.app (F.op.obj V)).hom ((psi.hom.app V).hom r) := by
  let P := F.sheafPushforwardContinuous Ab.{u + 1} J K
  have hc : eY.inv ≫ eta = psi ≫ P.map eX.inv := by
    apply (cancel_epi eY.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h, Category.assoc, ← P.map_comp,
      Iso.hom_inv_id, P.map_id, Category.comp_id]
  have he := congr_app (congrArg (fun q : BY ⟶ P.obj AX ↦ q.hom) hc) V
  change eY.inv.hom.app V ≫ eta.hom.app V =
    psi.hom.app V ≫ eX.inv.hom.app (F.op.obj V) at he
  exact congrArg (fun k : BY.obj.obj V ⟶ AX.obj.obj (F.op.obj V) ↦ k.hom r) he

private theorem ordinaryNativeSquare_apply (l : ℕ) [Fact l.Prime]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (nativeAb l Y).obj.obj V) :
    ((condensedPushforwardHom (Profinite.padicAlgClRingObj l) f).hom.app V).hom
      (((theta Y).inv.hom.app V).hom r) =
    ((theta X).inv.hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom
      ((((weilCoefficientsForgetAb l Y).map
        (adicConstantSheafToLowerStar l f)).hom.app V).hom r) := by
  exact ordinarySheafSquare_apply (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (InternalModuleOperations.siteMap f) (theta X) (theta Y)
    (condensedPushforwardHom (Profinite.padicAlgClRingObj l) f) (ordinaryNativeMap l f)
    (hcoeff X Y f) V r

private theorem ordinaryCoefficientInverse_apply (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsMonHom (ordinaryNativeMap l f)]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (ring l Y).obj.obj V) :
    ((condensedPushforwardHom (Profinite.padicAlgClRingObj l) f).hom.app V).hom
      (((theta Y).inv.hom.app V).hom r) =
    ((theta X).inv.hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom
      (((ordinaryCoefficientMap l f).hom.app V).hom r) := by
  exact (ordinaryNativeSquare_apply l theta hcoeff f V r).trans
    (congrArg (fun t : (nativeAb l X).obj.obj
        ((InternalModuleOperations.siteMap f).op.obj V) ↦
      ((theta X).inv.hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom t)
      (ordinaryCoefficientMap_apply l f V r)).symm

private theorem ordinaryPushedAction (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : internal l X) (V : Y.ProEtᵒᵖ)
    (r : (ring l Y).obj.obj V)
    (m : M.X.obj.obj ((InternalModuleOperations.siteMap f).op.obj V)) :
    r • (@id (((equivalence l Y (theta Y)).functor.obj
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).obj M)).val.obj V) m) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) M.X).app
      ((InternalModuleOperations.siteMap f).op.obj V) ≫
      (Mod.act M.X).hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom
        (((condensedPushforwardHom (Profinite.padicAlgClRingObj l) f).hom.app V).hom
          (((theta Y).inv.hom.app V).hom r) ⊗ₜ[ℤ] m) := by
  exact (ordinaryEquivalence_smul l Y (theta Y)
    ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).obj M) V r m).trans
    (InternalModuleOperations.section_action (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) (InternalModuleOperations.siteMap f)
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y) M.X
      (condensedPushforwardHom (Profinite.padicAlgClRingObj l) f) (Mod.act M.X)
      V (((theta Y).inv.hom.app V).hom r) m)

private theorem ordinaryPush_smul (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsMonHom (ordinaryNativeMap l f)]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internal l X) (V : Y.ProEtᵒᵖ) (r : (ring l Y).obj.obj V)
    (m : (((equivalence l X (theta X)).functor ⋙
      direct l f (ordinaryCoefficientMap l f)).obj M).val.obj V) :
    ((ModuleCat.smul (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f ⋙
      (equivalence l Y (theta Y)).functor).obj M).val.obj V) r).hom) m =
    ((ModuleCat.smul ((((equivalence l X (theta X)).functor ⋙
      direct l f (ordinaryCoefficientMap l f)).obj M).val.obj V) r).hom) m := by
  have hs := ordinaryCoefficientInverse_apply l theta hcoeff f V r
  have hL := ordinaryPushedAction l theta f M V r m
  have hR := ordinaryEquivalence_smul l X (theta X) M
    ((InternalModuleOperations.siteMap f).op.obj V)
    (((ordinaryCoefficientMap l f).hom.app V).hom r) m
  exact hL.trans ((congrArg (fun t ↦
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) M.X).app
      ((InternalModuleOperations.siteMap f).op.obj V) ≫
      (Mod.act M.X).hom.app ((InternalModuleOperations.siteMap f).op.obj V)).hom
      (t ⊗ₜ[ℤ] m)) hs).trans hR.symm)

private theorem ordinaryPushComparison_exists (l : ℕ) [Fact l.Prime]
    [∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsMonHom (ordinaryNativeMap l f)]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ c : CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f ⋙
        (equivalence l Y (theta Y)).functor ≅
      (equivalence l X (theta X)).functor ⋙ direct l f (ordinaryCoefficientMap l f),
      ∀ (M : internal l X) (V : Y.ProEtᵒᵖ)
        (m : ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).obj M).X.obj.obj V),
        (((c.hom.app M).val.app V).hom m) = m := by
  let L := CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f ⋙
    (equivalence l Y (theta Y)).functor
  let R := (equivalence l X (theta X)).functor ⋙ direct l f (ordinaryCoefficientMap l f)
  have h (M : internal l X) (V : Y.ProEtᵒᵖ)
      (r : (ring l Y).obj.obj V) (m : (R.obj M).val.obj V) :
      ((ModuleCat.smul ((L.obj M).val.obj V) r).hom) m =
        ((ModuleCat.smul ((R.obj M).val.obj V) r).hom) m :=
    ordinaryPush_smul l theta hcoeff f M V r m
  let q (M) : L.obj M ⟶ R.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (L.obj M).val) (M₂ := (R.obj M).val)
      (𝟙 _) (fun V r m ↦ h M V r m)⟩
  let p (M) : R.obj M ⟶ L.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (R.obj M).val) (M₂ := (L.obj M).val)
      (𝟙 _) (fun V r m ↦ (h M V r m).symm)⟩
  refine ⟨NatIso.ofComponents
    (fun M ↦ { hom := q M, inv := p M,
               hom_inv_id := by ext V m; rfl,
               inv_hom_id := by ext V m; rfl })
    (fun α ↦ by ext V m; rfl), ?_⟩
  intro M V m
  rfl

private def ordinaryCancelEquivalence
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (E : A ≌ B) {F G : B ⥤ C} (e : E.functor ⋙ F ≅ E.functor ⋙ G) : F ≅ G :=
  F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm F ≪≫
    Functor.isoWhiskerLeft E.inverse e ≪≫ Functor.isoWhiskerRight E.counitIso G ≪≫
      G.leftUnitor

/-- Normalized ring maps and ordinary scalar comparison for the supplied coefficient isomorphism.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Bhatt--Scholze,
Definitions 6.8.1 and 6.8.3 and Remark 6.8.15.
(blueprint: lem-sf-finite-span-scalar-ordinary).

Proof. Transport commutativity of the condensed coefficient to the native ring object
along the multiplicative isomorphism theta. The coefficient square writes the native
direct-image map as theta inverse, the condensed coefficient map and pushed theta, so it
is a monoid homomorphism; its reconstructed section-ring map is precomposition along the
first base-change projection. Construct presheaf pullback on small models of the sites, then
sheafify, giving the specified adjunction. Restrict internal actions along theta inverse
and reconstruct sections.
The coefficient square identifies the pushed actions, so identity section maps are
linear and define the direct-image comparison. Take its unique adjoint mate to construct
the pullback comparison. This transports exactness of the internal pullback and gives
the ordinary mate equation. Equivalences are additive in both directions. The small
ringed-site resolution theorem gives K-injective resolutions and derived categories;
right-derived composition with these exact equivalences gives some derived pushforward
comparison. Compositors can first be transported through the equivalences; their
geometric normalization and that of the derived comparison are separate subsequent steps.
All constructions apply to empty schemes, identity maps, and zero modules. -/
theorem finiteSpanScalarTransportOrdinary (l : ℕ) [Fact l.Prime]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)) :
    ∃ d : Data.{u} l, letI := d; d.theta = theta ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEtᵒᵖ)
    (r : (ring l Y).obj.obj V) (x : ((InternalModuleOperations.siteMap f).obj V.unop).left),
    (((d.coefficientMap f).hom.app V r).down.1 x) =
      r.down.1 ((Limits.pullback.fst V.unop.hom f).base x)) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adjunction l f (d.coefficientMap f)) (d.pullComparison f).inv).natTrans =
        (d.pushComparison f).hom) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : internal l X)
    (V : Y.ProEtᵒᵖ) (m : ((CondensedRing.lowerStar
      (Profinite.padicAlgClRingObj l) f).obj M).X.obj.obj V),
    (((d.pushComparison f).hom.app M).val.app V) m = m) := by
  classical
  let (X : Scheme.{u}) : IsCommMonObj (nativeAb l X) :=
    ordinaryNativeComm l X (theta X)
  let {X Y : Scheme.{u}} (f : X ⟶ Y) :
      IsMonHom (ordinaryNativeMap l f) :=
    ordinaryNativeCoefficientMon l theta hcoeff f
  let r := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ ordinaryCoefficientMap l f
  let {X Y : Scheme.{u}} (f : X ⟶ Y) :
      (PresheafOfModules.pushforward.{u + 1}
        (F := InternalModuleOperations.siteMap f) (r f).hom).IsRightAdjoint :=
    InternalModuleOperations.presheafPushforward_isRightAdjoint
      (InternalModuleOperations.siteMap f) (ring l X).obj (ring l Y).obj (r f).hom
  let E := fun X : Scheme.{u} ↦ equivalence l X (theta X)
  let (X : Scheme.{u}) : (E X).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let (X : Scheme.{u}) : (E X).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let (X : Scheme.{u}) : IsGrothendieckAbelian.{u + 1} (modules l X) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsMixedUniverses.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X)
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (nativeAb l X))).1
  let (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (modules l X) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let (X : Scheme.{u}) : Abelian.HasKInjectiveResolutions (modules l X) := inferInstance
  let c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f ⋙ (E Y).functor ≅
        (E X).functor ⋙ direct l f (r f) :=
    fun f ↦ (ordinaryPushComparison_exists l theta hcoeff f).choose
  let a := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦
    exists_equivalenceAdjunctionComparison (E Y) (E X)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adjunction l f (r f)) (c f)
  let p := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ (a f).choose
  let {X Y : Scheme.{u}} (f : X ⟶ Y) : PreservesFiniteLimits (inverse l f (r f)) :=
    (InternalModuleOperations.preserves_finite_limits_iff (E Y) (E X)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
      (inverse l f (r f)) (p f)).mp inferInstance
  let {X Y : Scheme.{u}} (f : X ⟶ Y) : PreservesFiniteColimits (inverse l f (r f)) :=
    (InternalModuleOperations.preserves_finite_colimits_iff (E Y) (E X)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
      (inverse l f (r f)) (p f)).mp inferInstance
  let {X Y : Scheme.{u}} (f : X ⟶ Y) : (inverse l f (r f)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let {X Y : Scheme.{u}} (f : X ⟶ Y) : (direct l f (r f)).Additive :=
    { map_add := by intros; ext V m; rfl }
  let cc := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
    ordinaryCancelEquivalence (E X)
      (F := direct l f (r f) ⋙ direct l g (r g)) (G := direct l (f ≫ g) (r (f ≫ g)))
      ((Functor.associator (E X).functor (direct l f (r f)) (direct l g (r g))).symm ≪≫
        Functor.isoWhiskerRight (c f).symm (direct l g (r g)) ≪≫
        Functor.associator (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
          (E Y).functor (direct l g (r g)) ≪≫
        Functor.isoWhiskerLeft (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
          (c g).symm ≪≫
        (Functor.associator (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
          (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g) (E Z).functor).symm ≪≫
        Functor.isoWhiskerRight
          (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g) (E Z).functor ≪≫
        c (f ≫ g))
  let d : Data.{u} l :=
    { theta := theta
      coefficientMap := r
      pullComparison := p
      pushComparison := c
      pushComposition := cc
      pullComposition := fun f g ↦
        (Adjunction.leftAdjointCompIso (adjunction l g (r g)) (adjunction l f (r f))
          (adjunction l (f ≫ g) (r (f ≫ g))) (cc f g)).symm
      derivedPushComparison := fun f ↦ rightSquareIso
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f)
        (E _).functor (E _).functor (direct l f (r f)) (c f) }
  refine ⟨d, rfl, ?_, ?_, ?_⟩
  · exact ordinaryCoefficientMap_sections l
  · intro X Y f
    exact (a f).choose_spec.1
  · intro X Y f M V m
    exact (ordinaryPushComparison_exists l theta hcoeff f).choose_spec M V m

end AlgebraicGeometry.ProEtale.FiniteSpanComparison

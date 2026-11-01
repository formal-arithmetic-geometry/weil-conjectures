/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasicDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleSheetTrace
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! # Deriving the fixed native finite-etale sheet trace -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

private theorem natTrans_fach
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F ⟶ G) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryNatTrans τ).app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hnt : (NatTrans.mapHomotopyCategory τ (.up ℤ)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := rfl
  rw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app, hnt,
    ← NatTrans.naturality_assoc, Functor.mapDerivedCategoryNatTrans_fac_assoc,
    reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K))]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
  simp

private theorem derivedId_fach
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (Z : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj Z) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app Z ≫ DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app Z) := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C)) Z
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  erw [Category.comp_id, Category.comp_id] at h
  exact h

section

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

private theorem derivedCounit_formula (K : DerivedCategory D) :
    adj.mapDerivedCategoryAdjunction.counit.app K =
      (Functor.mapDerivedCategoryCompIso g f).inv.app K ≫
        (Functor.mapDerivedCategoryNatTrans adj.counit).app K ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app K := by
  have h := Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso D (.up ℤ))
    (τ := adj.mapDerivedCategoryAdjunction.counit)
    (τ' := (Functor.mapDerivedCategoryCompIso g f).inv ≫
      Functor.mapDerivedCategoryNatTrans adj.counit ≫
      (Functor.mapDerivedCategoryIdIso D).hom) (fun X ↦ by
        simp only [NatTrans.comp_app]
        rw [adj.mapDerivedCategoryAdjunction_counit_app_Qh_obj,
          derivedId_fach, reassoc_of% (natTrans_fach adj.counit X)]
        have hc := Functor.mapDerivedCategoryCompIso_fach g f X
        have hh : (NatTrans.mapHomotopyCategory adj.counit (.up ℤ)).app X =
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (g ⋙ f)) (.up ℤ)).inv.app X ≫
              (adj.mapHomotopyCategory (.up ℤ)).counit.app X ≫
              (Functor.mapHomotopyCategoryIdIso D (.up ℤ)).inv.app X := by
          obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
          rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
          rw [Functor.mapHomotopyCategoryCompIso_refl_inv_app]
          have hid : (Functor.mapHomotopyCategoryIdIso D (.up ℤ)).inv.app
              ((HomotopyCategory.quotient D (.up ℤ)).obj L) = 𝟙 _ := by
            rw [← cancel_epi ((Functor.mapHomotopyCategoryIdIso D (.up ℤ)).hom.app
              ((HomotopyCategory.quotient D (.up ℤ)).obj L)), Iso.hom_inv_id_app,
              Functor.mapHomotopyCategoryIdIso_hom_app_eq_id, Category.comp_id]
            rfl
          rw [hid, Category.id_comp, Category.comp_id]
          rfl
        rw [hh, Functor.map_comp, Functor.map_comp]
        rw [← hc]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
          ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc,
          Iso.inv_hom_id_app, Category.comp_id])
  exact NatTrans.congr_app h K

end

variable (ell : ℕ) [Fact ell.Prime]

/-- The derived canonical sheet trace, constructed directly from the descended
sheaf natural transformation. No reverse adjunction is selected in this definition.
Source: exact derivation of finite sheet sums, clause (3) of smooth trace.
(blueprint: new-det-sp-native-finite-etale-derived-trace). -/
def traceDerivedSheetSum (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Etale f] (K : c.derived ell Y) :
    (actualPush (c.obj.{u} ell) f).obj ((actualPull (c.obj.{u} ell) f).obj K) ⟶ K :=
  letI := CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite (c.obj.{u} ell) f
  ((CondensedRing.lowerStar (c.obj.{u} ell) f).rightDerivedFunctorIsoMapDerivedCategory).hom.app _ ≫
    (CondensedRing.lowerStar (c.obj.{u} ell) f).mapDerivedCategory.map
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj.{u} ell) f).hom.app K) ≫
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar (c.obj.{u} ell) f)
      (CondensedRing.lowerStar (c.obj.{u} ell) f)).inv.app K ≫
    (Functor.mapDerivedCategoryNatTrans
      (CondensedRing.nativeFiniteEtaleSheetTraceNat (c.obj.{u} ell) f)).app K ≫
    (Functor.mapDerivedCategoryIdIso _).hom.app K

/-- Any reverse adjunction with the specified sheaf counit derives to the fixed
sheet-sum map.
Source: functoriality of exact derivation and its composition/unit comparisons.
(blueprint: new-det-sp-native-finite-etale-derived-trace).
Proof. Compute both sides on the localization of a homotopy complex. The
composition comparison is the identity on each term, the derived natural
transformation is the termwise counit, and the identity comparison is its
localization factor. The standard derived-adjunction counit has exactly that
formula. Localization detects equality of natural transformations. -/
theorem traceDerivedFiniteSum_eq_sheetSum (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    (b : CondensedRing.lowerStar (c.obj.{u} ell) f ⊣
      CondensedRing.upperStar (c.obj.{u} ell) f)
    (hb : b.counit = CondensedRing.nativeFiniteEtaleSheetTraceNat (c.obj.{u} ell) f)
    (K : c.derived ell Y) :
    traceDerivedFiniteSum ell c f b K = traceDerivedSheetSum ell c f K := by
  let := CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite (c.obj.{u} ell) f
  dsimp only [traceDerivedFiniteSum, traceDerivedSheetSum]
  rw [derivedCounit_formula b K, hb]

/-- The fixed geometric composite in the rank-zero finite-etale trace formula.
All factors are the published source unitor, compact-support comparison, and the
derived native sheet sum. This definition involves no adjunction-family choice.
Source: smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-derived-trace). -/
def traceFiniteEtaleSheetComposite {D : WeilConjectures.FiniteFieldDatum.{u}}
    (c : Coefficient ell) (s : SmoothDatum D) [IsFinite s.map] [Etale s.map]
    (hzero : s.dim = 0) (K : c.ctf ell s.Y.left) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj.{u} ell) s.compactification).obj
        ((c.smoothSource ell s.map s.dim).obj K.obj) ⟶ K.obj :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification
    (c.obj.{u} ell) s.compactification).map
      ((eqToIso (congrArg (fun d ↦ (c.smoothSource ell s.map d).obj K.obj) hzero)).hom ≫
        (traceSourceZero ell c s.map K.obj).hom) ≫
    traceShriekToStar ell c s.compactification
      ((actualPull (c.obj.{u} ell) s.map).obj K.obj) ≫
    traceDerivedSheetSum ell c s.map K.obj

/-- The rank-zero sheet equation at one fixed coefficient.
Source: the equality part of smooth trace clause (3).
(blueprint: new-det-sp-native-finite-etale-derived-trace). -/
def TraceFiniteEtaleSheetEquation (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) (c : Coefficient ell) : Prop :=
  ∀ (s : SmoothDatum D) [IsFinite s.map] [Etale s.map] (hzero : s.dim = 0)
    (K : c.ctf ell s.Y.left),
    (a c s).trace K = traceFiniteEtaleSheetComposite ell c s hzero K

end AlgebraicGeometry.ProEtale.PurityTransport

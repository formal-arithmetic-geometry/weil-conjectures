/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Algebra.Category.ModuleCat.CocontinuousGenerator
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingSections
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension

/-!
# Ordinary scalar extension evaluated on a w-contractible affine

Source: Hemo–Richarz–Scholbach, Section 3, equation (3.2) and Remark 3.2,
and Proposition 4.3(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale

private def pushSectionRingMap
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J Ab.{u + 1}] [HasSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf K Ab.{u + 1}) [MonObj R] [IsCommMonObj R] (V : Cᵒᵖ) :
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj R)).obj.obj V ⟶
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} K R).obj.obj
      (F.op.obj V) := by
  let P := ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor.obj
    ((sheafToPresheaf J Ab.{u + 1}).mapCommMon.obj
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).mapCommMon.obj
        (CommMon.mk R)))).obj V
  let Q := ((Monoidal.commMonFunctorCategoryEquivalence Dᵒᵖ Ab.{u + 1}).functor.obj
    ((sheafToPresheaf K Ab.{u + 1}).mapCommMon.obj (CommMon.mk R))).obj (F.op.obj V)
  let f : P.X ⟶ Q.X := 𝟙 _
  letI : IsMonHom f := by
    constructor
    · change _ ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1})).app V ≫
          ((Functor.LaxMonoidal.ε (F.sheafPushforwardContinuous Ab.{u + 1} J K)).hom.app V ≫
            (η[R]).hom.app (F.op.obj V)) =
        (Functor.LaxMonoidal.ε (sheafToPresheaf K Ab.{u + 1})).app (F.op.obj V) ≫
          (η[R]).hom.app (F.op.obj V)
      rw [← Category.assoc,
        Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
    · change _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
      rw [Category.comp_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
      change (Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
          ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj R)
          ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj R)).app V ≫
          ((Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous Ab.{u + 1} J K) R R).hom.app V ≫
            (μ[R]).hom.app (F.op.obj V)) =
        (Functor.LaxMonoidal.μ (sheafToPresheaf K Ab.{u + 1}) R R).app (F.op.obj V) ≫
          (μ[R]).hom.app (F.op.obj V)
      rw [← Category.assoc,
        Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app]
  exact InternalAbelianSheafModule.commMonToRing.map
    (CommMon.homMk (A := P) (B := Q) (Mon.Hom.mk f))

private def sectionScalarMap
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {R S : Sheaf J Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (a : R ⟶ S) [IsMonHom a] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf J Ab.{u + 1}).mapCommMon.map
        (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.Hom.mk' a))))
      InternalAbelianSheafModule.commMonToRing⟩

private def coefficientInsertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt) :
    (condensedSectionRing Λ).obj.obj
      (op ((connectedComponentsAlong (toSpecZ X)).obj U)) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (condensedRingObj Λ X)).obj.obj (op U) := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).IsContinuous
      (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : adj.IsMonoidal := Adjunction.isMonoidal_comp _ _
  let etaMap := adj.unitAlgHom Λ
  let a := sectionScalarMap (coherentTopology Profinite.{u}) etaMap
  let S := (connectedComponentsAlong (toSpecZ X)).obj U
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  exact a.hom.app (op S) ≫
    pushSectionRingMap (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
      profiniteToProEt ((lowerStar Ab.{u + 1} (toSpecZ X)).obj
        (condensedRingObj Λ X)) (op S) ≫
    pushSectionRingMap (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X))
      (condensedRingObj Λ X) (op (profiniteToProEt.obj S)) ≫
    R.obj.map ((connectedComponentsAlongAdjunction (toSpecZ X)).unit.app U).op

private theorem coefficientInsertion_apply
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt)
    (r : (condensedSectionRing Λ).obj.obj
      (op ((connectedComponentsAlong (toSpecZ X)).obj U))) :
    coefficientInsertion Λ X U r =
      ((upperStarFromPoint X).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction (toSpecZ X)).unit.app U).op
        (((upperStarFromPointAlongAdjunction (toSpecZ X)).unit.app Λ).hom.app
          (op ((connectedComponentsAlong (toSpecZ X)).obj U)) r) := rfl

private theorem coefficientInsertion_global
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt)
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    coefficientInsertion Λ X U
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        s.hom).app (op ((connectedComponentsAlong (toSpecZ X)).obj U)) (ULift.up 1)) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
        (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
          (upperStarFromPoint X).map s).hom).app (op U) (ULift.up 1) := by
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : a.IsMonoidal := Adjunction.isMonoidal_comp _ _
  let G := lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar
  let k := Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s
  have hu : a.unit.app (𝟙_ _) = Functor.LaxMonoidal.ε G ≫
      G.map (Functor.LaxMonoidal.ε (upperStarFromPoint X)) := by
    have h := NatTrans.IsMonoidal.unit (τ := a.unit)
    change 𝟙 _ ≫ a.unit.app (𝟙_ _) =
      Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε (upperStarFromPoint X)) at h
    simpa only [Category.id_comp] using h
  have hn : s ≫ a.unit.app Λ = Functor.LaxMonoidal.ε G ≫ G.map k := by
    have h := a.unit.naturality s
    change s ≫ a.unit.app Λ = a.unit.app (𝟙_ _) ≫ G.map ((upperStarFromPoint X).map s) at h
    rw [h, hu, Category.assoc, ← G.map_comp]
  let S := (connectedComponentsAlong (toSpecZ X)).obj U
  have he := congrArg (fun t ↦
    (Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      t.hom).app (op S) (ULift.up 1)) hn
  change (((upperStarFromPointAlongAdjunction (toSpecZ X)).unit.app Λ).hom.app (op S))
      ((Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        s.hom).app (op S) (ULift.up 1)) =
    (((Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})).app
      (op S) ≫ (Functor.LaxMonoidal.ε pointLowerStar).hom.app (op S) ≫
      (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (toSpecZ X))).hom.app
        (op (profiniteToProEt.obj S)) ≫
      k.hom.app (op ((profiniteToProEtAlong (toSpecZ X)).obj S))) (ULift.up 1)) at he
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc,
    Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc] at he
  rw [coefficientInsertion_apply, he]
  exact (NatTrans.naturality_apply
    (Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫ k.hom)
      ((connectedComponentsAlongAdjunction (toSpecZ X)).unit.app U).op (ULift.up 1)).symm

private theorem coefficientInsertion_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f] :
    Function.Bijective (coefficientInsertion Λ X (Scheme.ProEt.mk f)) := by
  exact bijective_unit_app_comp_map_unit (toSpecZ X) Λ (Scheme.ProEt.mk f)
    (bijective_toSheafify_connectedComponentsAlong_of_forall_exists_retraction
      (toSpecZ X) Λ
      (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction A T) (Iso.refl _))

private def affineCoefficientIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f] :
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj
        (op (Scheme.ProEt.mk f)) ≅
      (condensedSectionRing Λ).obj.obj
        (op (Profinite.of (ConnectedComponents (PrimeSpectrum A)))) := by
  have : IsIso (coefficientInsertion Λ X (Scheme.ProEt.mk f)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (coefficientInsertion_bijective Λ X A f)
  let d : (connectedComponentsAlong (toSpecZ X)).obj (Scheme.ProEt.mk f) ≅
      Profinite.of (ConnectedComponents (PrimeSpectrum A)) :=
    connectedComponentsFunctor.mapIso (Scheme.ΓSpecIso (CommRingCat.of A)).symm.op
  exact ((condensedSectionRing Λ).obj.mapIso d.op ≪≫
    asIso (coefficientInsertion Λ X (Scheme.ProEt.mk f))).symm
-- The regular-module comparison and its compatibility with scalar endomorphisms.

private def sectionUnitIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.obj
      (Mod.regular R) ≅
      SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)) := by
  let i : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.obj
      (Mod.regular R)).val ≅
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R))).val :=
    PresheafOfModules.isoMk
      (fun _ ↦ ModuleCat.isoMk (Iso.refl _) (by intro r; ext x; rfl))
      (by intro U V f; rfl)
  exact { hom := ⟨i.hom⟩, inv := ⟨i.inv⟩
          hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
          inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }

section ScalarRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

set_option hygiene false in
/-- The condensed scalar ring `Λ(*)`. -/
local notation "A" => condensedScalarRing Λ

set_option hygiene false in
/-- The condensed section ring sheaf of `Λ`. -/
local notation "B" => condensedSectionRing Λ

variable (adj : (condensedScalarExtensionModel Λ).E ⊣ SheafOfModules.restrictScalars.{u + 1}
  ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (condensedScalarMap Λ)))

private theorem constantScalarValue (V : Profinite.{u}ᵒᵖ) (r : condensedScalarRing Λ) :
    (condensedScalarMap Λ).hom.app V
        ((realizationRingUnit.{u + 1, u} (coherentTopology Profinite.{u}) (condensedScalarRing
          Λ)).app V r) =
      (condensedSectionRing Λ).obj.map (terminal.from V.unop).op r := by
  let a := constantPresheafAdj CommRingCat.{u + 1}
    (terminalIsTerminal (C := Profinite.{u}))
  let b := sheafificationAdjunction (coherentTopology Profinite.{u}) CommRingCat.{u + 1}
  have h : (toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (condensedScalarRing Λ))) ≫
      (condensedScalarMap Λ).hom = a.counit.app (condensedSectionRing Λ).obj := by
    change b.unit.app _ ≫ (sheafToPresheaf _ _).map ((a.comp b).counit.app _) = _
    erw [Adjunction.comp_counit_app, Functor.map_comp,
      ← Category.assoc,
      b.unit_naturality (a.counit.app (condensedSectionRing Λ).obj), Category.assoc,
      b.right_triangle_components, Category.comp_id]
  exact congrArg (fun f ↦ f.app V r) h

private def scalarSection (r : condensedScalarRing Λ) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ := by
  let R := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)
  exact (Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u}) R
    (fun V ↦ (R.obj.map (terminal.from V.unop).op).hom)
    (by
      intro V W f r
      have h : (terminal.from V.unop).op ≫ f = (terminal.from W.unop).op := by
        apply Quiver.Hom.unop_inj
        exact terminalIsTerminal.hom_ext _ _
      rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp, h]
      ) r).hom

private theorem scalarSection_value (r : condensedScalarRing Λ) (V : Profinite.{u}ᵒᵖ) :
    ((Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) ≫
      (scalarSection Λ r).hom).app V (ULift.up 1) =
      (condensedSectionRing Λ).obj.map (terminal.from V.unop).op r := by
  let R := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)
  have h := Sheaf.ε_comp_ringHomΓSheafCompose_hom (coherentTopology Profinite.{u}) R
    (fun V ↦ (R.obj.map (terminal.from V.unop).op).hom)
    (by
      intro V W f r
      have h : (terminal.from V.unop).op ≫ f = (terminal.from W.unop).op := by
        apply Quiver.Hom.unop_inj
        exact terminalIsTerminal.hom_ext _ _
      rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp, h]
      ) r
  apply (congrArg (fun f ↦ f.app V (ULift.up 1)) h).trans
  change ((1 : ℤ) : R.obj.obj V) * _ = _
  rw [Int.cast_one, _root_.one_mul]
  rfl

private abbrev realize : ModuleCat.{u + 1} A ⥤
    SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)) :=
  commutativeSiteConstantModuleFunctor.{u + 1, u}
    (coherentTopology Profinite.{u}) A ⋙ (condensedScalarExtensionModel Λ).E

private abbrev generator (M : ModuleCat.{u + 1} A) (V : Profinite.{u}ᵒᵖ) (a : M) :
    ((realize Λ).obj M).val.obj V :=
  ((adj).unit.app
    ((commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u}) A).obj
      M)).val.app V
      (ConstantScalarRealization.constantSection (coherentTopology Profinite.{u}) M V a)

private theorem generator_map (M : ModuleCat.{u + 1} A) {V W : Profinite.{u}ᵒᵖ}
    (f : V ⟶ W) (a : M) :
    ((realize Λ).obj M).val.map f (generator Λ adj M V a) =
      generator Λ adj M W a := by
  let eta := (adj).unit.app
    ((commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u}) A).obj M)
  have h := PresheafOfModules.naturality_apply eta.val f
    (ConstantScalarRealization.constantSection (coherentTopology Profinite.{u}) M V a)
  change eta.val.app W
    (((commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u}) A).obj
      M).val.map f
      (ConstantScalarRealization.constantSection (coherentTopology Profinite.{u}) M V a)) = _ at h
  rw [ConstantScalarRealization.constantSection_map] at h
  exact h.symm

private def oneMap : SheafOfModules.unit ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B) ⟶
    (realize Λ).obj (ModuleCat.of A A) :=
  (SheafOfModules.unitHomEquiv _).symm
    ⟨fun V ↦ generator Λ adj (ModuleCat.of A A) V 1,
      fun f ↦ generator_map Λ adj (ModuleCat.of A A) f 1⟩

private theorem oneMap_one (V : Profinite.{u}ᵒᵖ) :
    (oneMap Λ adj).val.app V (1 : (condensedSectionRing Λ).obj.obj V) =
      generator Λ adj (ModuleCat.of A A) V 1 := by
  change (1 : (condensedSectionRing Λ).obj.obj V) • generator Λ adj (ModuleCat.of A A) V 1 = _
  exact one_smul _ _

private theorem oneMap_isIso : IsIso (oneMap Λ adj) := by
  have := (realizationRingUnit_locallyBijective.{u + 1, u} (coherentTopology Profinite.{u}) A).1
  have := (realizationRingUnit_locallyBijective.{u + 1, u} (coherentTopology Profinite.{u}) A).2
  let K := (commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u})
    A).obj (ModuleCat.of A A)
  let e (N : SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) : ((realize Λ).obj (ModuleCat.of A
        A) ⟶ N) ≃ N.sections :=
    ((adj.homEquiv K N).trans
      (PresheafOfModules.sheafificationHomEquiv.{u + 1, u, u + 1, u + 1} (realizationRingUnit.{u
        + 1, u} (coherentTopology Profinite.{u}) A))).trans
        (PresheafOfModules.unitHomEquiv _)
  have he (N : SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) (f : (realize Λ).obj (ModuleCat.of A
        A) ⟶ N) :
      e N f = N.unitHomEquiv (oneMap Λ adj ≫ f) := by
    apply PresheafOfModules.sections_ext
    intro V
    dsimp only [e, Equiv.trans_apply]
    change ((PresheafOfModules.sheafificationHomEquiv.{u + 1, u, u + 1, u + 1}
      (realizationRingUnit.{u + 1, u} (coherentTopology Profinite.{u}) A))
      (adj.homEquiv K N f)).app V (1 : A) =
        f.val.app V ((oneMap Λ adj).val.app V (1 : (condensedSectionRing Λ).obj.obj V))
    rw [oneMap_one, Adjunction.homEquiv_unit]
    rfl
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hf : (fun f ↦ oneMap Λ adj ≫ f) = N.unitHomEquiv.symm ∘ e N := by
    funext f
    exact N.unitHomEquiv.injective (by simp only [Function.comp_apply,
      Equiv.apply_symm_apply, he])
  rw [hf]
  exact N.unitHomEquiv.symm.bijective.comp (e N).bijective

private theorem generator_naturality {M N : ModuleCat.{u + 1} A} (f : M ⟶ N)
    (V : Profinite.{u}ᵒᵖ) (a : M) :
    ((realize Λ).map f).val.app V (generator Λ adj M V a) =
      generator Λ adj N V (f a) := by
  have h := congrArg (fun k ↦ k.val.app V
    (ConstantScalarRealization.constantSection (coherentTopology Profinite.{u}) M V a))
    ((adj).unit_naturality
      ((commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u}) A).map f))
  change ((realize Λ).map f).val.app V (generator Λ adj M V a) =
    ((adj).unit.app
      ((commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u}) A).obj
        N)).val.app V
        (((commutativeSiteConstantModuleFunctor.{u + 1, u} (coherentTopology Profinite.{u})
          A).map f).val.app V
          (ConstantScalarRealization.constantSection (coherentTopology Profinite.{u}) M V a)) at h
  rw [ConstantScalarRealization.constantSection_naturality] at h
  exact h

private theorem generator_smul (M : ModuleCat.{u + 1} A) (V : Profinite.{u}ᵒᵖ) (a : A) (m : M) :
    generator Λ adj M V (a • m) =
      (condensedScalarMap Λ).hom.app V ((realizationRingUnit.{u + 1, u} (coherentTopology
        Profinite.{u}) A).app V a) • generator Λ adj M V m := by
  unfold generator
  rw [ConstantScalarRealization.constantSection_smul, map_smul]
  rfl

private def scalarEnd (r : condensedScalarRing Λ) :
    SheafOfModules.unit ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)) ⟶
    SheafOfModules.unit ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)) :=
  (SheafOfModules.unitHomEquiv _).symm
    ⟨fun V ↦ (condensedSectionRing Λ).obj.map (terminal.from V.unop).op r,
      fun {V W} f ↦ by
        change (condensedSectionRing Λ).obj.map f
          ((condensedSectionRing Λ).obj.map (terminal.from V.unop).op r) = _
        have h : (terminal.from V.unop).op ≫ f = (terminal.from W.unop).op := by
          apply Quiver.Hom.unop_inj
          exact terminalIsTerminal.hom_ext _ _
        rw [← ConcreteCategory.comp_apply, ← (condensedSectionRing Λ).obj.map_comp, h]⟩

private theorem scalarEnd_one (r : condensedScalarRing Λ) (V : Profinite.{u}ᵒᵖ) :
    (scalarEnd Λ r).val.app V (1 : (condensedSectionRing Λ).obj.obj V) =
      (condensedSectionRing Λ).obj.map (terminal.from V.unop).op r := by
  change (1 : (condensedSectionRing Λ).obj.obj V) •
    ((condensedSectionRing Λ).obj.map (terminal.from V.unop).op r) = _
  exact one_smul _ _

private theorem oneMap_scalar (r : condensedScalarRing Λ) :
    oneMap Λ adj ≫ (realize Λ).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r)) =
      scalarEnd Λ r ≫ oneMap Λ adj := by
  apply (SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro V
  change ((realize Λ).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r))).val.app V
      ((oneMap Λ adj).val.app V (1 : (condensedSectionRing Λ).obj.obj V)) =
    (oneMap Λ adj).val.app V ((scalarEnd Λ r).val.app V (1 : (condensedSectionRing Λ).obj.obj V))
  rw [oneMap_one, generator_naturality, scalarEnd_one]
  change generator Λ adj (ModuleCat.of A A) V (1 * r) = _
  rw [_root_.one_mul]
  calc
    _ = (condensedSectionRing Λ).obj.map (terminal.from V.unop).op r •
        generator Λ adj (ModuleCat.of A A) V 1 := by
      simpa only [smul_eq_mul, _root_.mul_one, constantScalarValue] using
        generator_smul Λ adj (ModuleCat.of A A) V r 1
    _ = _ := by
      simpa only [smul_eq_mul, _root_.mul_one, oneMap_one] using
        ((oneMap Λ adj).val.app V).hom.map_smul
          ((condensedSectionRing Λ).obj.map (terminal.from V.unop).op r) (1 :
            (condensedSectionRing Λ).obj.obj V) |>.symm

private theorem sectionRegular_scalar (r : condensedScalarRing Λ) :
    (sectionUnitIso
        (coherentTopology Profinite.{u}) Λ).inv ≫
      (InternalAbelianSheafModule.sectionModuleEquivalence
        (coherentTopology Profinite.{u}) Λ).functor.map
          (Mod.regularEndRingHom (Γ.ofHom (scalarSection Λ r))) =
    scalarEnd Λ r ≫ (sectionUnitIso
        (coherentTopology Profinite.{u}) Λ).inv := by
  apply (SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro V
  change (Mod.regularEndRingHom (Γ.ofHom (scalarSection Λ r))).hom.hom.app V
      (1 : (condensedSectionRing Λ).obj.obj V) =
    (scalarEnd Λ r).val.app V (1 : (condensedSectionRing Λ).obj.obj V)
  rw [scalarEnd_one]
  have h := Mod.one_comp_regularLift_regular (scalarSection Λ r)
  exact (congrArg (fun q ↦
    (Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      q.hom).app V (ULift.up 1)) h).trans (scalarSection_value Λ r V)

private def internalOneIso : Mod.regular Λ ≅
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ).inverse.obj
        ((realize Λ).obj (ModuleCat.of A A)) := by
  have : IsIso (oneMap Λ adj) := oneMap_isIso Λ adj
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  exact e.unitIso.app _ ≪≫ e.inverse.mapIso
    (sectionUnitIso (coherentTopology Profinite.{u}) Λ ≪≫ asIso (oneMap Λ adj))

private theorem internalOneIso_scalar (r : condensedScalarRing Λ) :
    (internalOneIso Λ adj).hom ≫
        (InternalAbelianSheafModule.sectionModuleEquivalence
          (coherentTopology Profinite.{u}) Λ).inverse.map
            ((realize Λ).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r))) =
      Mod.regularEndRingHom (Γ.ofHom (scalarSection Λ r)) ≫ (internalOneIso Λ adj).hom := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  let e₀ := sectionUnitIso (coherentTopology Profinite.{u}) Λ
  let t := (realize Λ).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r))
  let q := Mod.regularEndRingHom (Γ.ofHom (scalarSection Λ r))
  have hr := sectionRegular_scalar Λ r
  change e₀.inv ≫ e.functor.map q = scalarEnd Λ r ≫ e₀.inv at hr
  have hs : e.functor.map q ≫ e₀.hom = e₀.hom ≫ scalarEnd Λ r := by
    calc
      _ = e₀.hom ≫ (e₀.inv ≫ e.functor.map q) ≫ e₀.hom := by simp
      _ = _ := by rw [hr]; simp only [Category.assoc, e₀.inv_hom_id, Category.comp_id]
  have hk : e.functor.map q ≫ (e₀.hom ≫ oneMap Λ adj) =
      (e₀.hom ≫ oneMap Λ adj) ≫ t := by
    dsimp only [t]
    simp only [Category.assoc]
    rw [← Category.assoc, hs, Category.assoc, ← oneMap_scalar]
  change (e.unitIso.app _).hom ≫ e.inverse.map (e₀.hom ≫ oneMap Λ adj) ≫
      e.inverse.map t = q ≫ (e.unitIso.app _).hom ≫
        e.inverse.map (e₀.hom ≫ oneMap Λ adj)
  have hn : (e.unitIso.app (Mod.regular Λ)).hom ≫ e.inverse.map (e.functor.map q) =
      q ≫ (e.unitIso.app (Mod.regular Λ)).hom := by
    exact (e.unitIso.hom.naturality q).symm
  calc
    _ = (e.unitIso.app _).hom ≫ e.inverse.map ((e₀.hom ≫ oneMap Λ adj) ≫ t) := by
      simp only [e.inverse.map_comp, Category.assoc]
    _ = (e.unitIso.app _).hom ≫
        e.inverse.map (e.functor.map q ≫ (e₀.hom ≫ oneMap Λ adj)) := by rw [hk]
    _ = ((e.unitIso.app _).hom ≫ e.inverse.map (e.functor.map q)) ≫
        e.inverse.map (e₀.hom ≫ oneMap Λ adj) := by
      simp only [e.inverse.map_comp, Category.assoc]
    _ = _ := by rw [hn, Category.assoc]; rfl

private abbrev affineRealization (X : Scheme.{u}) (U : X.ProEt) :
    ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1}
      ((InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
        (condensedRingObj Λ X)).obj.obj (op U)) :=
  (realize Λ) ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ).inverse ⋙
    (upperStarFromPoint X).mapMod Λ ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor ⋙
    SheafOfModules.evaluation _ (op U)

private def affineOneIso (X : Scheme.{u}) (U : X.ProEt) :
    (affineRealization Λ X U).obj (ModuleCat.of A A) ≅
      ModuleCat.of
        ((InternalAbelianSheafModule.sectionRingSheaf
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj (op U))
        ((InternalAbelianSheafModule.sectionRingSheaf
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj (op U)) :=
  (SheafOfModules.evaluation _ (op U)).mapIso
    ((InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.mapIso
        (((upperStarFromPoint X).mapMod Λ).mapIso (internalOneIso Λ adj)).symm ≪≫
      sectionUnitIso
        (Scheme.ProEt.topology X) (condensedRingObj Λ X))

private theorem affineOneIso_scalar (X : Scheme.{u}) (U : X.ProEt)
    (r : condensedScalarRing Λ) :
    (affineRealization Λ X U).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r))
          ((affineOneIso Λ adj X U).inv 1) =
      ((Functor.LaxMonoidal.ε (sheafToPresheaf
        (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
          (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
            (upperStarFromPoint X).map (scalarSection Λ r)).hom).app (op U) (ULift.up 1)) •
        (affineOneIso Λ adj X U).inv 1 := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have := Functor.additive_of_preserves_binary_products (upperStarFromPoint X)
  let P := (upperStarFromPoint X).mapMod Λ
  have h := congrArg P.map (internalOneIso_scalar Λ adj r)
  rw [P.map_comp, P.map_comp] at h
  rw [Functor.mapMod_map_regularEndRingHom] at h
  have hv := congrArg (fun q ↦ q.hom.hom.app (op U)
    (1 : (InternalAbelianSheafModule.sectionRingSheaf
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj (op U))) h
  change (affineRealization Λ X U).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton A A r))
        ((affineOneIso Λ adj X U).inv 1) =
    ((affineOneIso Λ adj X U).inv)
      ((Mod.regularEndRingHom (Γ.mapFunctor (upperStarFromPoint X)
        (Γ.ofHom (scalarSection Λ r)))).hom.hom.app (op U)
        (1 : (InternalAbelianSheafModule.sectionRingSheaf
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj (op U))) at hv
  rw [← (affineOneIso Λ adj X U).inv.hom.map_smul]
  apply hv.trans
  congr 1
  have h1 := Mod.one_comp_regularLift_regular
    (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map (scalarSection Λ r))
  have h2 := congrArg (fun q ↦
    (Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      q.hom).app (op U) (ULift.up 1)) h1
  change (Mod.regularEndRingHom (Γ.mapFunctor (upperStarFromPoint X)
    (Γ.ofHom (scalarSection Λ r)))).hom.hom.app (op U)
      (1 : (InternalAbelianSheafModule.sectionRingSheaf
        (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj (op U)) = _ at h2
  change _ = _ * (1 : (InternalAbelianSheafModule.sectionRingSheaf
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)).obj.obj (op U))
  rw [_root_.mul_one]
  exact h2

end ScalarRealization

private theorem cocontinuousScalarIso
    {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : ModuleCat.{v} R ⥤ ModuleCat.{v} S) [F.Additive]
    [PreservesColimitsOfSize.{v, v} F]
    (e : F.obj (ModuleCat.of R R) ≅ ModuleCat.of S S)
    (hs : ∀ r : R,
      F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R R r)) (e.inv 1) = φ r • e.inv 1) :
    Nonempty (F ≅ ModuleCat.extendScalars φ) := by
  have atOne {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
      (g : M ⟶ (ModuleCat.restrictScalars φ).obj N) (m : M) :
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ g
        ((1 : S) ⊗ₜ[R, φ] m) = g m := by
    exact congrArg (fun f : M ⟶ (ModuleCat.restrictScalars φ).obj N ↦ f m)
      ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv φ).apply_symm_apply g)
  let j (M : ModuleCat.{v} R) : M ⟶ (ModuleCat.restrictScalars φ).obj (F.obj M) :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj (F.obj M))
      { toFun := fun m ↦ F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))
          (e.inv 1)
        map_add' := by
          intro m n
          rw [LinearMap.toSpanSingleton_add, ModuleCat.ofHom_add, F.map_add]
          rfl
        map_smul' := by
          intro r m
          have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R M (r • m)) =
              ModuleCat.ofHom (LinearMap.toSpanSingleton R R r) ≫
                ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro a
            simp [LinearMap.toSpanSingleton_apply, _root_.mul_comm, smul_smul]
          rw [h, F.map_comp]
          change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))
            (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R R r)) (e.inv 1)) = _
          rw [hs, map_smul]
          rfl }
  let α : ModuleCat.extendScalars φ ⟶ F :=
    { app := fun M ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ (j M)
      naturality := by
        intro M N f
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ (j N)).hom
            ((1 : S) ⊗ₜ[R, φ] f m) =
          F.map f ((ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ (j M)).hom
            ((1 : S) ⊗ₜ[R, φ] m))
        rw [atOne, atOne]
        change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f m)))
            (e.inv 1) =
          F.map f (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)) (e.inv 1))
        have hspan : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f m)) =
            ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) ≫ f := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro a
          exact (f.hom.map_smul a m).symm
        rw [hspan, F.map_comp]
        rfl }
  let := φ.toAlgebra
  let t : (ModuleCat.extendScalars φ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
    (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
  have hα : α.app (ModuleCat.of R R) = t.hom ≫ e.inv := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro r
    change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ
      (j (ModuleCat.of R R))).hom ((1 : S) ⊗ₜ[R, φ] r) = _
    rw [atOne]
    change F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R R r)) (e.inv 1) =
      e.inv (r • (1 : S))
    rw [hs]
    change φ r • e.inv 1 = e.inv (φ r * 1)
    rw [_root_.mul_one]
    simpa only [smul_eq_mul, _root_.mul_one] using (e.inv.hom.map_smul (φ r) 1).symm
  have hr : IsIso (α.app (ModuleCat.of R R)) := by rw [hα]; infer_instance
  have hi (M : ModuleCat.{v} R) : IsIso (α.app M) :=
    ModuleCat.isIso_app_of_rankOne α hr M
  let : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨(asIso α).symm⟩
-- Colimit preservation of each factor in the actual realization functor.

private theorem constant_cocontinuous (R : Type (u + 1)) [CommRing R] :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (commutativeSiteConstantModuleFunctor.{u + 1, u}
        (coherentTopology Profinite.{u}) R) := by
  let P := siteConstantModulePresheafGeneral (C := Profinite.{u}) R
  have : PreservesColimitsOfSize.{u + 1, u + 1} P := by
    constructor
    intro K _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  have := (realizationRingUnit_locallyBijective (coherentTopology Profinite.{u}) R).1
  have := (realizationRingUnit_locallyBijective (coherentTopology Profinite.{u}) R).2
  change PreservesColimitsOfSize.{u + 1, u + 1}
    (P ⋙ PresheafOfModules.sheafification
      (realizationRingUnit (coherentTopology Profinite.{u}) R))
  infer_instance

private theorem affine_realization_cocontinuous
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f] :
    PreservesColimitsOfSize.{u + 1, u + 1}
      ((commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u})
          (condensedScalarRing Λ) ⋙ (condensedScalarExtensionModel Λ).E) ⋙
        (InternalAbelianSheafModule.sectionModuleEquivalence
          (coherentTopology Profinite.{u}) Λ).inverse ⋙
        (upperStarFromPoint X).mapMod Λ ⋙
        (InternalAbelianSheafModule.sectionModuleEquivalence
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor ⋙
        SheafOfModules.evaluation _ (op (Scheme.ProEt.mk f))) := by
  have := constant_cocontinuous (condensedScalarRing Λ)
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (condensedScalarMap Λ)
  obtain ⟨adj, _⟩ := h (condensedScalarExtensionModel Λ).E
    (condensedScalarExtensionModel Λ).obj_eq (condensedScalarExtensionModel Λ).map_eq
  have : (condensedScalarExtensionModel Λ).E.IsLeftAdjoint := adj.isLeftAdjoint
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : a.IsMonoidal := Adjunction.isMonoidal_comp _ _
  have : ((upperStarFromPoint X).mapMod Λ).IsLeftAdjoint :=
    (a.mapModAdjunction Λ).isLeftAdjoint
  let W := Scheme.ProEt.mk f
  have : IsAffine W.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W :=
    Scheme.ProEt.isWeaklyContractible_of_iso (R := CommRingCat.of A) (Iso.refl _)
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.evaluation
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
              (Scheme.ProEt.topology X) (condensedRingObj Λ X))) (op W)) :=
    (Scheme.ProEt.affine_weaklyContractible_evaluation_colimits X _ W
      (fun _ _ φ hφ ↦ by
        have := hφ
        exact hW φ ((Sheaf.isLocallySurjective_iff_epi φ).mpr inferInstance))).2.2.1
  infer_instance

private theorem affineCoefficientIso_scalar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f] (r : condensedScalarRing Λ) :
    (affineCoefficientIso Λ X A f).inv
      ((condensedSectionRing Λ).obj.map
        (terminal.from (Profinite.of (ConnectedComponents (PrimeSpectrum A)))).op r) =
    (Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (scalarSection Λ r)).hom).app
          (op (Scheme.ProEt.mk f)) (ULift.up 1) := by
  let U := Scheme.ProEt.mk f
  let S := (connectedComponentsAlong (toSpecZ X)).obj U
  let d : S ≅ Profinite.of (ConnectedComponents (PrimeSpectrum A)) :=
    connectedComponentsFunctor.mapIso (Scheme.ΓSpecIso (CommRingCat.of A)).symm.op
  change coefficientInsertion Λ X U
    ((condensedSectionRing Λ).obj.map d.op.hom
      ((condensedSectionRing Λ).obj.map
        (terminal.from (Profinite.of (ConnectedComponents (PrimeSpectrum A)))).op r)) = _
  have hd : (terminal.from (Profinite.of (ConnectedComponents (PrimeSpectrum A)))).op ≫
      d.op.hom = (terminal.from S).op := by
    apply Quiver.Hom.unop_inj
    exact terminalIsTerminal.hom_ext _ _
  have hx : (condensedSectionRing Λ).obj.map d.op.hom
      ((condensedSectionRing Λ).obj.map
        (terminal.from (Profinite.of (ConnectedComponents (PrimeSpectrum A)))).op r) =
      (condensedSectionRing Λ).obj.map (terminal.from S).op r := by
    rw [← ConcreteCategory.comp_apply, ← (condensedSectionRing Λ).obj.map_comp, hd]
  erw [hx, ← scalarSection_value Λ r (op S)]
  exact coefficientInsertion_global Λ X U (scalarSection Λ r)

set_option maxHeartbeats 400000 in
-- The unification of the cocontinuous comparison with the composite realization is slow.
/-- The coefficient comparison and the ordinary, module-valued scalar comparison.
This assertion concerns modules in degree zero, without derived categories or
truncation bounds. Scalar extension uses the actual ordinary functor in the fixed
change-of-rings model.

Source: Hemo–Richarz–Scholbach, equation (3.2), Remark 3.2 and Proposition 4.3(1).
(blueprint: lem-zl-condensed-affine-ordinary-scalar-sections).

Proof: the point-basis evaluation theorem identifies the section ring of the
inverse image of Λ on Spec A with Λ(pi_0 Spec A). The comparison is constructed
in commutative rings, hence preserves the constant scalar map from Λ(*).
For an R-module M, send b tensor m to b times the image of its constant section.
This balanced map is natural and is the identity on the free rank-one module.
Ordinary scalar extension, inverse image and both module equivalences preserve
colimits. Evaluation on the affine preserves colimits by weak contractibility.
Thus the comparison is an isomorphism on arbitrary free modules, by coproducts,
and on every module, by taking a free presentation and its cokernel. Transport
along the coefficient-ring isomorphism gives precisely the displayed B-linear
comparison. This argument includes the empty affine and zero coefficient rings:
all modules over the zero section ring are zero. No flatness is assumed. -/
theorem condensed_affine_ordinary_scalar_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f] :
    ∃ e :
      (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
        (condensedRingObj Λ X)).obj.obj (op (Scheme.ProEt.mk f)) ≅
      (condensedSectionRing Λ).obj.obj
        (op (Profinite.of (ConnectedComponents (PrimeSpectrum A)))),
      Nonempty
        ((commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u})
            (condensedScalarRing Λ) ⋙ (condensedScalarExtensionModel Λ).E) ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence
            (coherentTopology Profinite.{u}) Λ).inverse ⋙
          (upperStarFromPoint X).mapMod Λ ⋙
          (InternalAbelianSheafModule.sectionModuleEquivalence
            (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor ⋙
          SheafOfModules.evaluation _ (op (Scheme.ProEt.mk f)) ⋙
          ModuleCat.restrictScalars.{u + 1} e.inv.hom ≅
          ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            ((condensedSectionRing Λ).obj.map
              (terminal.from (Profinite.of
                (ConnectedComponents (PrimeSpectrum A)))).op).hom) := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (condensedScalarMap Λ)
  obtain ⟨adj, _⟩ := h (condensedScalarExtensionModel Λ).E
    (condensedScalarExtensionModel Λ).obj_eq (condensedScalarExtensionModel Λ).map_eq
  let e := affineCoefficientIso Λ X A f
  refine ⟨e, ?_⟩
  let F := affineRealization Λ X (Scheme.ProEt.mk f) ⋙
    ModuleCat.restrictScalars.{u + 1} e.inv.hom
  have := affine_realization_cocontinuous Λ X A f
  have : (ModuleCat.restrictScalars.{u + 1} e.inv.hom).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} e.inv.hom).isLeftAdjoint
  have : PreservesColimitsOfSize.{u + 1, u + 1} F := by dsimp [F]; infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ).inverse
  have := Functor.additive_of_preserves_binary_products ((upperStarFromPoint X).mapMod Λ)
  have := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor
  have : (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) (condensedRingObj Λ X)))
          (op (Scheme.ProEt.mk f))).Additive := by
    unfold SheafOfModules.evaluation
    infer_instance
  have : F.Additive := by dsimp [F, affineRealization, realize]; infer_instance
  let i : F.obj (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)) ≅
      ModuleCat.of
        ((condensedSectionRing Λ).obj.obj
          (op (Profinite.of (ConnectedComponents (PrimeSpectrum A)))))
        ((condensedSectionRing Λ).obj.obj
          (op (Profinite.of (ConnectedComponents (PrimeSpectrum A))))) :=
    (ModuleCat.restrictScalars.{u + 1} e.inv.hom).mapIso
      (affineOneIso Λ adj X (Scheme.ProEt.mk f)) ≪≫
      ModuleCat.restrictScalarsIsoOfEquiv e.symm.commRingCatIsoToRingEquiv
  apply cocontinuousScalarIso
    ((condensedSectionRing Λ).obj.map
      (terminal.from (Profinite.of (ConnectedComponents (PrimeSpectrum A)))).op).hom F i
  intro r
  have hi : i.inv 1 = (affineOneIso Λ adj X (Scheme.ProEt.mk f)).inv 1 := by
    change (affineOneIso Λ adj X (Scheme.ProEt.mk f)).inv (e.inv (1 : _)) = _
    rw [map_one]
  rw [hi]
  change (affineRealization Λ X (Scheme.ProEt.mk f)).map
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (condensedScalarRing Λ)
      (condensedScalarRing Λ) r))
        ((affineOneIso Λ adj X (Scheme.ProEt.mk f)).inv 1) =
    e.inv
      ((condensedSectionRing Λ).obj.map
        (terminal.from (Profinite.of (ConnectedComponents (PrimeSpectrum A)))).op r) •
      (affineOneIso Λ adj X (Scheme.ProEt.mk f)).inv 1
  rw [affineCoefficientIso_scalar, affineOneIso_scalar]

end AlgebraicGeometry.ProEtale

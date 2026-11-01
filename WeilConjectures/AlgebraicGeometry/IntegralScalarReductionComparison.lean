/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalarRealization
import all WeilConjectures.SixFunctors.ContinuousScalarFinitePresentation
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.CategoryTheory.MapModScalarExtension
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison

/-! # Actual reductions of bounded free scalar models

Source: current blueprint, sk-prop-integral-local-structure, proof step 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale

private def internalScalarAction (A : Type u) [CommRing A]
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) (a : A) (x : N.X) : N.X :=
  (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) N.X).hom (ULift.up a ⊗ₜ[ℤ] x)

private instance internalScalarModule (A : Type u) [CommRing A]
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) : Module A N.X where
  smul := internalScalarAction A N
  one_smul x := by
    have h := congrArg (fun f ↦ f.hom (ULift.up (1 : ℤ) ⊗ₜ[ℤ] x))
      (Mod.one_act (A := AddCommGrpCat.of (ULift.{u + 1} A)) N.X)
    change internalScalarAction A N 1 x = x
    have h' : internalScalarAction A N ((1 : ℤ) : A) x = (1 : ℤ) • x := h
    simpa only [Int.cast_one, one_smul] using h'
  mul_smul a b x := by
    have h := congrArg (fun f ↦ f.hom ((ULift.up a ⊗ₜ[ℤ] ULift.up b) ⊗ₜ[ℤ] x))
      (Mod.mul_act (A := AddCommGrpCat.of (ULift.{u + 1} A)) N.X)
    exact h
  smul_zero a := by
    change internalScalarAction A N a 0 = 0
    simp [internalScalarAction]
  zero_smul x := by
    change internalScalarAction A N 0 x = 0
    rw [internalScalarAction, show (ULift.up (0 : A) : ULift.{u + 1} A) = 0 from rfl,
      TensorProduct.zero_tmul, map_zero]
  add_smul a b x := by
    change internalScalarAction A N (a + b) x =
      internalScalarAction A N a x + internalScalarAction A N b x
    simp only [internalScalarAction, show (ULift.up (a + b) : ULift.{u + 1} A) =
      ULift.up a + ULift.up b from rfl, TensorProduct.add_tmul, map_add]
  smul_add a x y := by
    change internalScalarAction A N a (x + y) =
      internalScalarAction A N a x + internalScalarAction A N a y
    simp [internalScalarAction, TensorProduct.tmul_add]

private theorem scalarModules_essSurj (A : Type u) [CommRing A] :
    (FiniteConstantModel.scalarModules A).EssSurj := by
  constructor
  intro N
  let M := ModuleCat.of A N.X
  refine ⟨M, ⟨Mod.isoMk (Iso.refl N.X) ?_⟩⟩
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a x
  rfl

private instance scalarModules_equivalence (A : Type u) [CommRing A] :
    (FiniteConstantModel.scalarModules A).IsEquivalence := by
  let : (FiniteConstantModel.scalarModules A).Full :=
    ContinuousScalarPresentation.scalarModules_full A
  let : (FiniteConstantModel.scalarModules A).Faithful :=
    ContinuousScalarPresentation.scalarModules_faithful A
  let : (FiniteConstantModel.scalarModules A).EssSurj := scalarModules_essSurj A
  exact {}

private def scalarAbMap {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    AddCommGrpCat.of (ULift.{u + 1} A) ⟶ AddCommGrpCat.of (ULift.{u + 1} B) :=
  AddCommGrpCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (q.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom

private instance scalarAbMap_monHom {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) : IsMonHom (scalarAbMap q) :=
  AddCommGrpCat.isMonHom_ofHom_ringHom _

private def scalarRestrictionIso {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) :
    ModuleCat.restrictScalars.{u + 1} q ⋙ FiniteConstantModel.scalarModules A ≅
      FiniteConstantModel.scalarModules B ⋙ Mod.comap (scalarAbMap q) := by
  refine NatIso.ofComponents (fun M ↦ Mod.isoMk (Iso.refl _) ?_) ?_
  · simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a x
    rfl
  · intro M N f
    apply Mod.hom_ext
    rfl

private def scalarExtensionIso {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) :
    FiniteConstantModel.scalarModules A ⋙ Mod.extendScalars (scalarAbMap q) ≅
      ModuleCat.extendScalars.{u, u, u + 1} q ⋙ FiniteConstantModel.scalarModules B := by
  let eA := (FiniteConstantModel.scalarModules A).asEquivalence
  let eB := (FiniteConstantModel.scalarModules B).asEquivalence
  let R := eB.inverse ⋙ ModuleCat.restrictScalars.{u + 1} q
  let t : R ⋙ eA.functor ≅ Mod.comap (scalarAbMap q) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (scalarRestrictionIso q) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eB.counitIso _ ≪≫
      Functor.leftUnitor _
  let r : R ≅ Mod.comap (scalarAbMap q) ⋙ eA.inverse :=
    (Functor.rightUnitor R).symm ≪≫ Functor.isoWhiskerLeft R eA.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight t _
  let a := eA.toAdjunction.comp (Mod.extendRestrictAdjunction (scalarAbMap q))
  let b := ((ModuleCat.extendRestrictScalarsAdj.{u + 1} q).comp eB.toAdjunction).ofNatIsoRight r
  exact a.leftAdjointUniq b

private instance constantPresheafBraided :
    (Functor.const Profinite.{u}ᵒᵖ :
      Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}).Braided where
  braided M N := by
    apply NatTrans.ext
    funext V
    change (𝟙 (M ⊗ N)) ≫ (β_ M N).hom = (β_ M N).hom ≫ (𝟙 (N ⊗ M))
    simp only [Category.id_comp, Category.comp_id]

private instance constantSheafBraided :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).Braided :=
  inferInstanceAs (Functor.const Profinite.{u}ᵒᵖ ⋙
    presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).Braided

private def constantScalarExtensionIso {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) :
    Mod.extendScalars (scalarAbMap q) ⋙
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} B)) ≅
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙
      Mod.extendScalars
        ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
          (scalarAbMap q)) := by
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let := adj.rightAdjointLaxMonoidal
  exact Functor.mapModExtendScalarsIso _ _ adj (scalarAbMap q)

private def continuousRingMap {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) :
    Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousCoefficientRingSheaf B :=
  ⟨{ app := fun _ ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        ((q.compLeftContinuous _ hq).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

private abbrev continuousAbMap {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) :
    Profinite.continuousCoefficientRingObj A ⟶
      Profinite.continuousCoefficientRingObj B :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (continuousRingMap q hq)

private instance continuousAbMap_monHom {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) : IsMonHom (continuousAbMap q hq) :=
  inferInstanceAs (IsMonHom
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (continuousRingMap q hq)))

private theorem scalarContinuous_square {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) :
    FiniteConstantModel.scalarToContinuous A ≫ continuousAbMap q hq =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (scalarAbMap q) ≫
        FiniteConstantModel.scalarToContinuous B := by
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right]
  change _ = adj.homEquiv _ _
    ((presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map (scalarAbMap q)) ≫ _)
  rw [adj.homEquiv_naturality_left]
  dsimp only [adj]
  simp only [FiniteConstantModel.scalarToContinuous, Equiv.apply_symm_apply]
  rfl

private def continuousScalarExtensionIso {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) :
    continuousScalarFunctor A ⋙ Mod.extendScalars (continuousAbMap q hq) ≅
      ModuleCat.extendScalars.{u, u, u + 1} q ⋙ continuousScalarFunctor B := by
  let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let φA := FiniteConstantModel.scalarToContinuous A
  let φB := FiniteConstantModel.scalarToContinuous B
  let r := continuousAbMap q hq
  let c := C.map (scalarAbMap q)
  let h : φA ≫ r = c ≫ φB := scalarContinuous_square q hq
  let e : Mod.extendScalars (φA ≫ r) ≅ Mod.extendScalars (c ≫ φB) :=
    Mod.extendScalarsIsoOfEq h
  let t : Mod.extendScalars φA ⋙ Mod.extendScalars r ≅
      Mod.extendScalars c ⋙ Mod.extendScalars φB :=
    (Mod.extendScalarsComp φA r).symm ≪≫ e ≪≫ Mod.extendScalarsComp c φB
  change (FiniteConstantModel.scalarModules A ⋙
      (C.mapMod (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙ Mod.extendScalars φA)) ⋙
      Mod.extendScalars r ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ t ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (constantScalarExtensionIso q).symm _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarExtensionIso q) _ ≪≫
    Functor.associator _ _ _

private def universalArrowIso
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (A : C) (M : D) (p : A ⟶ R.obj M)
    (hp : ∀ N : D, Function.Bijective fun g : M ⟶ N ↦ p ≫ R.map g) :
    L.obj A ≅ M := by
  let f : L.obj A ⟶ M := (adj.homEquiv _ _).symm p
  let g := Classical.choose ((hp (L.obj A)).surjective (adj.unit.app A))
  have hg : p ≫ R.map g = adj.unit.app A :=
    Classical.choose_spec ((hp (L.obj A)).surjective (adj.unit.app A))
  have hf : adj.unit.app A ≫ R.map f = p := by
    simpa only [Adjunction.homEquiv_unit] using (adj.homEquiv _ _).apply_symm_apply p
  have hfg : f ≫ g = 𝟙 (L.obj A) := by
    apply (adj.homEquiv A (L.obj A)).injective
    rw [Adjunction.homEquiv_naturality_right]
    change ((adj.homEquiv A M) ((adj.homEquiv A M).symm p)) ≫ R.map g = _
    rw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit, R.map_id]
    exact hg.trans (Category.comp_id (adj.unit.app A)).symm
  have hgf : g ≫ f = 𝟙 M := by
    apply (hp M).injective
    simp only [R.map_comp, ← Category.assoc, hg, R.map_id, Category.comp_id]
    exact hf
  exact ⟨f, g, hfg, hgf⟩

private def rawQuotientIso
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hflat : ∀ i : ℤ, Module.Flat A (P.X i))
    (M : DerivedCategory (ModuleCat.{u} B))
    (p : DerivedCategory.Q.obj P ⟶ (ModuleCat.restrictScalars q).mapDerivedCategory.obj M)
    (hp : ∀ N : DerivedCategory (ModuleCat.{u} B),
      Function.Bijective fun g : M ⟶ N ↦
        p ≫ (ModuleCat.restrictScalars q).mapDerivedCategory.map g) :
    DerivedCategory.Q.obj
      (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) ≅ M := by
  let F := ModuleCat.extendScalars.{u, u, u} q
  let R := ModuleCat.restrictScalars.{u} q
  let : F.Additive := (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
  let : F.PreservesKFlatQuasiIso := ModuleCat.extendScalars_preservesKFlatQuasiIso q
  let adj : F.leftDerivedFunctor ⊣ R.mapDerivedCategory :=
    (ModuleCat.extendRestrictScalarsAdj q).derivedAdjunction.ofNatIsoRight
      R.rightDerivedFunctorIsoMapDerivedCategory
  let : P.IsStrictlyGE a := ha
  let : P.IsStrictlyLE b := hb
  have hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_bounded_of_flat P a b
      (fun i ↦ (ModuleCat.flat_iff_flat (P.X i)).mpr (hflat i))
  let := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let Q := (F.mapHomologicalComplex (.up ℤ)).obj P
  let e : F.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj Q :=
    (F.leftDerivedFunctor.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P)).symm ≪≫
    asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app Q
  exact e.symm ≪≫ universalArrowIso adj _ M p hp

private def pointScalarExtensionIso
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) (W : Scheme.{u}) :
    FiniteConstantModel.modelFunctor A W ⋙
      Mod.extendScalars ((upperStarFromPoint W).map (continuousAbMap q hq)) ≅
      ModuleCat.extendScalars.{u, u, u + 1} q ⋙
        FiniteConstantModel.modelFunctor B W := by
  let F := upperStarFromPoint W
  let : F.Braided :=
    { toMonoidal := inferInstance
      braided := Functor.LaxBraided.braided }
  let adj := upperStarFromPointAdjunction W
  let := adj.rightAdjointLaxMonoidal
  let : adj.IsMonoidal := by
    constructor
    · rfl
    · intro X Y; rfl
  let e := (Functor.mapModExtendScalarsIso _ _ adj (continuousAbMap q hq)).symm
  change (continuousScalarFunctor A ⋙ F.mapMod (Profinite.continuousCoefficientRingObj A)) ⋙
    Mod.extendScalars (F.map (continuousAbMap q hq)) ≅ _
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (continuousScalarExtensionIso q hq) _ ≪≫
    Functor.associator _ _ _

set_option synthInstance.maxHeartbeats 200000 in
-- Infer the countable tensor structure of the internal module category once.
private theorem free_internal_flat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (M : AdicCompletion.Modules l E W)
    (hM : Mod.IsFree (AdicCompletion.ring l E W) M) : ObjectProperty.flat M := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  let : (ObjectProperty.flat (A := AdicCompletion.Modules l E W)).IsClosedUnderLimitsOfShape
      (Discrete (Fin n)) := CochainComplex.closedUnderLimitsOfShape_discrete_flat _ _
  apply (ObjectProperty.flat).prop_of_iso e.symm
  apply ObjectProperty.prop_of_isLimit _
    (biproduct.isLimit (fun _ : Fin n ↦ Mod.regular (AdicCompletion.ring l E W)))
  intro i
  exact ObjectProperty.prop_unit _

private def uliftExtensionIso {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) :
    ModuleCat.uliftFunctor.{u + 1, u} A ⋙ ModuleCat.extendScalars.{u, u, u + 1} q ≅
      ModuleCat.extendScalars.{u, u, u} q ⋙ ModuleCat.uliftFunctor.{u + 1, u} B := by
  let := q.toAlgebra
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (ULift.moduleEquiv : ULift.{u + 1} M ≃ₗ[A] M)).trans
        (ULift.moduleEquiv : ULift.{u + 1} (B ⊗[A] M) ≃ₗ[B] B ⊗[A] M).symm).toModuleIso
  · intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b m => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private def smallScalarExtensionIso
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (q : A →+* B) (hq : Continuous q) (W : Scheme.{u}) :
    (ModuleCat.uliftFunctor.{u + 1, u} A ⋙ FiniteConstantModel.modelFunctor A W) ⋙
      Mod.extendScalars ((upperStarFromPoint W).map (continuousAbMap q hq)) ≅
      ModuleCat.extendScalars.{u, u, u} q ⋙
        (ModuleCat.uliftFunctor.{u + 1, u} B ⋙ FiniteConstantModel.modelFunctor B W) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pointScalarExtensionIso q hq W) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (uliftExtensionIso q) _ ≪≫
    Functor.associator _ _ _

private theorem modelFunctor_free
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (W : Scheme.{u}) (M : ModuleCat.{u} A)
    (hfinite : Module.Finite A M) (hfree : Module.Free A M) :
    Mod.IsFree (condensedRingObj (Profinite.continuousCoefficientRingObj A) W)
      ((ModuleCat.uliftFunctor.{u + 1, u} A ⋙
        FiniteConstantModel.modelFunctor A W).obj M) := by
  let : Module.Finite A M := hfinite
  let : Module.Free A M := hfree
  obtain ⟨r, ⟨e⟩⟩ := FiniteConstantModel.finiteFree_coordinates A (ULift.{u + 1} M)
  let F := CondensedRing.upperStarFromPointMod (Profinite.continuousCoefficientRingObj A) W
  have h : Mod.IsFree (Profinite.continuousCoefficientRingObj A)
      ((continuousScalarFunctor A).obj
        ((ModuleCat.uliftFunctor.{u + 1, u} A).obj M)) :=
    ⟨r, ⟨(continuousScalarFunctor A).mapIso e.toModuleIso.symm ≪≫
      ContinuousScalarPresentation.continuousFreeIso A r⟩⟩
  obtain ⟨r, ⟨e⟩⟩ := h
  refine ⟨r, ⟨F.mapIso e ≪≫ ?_⟩⟩
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint W) :=
    (upperStarFromPointAdjunction W).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (upperStarFromPoint W) := inferInstance
  have : PreservesBinaryBiproducts (upperStarFromPoint W) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint W).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  exact FiniteConstantModel.mapFiniteFreeIso (upperStarFromPoint W)
    (Profinite.continuousCoefficientRingObj A) r

/-- A universal scalar quotient realizes the actual derived reduction of the internal model.
Source: current blueprint, sk-prop-integral-local-structure, proof step 3
(blueprint: lem-pe-integral-scalar-reduction-comparison).

Proof: identify ordinary modules with module objects in abelian groups. Uniqueness of
left adjoints identifies extension of scalars under this equivalence. Constant-sheaf
inverse image and inverse image from the condensed point commute with extension of
scalars by the same adjunction argument. Naturality of constant functions identifies
these comparisons for the actual continuous quotient map. Universe lift commutes with
ordinary scalar tensor by the tensor product universal property. The bounded free
complex and its internal realization are K-flat. Consequently both derived extensions
are computed termwise. The universal property of p identifies the scalar quotient with
M, and exact finite scalar realization carries this identification to the asserted
isomorphism. The zero complex, zero coefficient ring, and empty scheme are included. -/
theorem integralScalarReduction_of_universal
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i))
    (n : ℕ) (M : DerivedCategory
      (ModuleCat.{u} (Padic.coefficientExtensionRing l E (n + 1))))
    (p : DerivedCategory.Q.obj P ⟶
      (ModuleCat.restrictScalars.{u}
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))).mapDerivedCategory.obj M)
    (hp : ∀ N : DerivedCategory
      (ModuleCat.{u} (Padic.coefficientExtensionRing l E (n + 1))),
      Function.Bijective fun g : M ⟶ N ↦ p ≫
        (ModuleCat.restrictScalars.{u}
          (Ideal.Quotient.mk
            (Padic.coefficientExtensionIdeal l E (n + 1)))).mapDerivedCategory.map g) :
    Nonempty
      ((AdicCompletion.derivedReduction l E W n).obj (internalPerfectScalarModel l E W P) ≅
        (integralFiniteScalarRealization l E W n).obj M) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let q : A →+* B := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
  let FA := ModuleCat.uliftFunctor.{u + 1, u} A ⋙ FiniteConstantModel.modelFunctor A W
  let FB := integralFiniteScalarFunctor l E W n
  let : (FiniteConstantModel.modelFunctor A W).Additive :=
    (((AdmissibleScalarRealization.admissible_scalar_realization_exact l W).2.2.1 E).1.1).2.1
  let : FA.Additive := inferInstance
  let : (FiniteConstantModel.modelFunctor B W).Additive := by
    let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    let : DiscreteTopology B := DerivedNakayama.quotientDiscrete l E (n + 1)
    exact (AdmissibleScalarRealization.finite_scalar_assertions B W).1.2.1
  let : (ModuleCat.extendScalars.{u, u, u} q).Additive :=
    (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
  let : P.IsStrictlyGE a := ha
  let : P.IsStrictlyLE b := hb
  let D : CochainComplex (AdicCompletion.Modules l E W) ℤ :=
    (FA.mapHomologicalComplex (.up ℤ)).obj P
  have hD : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E W) (.up ℤ)).kFlat D := by
    apply CochainComplex.kFlat_of_bounded_of_flat D a b
    intro i
    exact free_internal_flat l E W _ (modelFunctor_free A W (P.X i) (hP i).1 (hP i).2)
  let R := Mod.extendScalars (AdicCompletion.quotient l E W n)
  let := R.isIso_leftDerivedFunctorCounit_app_of_kFlat D hD
  let DR := (R.mapHomologicalComplex (.up ℤ)).obj D
  let eRed : R.leftDerivedFunctor.obj (DerivedCategory.Q.obj D) ≅
      DerivedCategory.Q.obj DR :=
    (R.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso _).app D)).symm ≪≫
    asIso (R.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj D)) ≪≫
    DerivedCategory.Qh.mapIso ((R.mapHomotopyCategoryFactors (.up ℤ)).app D) ≪≫
    (DerivedCategory.quotientCompQhIso _).app DR
  have hflat (i : ℤ) : Module.Flat A (P.X i) := by
    let : Module.Free A (P.X i) := (hP i).2
    infer_instance
  let eRaw := rawQuotientIso q P a b ha hb hflat M p hp
  let eChange : DR ≅ (FB.mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars.{u, u, u} q).mapHomologicalComplex (.up ℤ)).obj P) :=
    (Functor.mapHomologicalComplexCompIso
      (smallScalarExtensionIso q continuous_quot_mk W) (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, u} q ⋙ FB)) (.up ℤ)).app P).symm
  exact ⟨eRed ≪≫ DerivedCategory.Q.mapIso eChange ≪≫
    (FB.mapDerivedCategoryFactors.app _).symm ≪≫ FB.mapDerivedCategory.mapIso eRaw⟩

end AlgebraicGeometry.ProEtale

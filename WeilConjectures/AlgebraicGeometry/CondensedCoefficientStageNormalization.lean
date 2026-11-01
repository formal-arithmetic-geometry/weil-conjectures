/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Exact.ExactDerivedTransformation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso

/-! # Normalized scalar extensions for condensed constructible coefficients

Source: latest blueprint, `sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/`,
opening scalar-extension paragraph and `def-sfb-derived-extend-comp-iso.proof.md`;
`sk-prop-qlbar-two-colimit/def-sfb-constructible-cocone.md`.
(blueprint: lem-general-algebraically-closed-coefficient-stages).

The categories and scalar functors are the existing condensed ones. The structure below
packages their normalized shifts, unitors and associators. Its vertex comparison is the
existing comparison of the constructible cocone. Exactness is expressed by preservation
of ambient distinguished triangles, which is precisely exactness for the induced
triangulated structures, without choosing a second pretriangulation on a full subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.upperStarFromPointComp
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_pointUpperStar
  AlgebraicGeometry.ProEtale.oplaxMonoidal_pointUpperStar

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

private theorem ordinaryUnitHom {A B : C} [MonObj A] [MonObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f] (M : Mod C A) :
    ((extendRestrictAdjunction f).unit.app M).hom = extendUnitHom f M := by
  change extendUnitHom f M ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem ordinaryEq_unit {A B : C} [MonObj A] [MonObj B] [IsCommMonObj A]
    (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (h : f = g) (M : Mod C A) :
    extendUnitHom f M ≫ ((extendScalarsIsoOfEq h).hom.app M).hom =
      extendUnitHom g M := by
  have hh := congrArg (fun f ↦ f.hom)
    (Adjunction.unit_leftAdjointUniq_hom_app (extendRestrictAdjunction f)
      ((extendRestrictAdjunction g).ofNatIsoRight (comapCongr h).symm) M)
  change ((extendRestrictAdjunction f).unit.app M).hom ≫
      ((extendScalarsIsoOfEq h).hom.app M).hom =
    ((extendRestrictAdjunction g).unit.app M).hom ≫ 𝟙 _ at hh
  simpa only [ordinaryUnitHom, Category.comp_id] using hh

@[reassoc]
private theorem ordinaryComp_unit (f : R ⟶ S) [IsMonHom f]
    (g : S ⟶ T) [IsMonHom g] (k : R ⟶ T) [IsMonHom k]
    (h : f ≫ g = k) (M : Mod C R) :
    extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
        (((extendScalarsComp f g).symm ≪≫ extendScalarsIsoOfEq h).hom.app M).hom =
      extendUnitHom k M := by
  let adj := ((extendRestrictAdjunction f).comp (extendRestrictAdjunction g)).ofNatIsoRight
    (comapComp f g).symm
  have hh := congrArg (fun f ↦ f.hom)
    (Adjunction.unit_leftAdjointUniq_hom_app adj (extendRestrictAdjunction (f ≫ g)) M)
  have hu : (adj.unit.app M).hom =
      extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) := by
    change (((extendRestrictAdjunction f).comp
      (extendRestrictAdjunction g)).unit.app M).hom ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_unit_app, comp_hom', comap_map_hom,
      ordinaryUnitHom, ordinaryUnitHom]
  change (adj.unit.app M).hom ≫ ((extendScalarsComp f g).inv.app M).hom =
    ((extendRestrictAdjunction (f ≫ g)).unit.app M).hom at hh
  rw [hu, ordinaryUnitHom] at hh
  change extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
      (((extendScalarsComp f g).inv.app M).hom ≫
        ((extendScalarsIsoOfEq h).hom.app M).hom) = _
  rw [← Category.assoc, ← Category.assoc, hh, ordinaryEq_unit]

private theorem ordinaryId_unit (f : R ⟶ R) [IsMonHom f] (h : f = 𝟙 R) (M : Mod C R) :
    extendUnitHom f M ≫
        ((extendScalarsIsoOfEq h ≪≫ extendScalarsId).hom.app M).hom = 𝟙 M.X := by
  have hh := congrArg (fun f ↦ f.hom)
    (Adjunction.unit_leftAdjointUniq_hom_app (extendRestrictAdjunction (𝟙 R))
      (Adjunction.id.ofNatIsoRight (comapId R).symm) M)
  change ((extendRestrictAdjunction (𝟙 R)).unit.app M).hom ≫
      (extendScalarsId.hom.app M).hom = 𝟙 M.X ≫ 𝟙 M.X at hh
  rw [ordinaryUnitHom, Category.id_comp] at hh
  change extendUnitHom f M ≫ (((extendScalarsIsoOfEq h).hom.app M).hom ≫
    (extendScalarsId.hom.app M).hom) = _
  rw [← Category.assoc, ordinaryEq_unit, hh]

private theorem ordinaryComp_assoc
    {U : C} [MonObj U] [IsCommMonObj T]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g] (h : T ⟶ U) [IsMonHom h]
    (a : R ⟶ T) [IsMonHom a] (b : S ⟶ U) [IsMonHom b] (c : R ⟶ U) [IsMonHom c]
    (p : f ≫ g = a) (q : g ≫ h = b) (r : a ≫ h = c) (s : f ≫ b = c)
    (M : Mod C R) :
    (extendScalars h).map
        ((((extendScalarsComp f g).symm ≪≫ extendScalarsIsoOfEq p).hom).app M) ≫
      (((extendScalarsComp a h).symm ≪≫ extendScalarsIsoOfEq r).hom.app M) =
    (((extendScalarsComp g h).symm ≪≫ extendScalarsIsoOfEq q).hom.app
        ((extendScalars f).obj M)) ≫
      (((extendScalarsComp f b).symm ≪≫ extendScalarsIsoOfEq s).hom.app M) := by
  let m := (extendScalarsComp f g).symm ≪≫ extendScalarsIsoOfEq p
  let n := (extendScalarsComp a h).symm ≪≫ extendScalarsIsoOfEq r
  let t := (extendScalarsComp g h).symm ≪≫ extendScalarsIsoOfEq q
  let v := (extendScalarsComp f b).symm ≪≫ extendScalarsIsoOfEq s
  have hn : extendUnitHom h ((extendScalars g).obj ((extendScalars f).obj M)) ≫
        ((extendScalars h).map (m.hom.app M)).hom =
      (m.hom.app M).hom ≫ extendUnitHom h ((extendScalars a).obj M) := by
    have hh := congrArg (fun f ↦ f.hom)
      ((extendRestrictAdjunction h).unit.naturality (m.hom.app M))
    simpa only [Functor.id_map, Functor.comp_map, comp_hom', comap_map_hom,
      ordinaryUnitHom, Functor.comp_obj, Functor.id_obj, comap] using hh.symm
  have hL : extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
        extendUnitHom h ((extendScalars g).obj ((extendScalars f).obj M)) ≫
        ((extendScalars h).map (m.hom.app M)).hom ≫ (n.hom.app M).hom =
      extendUnitHom c M := by
    rw [reassoc_of% hn]
    rw [ordinaryComp_unit_assoc f g a p M, ordinaryComp_unit a h c r M]
  have hR : extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
        extendUnitHom h ((extendScalars g).obj ((extendScalars f).obj M)) ≫
        (t.hom.app ((extendScalars f).obj M)).hom ≫ (v.hom.app M).hom =
      extendUnitHom c M := by
    rw [ordinaryComp_unit_assoc g h b q ((extendScalars f).obj M), ordinaryComp_unit f b c s M]
  apply (((extendRestrictAdjunction f).comp (extendRestrictAdjunction g)).comp
    (extendRestrictAdjunction h)).homEquiv M _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply hom_ext
  simpa only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    comp_hom', comap_map_hom, ordinaryUnitHom, Category.assoc,
    Functor.comp_obj, comap, m, n, t, v] using hL.trans hR.symm

private theorem ordinaryComp_leftUnit
    (f : R ⟶ R) [IsMonHom f] (hf : f = 𝟙 R)
    (g : R ⟶ S) [IsMonHom g] (p : f ≫ g = g) (M : Mod C R) :
    (((extendScalarsComp f g).symm ≪≫ extendScalarsIsoOfEq p).hom.app M) =
      (extendScalars g).map ((extendScalarsIsoOfEq hf ≪≫ extendScalarsId).hom.app M) := by
  let i := extendScalarsIsoOfEq hf ≪≫ extendScalarsId
  have hn := congrArg (fun f ↦ f.hom)
    ((extendRestrictAdjunction g).unit.naturality (i.hom.app M))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, comp_hom', comap_map_hom] at hn
  simp only [ordinaryUnitHom, comap_map_hom] at hn
  have hR : extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
      ((extendScalars g).map (i.hom.app M)).hom = extendUnitHom g M := by
    rw [← hn, ← Category.assoc]
    erw [ordinaryId_unit, Category.id_comp]
  apply ((extendRestrictAdjunction f).comp (extendRestrictAdjunction g)).homEquiv M _
    |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply hom_ext
  simpa only [Adjunction.comp_unit_app, Functor.comp_map, comp_hom', comap_map_hom,
    ordinaryUnitHom, Category.assoc, Functor.comp_obj, comap, i] using
    (ordinaryComp_unit f g g p M).trans hR.symm

private theorem ordinaryComp_rightUnit
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ S) [IsMonHom g]
    (hg : g = 𝟙 S) (p : f ≫ g = f) (M : Mod C R) :
    (((extendScalarsComp f g).symm ≪≫ extendScalarsIsoOfEq p).hom.app M) =
      (extendScalarsIsoOfEq hg ≪≫ extendScalarsId).hom.app ((extendScalars f).obj M) := by
  have hR : extendUnitHom f M ≫ extendUnitHom g ((extendScalars f).obj M) ≫
      ((extendScalarsIsoOfEq hg ≪≫ extendScalarsId).hom.app ((extendScalars f).obj M)).hom =
      extendUnitHom f M := by
    rw [ordinaryId_unit]
    erw [Category.comp_id]
  apply ((extendRestrictAdjunction f).comp (extendRestrictAdjunction g)).homEquiv M _
    |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply hom_ext
  simpa only [Adjunction.comp_unit_app, Functor.comp_map, comp_hom', comap_map_hom,
    ordinaryUnitHom, Category.assoc, Functor.comp_obj, comap] using
    (ordinaryComp_unit f g f p M).trans hR.symm

/-- The fixed comparison with degreewise scalar extension followed by localization.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact scalar extension.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
def finiteScalarLocalizationIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory.Q ⋙ derivedExtendScalarsSubfield X ℓ h ≅
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategoryFactors

/-- The corresponding fixed comparison for extension to the condensed algebraic closure.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact scalar extension.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
def closureScalarLocalizationIso (E : FiniteIntermediateField ℓ) :
    DerivedCategory.Q ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Mod.extendScalars
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- Shift and comparison data on the fixed condensed scalar functors. Category shifts
are the restrictions of ordinary derived shifts, using `ObjectProperty.hasShift`.
Normalization and coherence are propositions about these data, stated separately below.
The larger heartbeat budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
class CondensedCoefficientStageData where
  /-- The finite coefficient subcategories are stable under every integer shift. -/
  [finiteStable : ∀ E : FiniteIntermediateField ℓ,
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsStableUnderShift ℤ]
  /-- The vertex is stable under every ordinary derived shift. -/
  [closureStable : (boundedConstructible (padicAlgClRingObj X ℓ)).IsStableUnderShift ℤ]
  /-- Coherent shifts on the ambient finite scalar functors. -/
  [ambientFiniteShift : ∀ (E F : FiniteIntermediateField ℓ) (h : E ≤ F),
    (derivedExtendScalarsSubfield X ℓ h).CommShift ℤ]
  /-- Coherent shifts on the ambient vertex scalar functors. -/
  [ambientClosureShift : ∀ E : FiniteIntermediateField ℓ,
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ]
  /-- Coherent shift comparisons on the restricted finite scalar functors. -/
  [finiteShift : ∀ (E F : FiniteIntermediateField ℓ) (h : E ≤ F),
    (constructibleExtendScalars X ℓ h).CommShift ℤ]
  /-- Coherent shift comparisons on the restricted vertex scalar functors. -/
  [closureShift : ∀ E : FiniteIntermediateField ℓ,
    (constructibleToPadicAlgCl X ℓ E).CommShift ℤ]
  /-- Identity coefficient inclusions, used only to type the ordinary unit normalization. -/
  coefficientId (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 (padicSubfieldRingObj X ℓ E)
  /-- Composition of coefficient inclusions, used to type tensor multiplication. -/
  coefficientComp (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjMap X ℓ k =
      padicSubfieldRingObjMap X ℓ (h.trans k)
  /-- Ambient unit comparison. -/
  ambientUnit (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsSubfield X ℓ (le_refl E) ≅ 𝟭 _
  /-- Ambient finite composition comparison. -/
  ambientComp (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsSubfield X ℓ k ≅
      derivedExtendScalarsSubfield X ℓ (h.trans k)
  /-- Unit comparison on the actual bounded constructible category. -/
  unit (E : FiniteIntermediateField ℓ) :
    constructibleExtendScalars X ℓ (le_refl E) ≅ 𝟭 (PadicSubfieldConstructible X ℓ E)
  /-- Composition comparison on the actual bounded constructible categories. -/
  comp (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    constructibleExtendScalars X ℓ h ⋙ constructibleExtendScalars X ℓ k ≅
      constructibleExtendScalars X ℓ (h.trans k)

attribute [instance_reducible] CondensedCoefficientStageData.ambientFiniteShift
  CondensedCoefficientStageData.ambientClosureShift CondensedCoefficientStageData.finiteShift
  CondensedCoefficientStageData.closureShift

attribute [instance] CondensedCoefficientStageData.finiteStable
  CondensedCoefficientStageData.closureStable CondensedCoefficientStageData.ambientFiniteShift
  CondensedCoefficientStageData.ambientClosureShift CondensedCoefficientStageData.finiteShift
  CondensedCoefficientStageData.closureShift

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The ShiftNormalization clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageShiftNormalization
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- Ambient shifts agree with the canonical exact, degreewise derived shifts. -/
  finiteShiftNormalization (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    @NatTrans.CommShift _ _ _ _ _ _ (finiteScalarLocalizationIso X ℓ h).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ DerivedCategory.Q
        (derivedExtendScalarsSubfield X ℓ h) ℤ _ _ _ _ inferInstance
        (d.ambientFiniteShift E F h)) inferInstance
  /-- The same degreewise normalization at the algebraic closure. -/
  closureShiftNormalization (E : FiniteIntermediateField ℓ) :
    @NatTrans.CommShift _ _ _ _ _ _ (closureScalarLocalizationIso X ℓ E).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ DerivedCategory.Q
        (derivedExtendScalarsToPadicAlgCl X ℓ E) ℤ _ _ _ _ inferInstance
        (d.ambientClosureShift E)) inferInstance
  /-- Additivity of finite scalar extension on the full subcategories. -/
  finiteAdditive (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    (constructibleExtendScalars X ℓ h).Additive
  /-- Additivity of scalar extension to the vertex. -/
  closureAdditive (E : FiniteIntermediateField ℓ) : (constructibleToPadicAlgCl X ℓ E).Additive
  /-- The finite shift comparison is the restriction of the ambient one. -/
  finiteShiftRestriction (E F : FiniteIntermediateField ℓ) (h : E ≤ F) (n : ℤ)
      (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.map
        (((d.finiteShift E F h).commShiftIso n).hom.app K) ≫
      ((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.commShiftIso n).hom.app
        ((constructibleExtendScalars X ℓ h).obj K) =
    (derivedExtendScalarsSubfield X ℓ h).map
        (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.commShiftIso n).hom.app K) ≫
      ((d.ambientFiniteShift E F h).commShiftIso n).hom.app K.obj
  /-- The vertex shift comparison is the restriction of the ambient one. -/
  closureShiftRestriction (E : FiniteIntermediateField ℓ) (n : ℤ)
      (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map
        (((d.closureShift E).commShiftIso n).hom.app K) ≫
      ((boundedConstructible (padicAlgClRingObj X ℓ)).ι.commShiftIso n).hom.app
        ((constructibleToPadicAlgCl X ℓ E).obj K) =
    (derivedExtendScalarsToPadicAlgCl X ℓ E).map
        (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.commShiftIso n).hom.app K) ≫
      ((d.ambientClosureShift E).commShiftIso n).hom.app K.obj

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The TensorNormalization clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageTensorNormalization
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- On all complexes the unit is localization of ordinary tensor multiplication. -/
  unitNormalization (E : FiniteIntermediateField ℓ)
      (K : CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (d.ambientUnit E).hom.app (DerivedCategory.Q.obj K) =
      (finiteScalarLocalizationIso X ℓ (le_refl E)).hom.app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (Mod.extendScalarsIsoOfEq (d.coefficientId E) ≪≫
              Mod.extendScalarsId (R := padicSubfieldRingObj X ℓ E)) (ComplexShape.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app K)
  /-- Finite associators localize the ordinary tensor multiplication comparison. -/
  compNormalization (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G)
      (K : CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (d.ambientComp E F G h k).hom.app (DerivedCategory.Q.obj K) ≫
        (finiteScalarLocalizationIso X ℓ (h.trans k)).hom.app K =
      (derivedExtendScalarsSubfield X ℓ k).map
          ((finiteScalarLocalizationIso X ℓ h).hom.app K) ≫
        (finiteScalarLocalizationIso X ℓ k).hom.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
                (padicSubfieldRingObjMap X ℓ k)).symm ≪≫
              Mod.extendScalarsIsoOfEq (d.coefficientComp E F G h k))
            (ComplexShape.up ℤ)).hom.app K)
  /-- The fixed ambient vertex comparison has the same tensor normalization. -/
  closureCompNormalization (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (derivedExtendScalarsCompIso X ℓ h).hom.app (DerivedCategory.Q.obj K) ≫
        (closureScalarLocalizationIso X ℓ E).hom.app K =
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map
          ((finiteScalarLocalizationIso X ℓ h).hom.app K) ≫
        (closureScalarLocalizationIso X ℓ F).hom.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
                (padicSubfieldRingObjToPadicAlgCl X ℓ F)).symm ≪≫
              Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))
            (ComplexShape.up ℤ)).hom.app K)
  /-- Full-subcategory restriction of the ambient unit. -/
  unitRestriction (E : FiniteIntermediateField ℓ) (K : PadicSubfieldConstructible X ℓ E) :
    ((d.unit E).hom.app K).hom = (d.ambientUnit E).hom.app K.obj
  /-- Full-subcategory restriction of the ambient finite associator. -/
  compRestriction (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G)
      (K : PadicSubfieldConstructible X ℓ E) :
    ((d.comp E F G h k).hom.app K).hom = (d.ambientComp E F G h k).hom.app K.obj
  /-- Theta is the prescribed restriction, hence the one in `constructibleCocone`. -/
  thetaRestriction (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The Coherence clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageCoherence
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- Units commute with every integer shift. -/
  unitShift (E : FiniteIntermediateField ℓ) :
    @NatTrans.CommShift _ _ _ _ _ _ (d.unit E).hom ℤ _ _ _
      (d.finiteShift E E (le_refl E)) inferInstance
  /-- Finite associators commute with every integer shift. -/
  compShift (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    @NatTrans.CommShift _ _ _ _ _ _ (d.comp E F G h k).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (d.finiteShift E F h) (d.finiteShift F G k))
      (d.finiteShift E G (h.trans k))
  /-- Theta commutes with every integer shift. -/
  thetaShift (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    @NatTrans.CommShift _ _ _ _ _ _ (constructibleToPadicAlgClCompIso X ℓ h).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (d.finiteShift E F h) (d.closureShift F)) (d.closureShift E)
  /-- Left unit identity, evaluated at an arbitrary constructible complex. -/
  leftUnit (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : PadicSubfieldConstructible X ℓ E) :
    (d.comp E E F (le_refl E) h).hom.app K =
      (constructibleExtendScalars X ℓ h).map ((d.unit E).hom.app K)
  /-- Right unit identity. -/
  rightUnit (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : PadicSubfieldConstructible X ℓ E) :
    (d.comp E F F h (le_refl F)).hom.app K =
      (d.unit F).hom.app ((constructibleExtendScalars X ℓ h).obj K)
  /-- The corresponding unit identity for the vertex. -/
  thetaUnit (E : FiniteIntermediateField ℓ) (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgClCompIso X ℓ (le_refl E)).hom.app K =
      (constructibleToPadicAlgCl X ℓ E).map ((d.unit E).hom.app K)
  /-- The four-field cocycle; evaluating removes the canonical functor associator. -/
  associativity (E F G H : FiniteIntermediateField ℓ)
      (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleExtendScalars X ℓ j).map ((d.comp E F G h k).hom.app K) ≫
        (d.comp E G H (h.trans k) j).hom.app K =
      (d.comp F G H k j).hom.app ((constructibleExtendScalars X ℓ h).obj K) ≫
        (d.comp E F H h (k.trans j)).hom.app K
  /-- The same cocycle with algebraically closed final coefficient field. -/
  thetaAssociativity (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G)
      (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl X ℓ G).map ((d.comp E F G h k).hom.app K) ≫
        (constructibleToPadicAlgClCompIso X ℓ (h.trans k)).hom.app K =
      (constructibleToPadicAlgClCompIso X ℓ k).hom.app
          ((constructibleExtendScalars X ℓ h).obj K) ≫
        (constructibleToPadicAlgClCompIso X ℓ h).hom.app K

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The Exactness clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageExactness
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- On Noetherian spaces the finite full subcategories are triangulated. -/
  finiteTriangulated (hX : TopologicalSpace.NoetherianSpace X) (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated
  /-- On Noetherian spaces the vertex full subcategory is triangulated. -/
  closureTriangulated (hX : TopologicalSpace.NoetherianSpace X) :
    (boundedConstructible (padicAlgClRingObj X ℓ)).IsTriangulated
  /-- Exactness for the prescribed restricted shifts and induced distinguished triangles. -/
  finiteExact (hX : TopologicalSpace.NoetherianSpace X) (E F : FiniteIntermediateField ℓ)
      (h : E ≤ F) (T : Triangle (PadicSubfieldConstructible X ℓ E)) :
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.mapTriangle.obj T) ∈ distTriang _ →
      ((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.mapTriangle.obj
        ((@Functor.mapTriangle _ _ _ _ _ _ (constructibleExtendScalars X ℓ h)
          (d.finiteShift E F h)).obj T)) ∈ distTriang _
  /-- Exactness of the vertex functors for the ordinary restricted derived shift. -/
  closureExact (hX : TopologicalSpace.NoetherianSpace X) (E : FiniteIntermediateField ℓ)
      (T : Triangle (PadicSubfieldConstructible X ℓ E)) :
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.mapTriangle.obj T) ∈ distTriang _ →
      ((boundedConstructible (padicAlgClRingObj X ℓ)).ι.mapTriangle.obj
        ((@Functor.mapTriangle _ _ _ _ _ _ (constructibleToPadicAlgCl X ℓ E)
          (d.closureShift E)).obj T)) ∈ distTriang _

/-- Exactly the ambient normalizations, restricted comparisons, coherence, and
conditional exactness required of the chosen condensed scalar data.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
def CondensedCoefficientStageNormalized (d : CondensedCoefficientStageData X ℓ) : Prop :=
  @CondensedCoefficientStageShiftNormalization X ℓ _ d ∧
    @CondensedCoefficientStageTensorNormalization X ℓ _ d ∧
    @CondensedCoefficientStageCoherence X ℓ _ d ∧
    @CondensedCoefficientStageExactness X ℓ _ d

private theorem commShiftData_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, s.commShiftIso n = t.commShiftIso n) : s = t := by
  cases s with
  | mk σ σzero σadd =>
    cases t with
    | mk τ τzero τadd =>
      have heq : σ = τ := funext h
      cases heq
      rfl

private theorem normalizedShift_unique
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.CommShift ℤ]
    (F : D ⥤ E) (G : C ⥤ E) [G.CommShift ℤ] (e : L ⋙ F ≅ G)
    (s t : F.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift e.hom ℤ)
    (ht : letI := t; NatTrans.CommShift e.hom ℤ) : s = t := by
  apply commShiftData_ext
  intro n
  apply Iso.ext
  apply Localization.natTrans_ext L W
  intro K
  have hσ :
      F.map ((L.commShiftIso n).hom.app K) ≫ (s.commShiftIso n).hom.app (L.obj K) ≫
        (e.hom.app K)⟦n⟧' =
      e.hom.app (K⟦n⟧) ≫ (G.commShiftIso n).hom.app K := by
    let := s
    let : NatTrans.CommShift e.hom ℤ := hs
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm e.hom n K
  have hτ :
      F.map ((L.commShiftIso n).hom.app K) ≫ (t.commShiftIso n).hom.app (L.obj K) ≫
        (e.hom.app K)⟦n⟧' =
      e.hom.app (K⟦n⟧) ≫ (G.commShiftIso n).hom.app K := by
    let := t
    let : NatTrans.CommShift e.hom ℤ := ht
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm e.hom n K
  simpa only [cancel_epi, ← Category.assoc, cancel_mono] using hσ.trans hτ.symm

private theorem exactDerivedComp_normalization
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (m : F ⋙ G ≅ H) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso m).hom.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategoryFactors.hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso m (.up ℤ)).hom.app K) := by
  have hcomp : (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K :=
    Functor.mapDerivedCategoryCompIso_hom_app_factors F G K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← hcomp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

@[instance_reducible]
private def normalizedFiniteShift (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    (derivedExtendScalarsSubfield X ℓ h).CommShift ℤ :=
  Functor.CommShift.ofIso
    (Mod.extendScalars
        (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory.symm
    ℤ

@[instance_reducible]
private def normalizedClosureShift (E : FiniteIntermediateField ℓ) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso
    (Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ

private theorem normalizedCoefficientId (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 (padicSubfieldRingObj X ℓ E) := by
  change coefficientMap (Profinite.padicSubfieldRingObjMap ℓ (le_refl E)) X = _
  rw [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id]

private theorem normalizedCoefficientComp (E F G : FiniteIntermediateField ℓ)
    (h : E ≤ F) (k : F ≤ G) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjMap X ℓ k =
      padicSubfieldRingObjMap X ℓ (h.trans k) := by
  rw [← coefficientMap_comp, ← Profinite.padicSubfieldRingObjMap_comp]

private def descendIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W]
    {F G : B ⥤ C} (e : q ⋙ F ≅ q ⋙ G) : F ≅ G :=
  (Localization.fullyFaithfulWhiskeringLeft q W C).preimageIso e

private theorem descendIso_hom_app
    {A B C : Type*} [Category A] [Category B] [Category C]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W]
    {F G : B ⥤ C} (e : q ⋙ F ≅ q ⋙ G) (K : A) :
    (descendIso q W e).hom.app (q.obj K) = e.hom.app K :=
  congr_app ((Localization.fullyFaithfulWhiskeringLeft q W C).map_preimage e.hom) K

private def normalizedAmbientUnit (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsSubfield X ℓ (le_refl E) ≅ 𝟭 _ :=
  descendIso DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (finiteScalarLocalizationIso X ℓ (le_refl E) ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (Mod.extendScalarsIsoOfEq (normalizedCoefficientId X ℓ E) ≪≫ Mod.extendScalarsId)
          (.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso _ (.up ℤ)) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

private def normalizedAmbientComp (E F G : FiniteIntermediateField ℓ)
    (h : E ≤ F) (k : F ≤ G) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsSubfield X ℓ k ≅
      derivedExtendScalarsSubfield X ℓ (h.trans k) :=
  descendIso DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (finiteScalarLocalizationIso X ℓ h)
        (derivedExtendScalarsSubfield X ℓ k) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (finiteScalarLocalizationIso X ℓ k) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso
          ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
            (padicSubfieldRingObjMap X ℓ k)).symm ≪≫
            Mod.extendScalarsIsoOfEq (normalizedCoefficientComp X ℓ E F G h k)) (.up ℤ))
        DerivedCategory.Q ≪≫
      (finiteScalarLocalizationIso X ℓ (h.trans k)).symm)

private theorem normalizedClosureComp_fac (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
    (K : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (derivedExtendScalarsCompIso X ℓ h).hom.app (DerivedCategory.Q.obj K) ≫
        (closureScalarLocalizationIso X ℓ E).hom.app K =
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map
          ((finiteScalarLocalizationIso X ℓ h).hom.app K) ≫
        (closureScalarLocalizationIso X ℓ F).hom.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
            (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
                (padicSubfieldRingObjToPadicAlgCl X ℓ F)).symm ≪≫
              Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))
            (.up ℤ)).hom.app K) := by
  let a := Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)
  let b := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)
  let c := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let m : a ⋙ b ≅ c := (Mod.extendScalarsComp _ _).symm ≪≫
    Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)
  have hf := exactDerivedComp_normalization a b c m K
  have hf' := congrArg (fun f ↦
    b.leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (a.leftDerivedFunctor.obj (DerivedCategory.Q.obj K)) ≫
      b.mapDerivedCategory.map
        (a.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K)) ≫ f) hf
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] at hf'
  simp only [derivedExtendScalarsCompIso, finiteScalarLocalizationIso, closureScalarLocalizationIso,
    Functor.leftDerivedFunctorCompIso, Functor.leftDerivedFunctorNatIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← b.mapDerivedCategory.map_comp_assoc,
    ← b.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc] at hf'
  have hn := b.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (a.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K))
  have hn' := congrArg (fun f ↦ f ≫
    (Functor.mapDerivedCategoryCompIso a b).inv.app (DerivedCategory.Q.obj K) ≫
    (Functor.mapDerivedCategoryNatIso m).hom.app (DerivedCategory.Q.obj K) ≫
    c.mapDerivedCategoryFactors.hom.app K) hn
  simp only [Category.assoc] at hn'
  have heq := hn'.symm.trans hf'
  simp only [a, b, c, m, Functor.map_comp, Category.assoc] at heq
  exact heq

private theorem stableBoundedConstructible
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (boundedConstructible R).IsStableUnderShift ℤ := by
  refine ⟨fun n ↦ ⟨fun K hK ↦ ⟨?_, ?_⟩⟩⟩
  · exact ObjectProperty.le_shift DerivedCategory.TStructure.t.bounded n K hK.1
  · intro i
    exact IsConstructibleModuleObject.of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso n i (n + i) rfl).app K).symm (hK.2 _)

@[instance_reducible]
private def normalizedStageData : CondensedCoefficientStageData X ℓ :=
  letI := normalizedFiniteShift X ℓ
  letI := normalizedClosureShift X ℓ
  letI (E : FiniteIntermediateField ℓ) :=
    stableBoundedConstructible X (padicSubfieldRingObj X ℓ E)
  letI := stableBoundedConstructible X (padicAlgClRingObj X ℓ)
  { finiteStable := fun E ↦ stableBoundedConstructible X (padicSubfieldRingObj X ℓ E)
    closureStable := stableBoundedConstructible X (padicAlgClRingObj X ℓ)
    ambientFiniteShift := normalizedFiniteShift X ℓ
    ambientClosureShift := normalizedClosureShift X ℓ
    finiteShift := fun E F h ↦ by
      unfold constructibleExtendScalars
      infer_instance
    closureShift := fun E ↦ by
      unfold constructibleToPadicAlgCl
      infer_instance
    coefficientId := normalizedCoefficientId X ℓ
    coefficientComp := normalizedCoefficientComp X ℓ
    ambientUnit := normalizedAmbientUnit X ℓ
    ambientComp := normalizedAmbientComp X ℓ
    unit := fun E ↦
      Functor.fullyFaithfulCancelRight (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
          (normalizedAmbientUnit X ℓ E))
    comp := fun E F G h k ↦
      Functor.fullyFaithfulCancelRight (boundedConstructible (padicSubfieldRingObj X ℓ G)).ι
        (Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
          (normalizedAmbientComp X ℓ E F G h k)) }

private theorem normalizedStageShiftNormalization :
    let := normalizedStageData X ℓ
    CondensedCoefficientStageShiftNormalization X ℓ := by
  let := normalizedStageData X ℓ
  have finiteAdd (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
      (derivedExtendScalarsSubfield X ℓ h).Additive :=
    Functor.additive_of_iso
      (Mod.extendScalars
        (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory.symm
  have closureAdd (E : FiniteIntermediateField ℓ) :
      (derivedExtendScalarsToPadicAlgCl X ℓ E).Additive :=
    Functor.additive_of_iso (Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory.symm
  refine
    { finiteShiftNormalization := ?_
      closureShiftNormalization := ?_
      finiteAdditive := fun E F h ↦ by
        unfold constructibleExtendScalars
        infer_instance
      closureAdditive := fun E ↦ by
        unfold constructibleToPadicAlgCl
        infer_instance
      finiteShiftRestriction := ?_
      closureShiftRestriction := ?_ }
  · intro E F h
    let e := (Mod.extendScalars
      (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory
    have : NatTrans.CommShift e.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility e.symm ℤ
    have : NatTrans.CommShift e.hom ℤ := NatTrans.CommShift.of_iso_inv e.symm ℤ
    change NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q e.hom ≫
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategoryFactors.hom) ℤ
    infer_instance
  · intro E
    let e := (Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory
    have : NatTrans.CommShift e.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility e.symm ℤ
    have : NatTrans.CommShift e.hom ℤ := NatTrans.CommShift.of_iso_inv e.symm ℤ
    change NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q e.hom ≫
        (Mod.extendScalars
          (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors.hom) ℤ
    infer_instance
  · intro E F h n K
    let e := (boundedConstructible (padicSubfieldRingObj X ℓ F)).liftCompιIso
      ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        derivedExtendScalarsSubfield X ℓ h)
      (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K)
    have : NatTrans.CommShift e.hom ℤ :=
      Functor.CommShift.ofComp_compatibility e ℤ
    have hh := NatTrans.shift_app_comm e.hom n K
    dsimp only [e, ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app] at hh
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hh
    simp only [constructibleExtendScalars, Functor.commShiftIso_comp_hom_app] at hh ⊢
    exact hh
  · intro E n K
    let e := (boundedConstructible (padicAlgClRingObj X ℓ)).liftCompιIso
      ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        derivedExtendScalarsToPadicAlgCl X ℓ E)
      (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)
    have : NatTrans.CommShift e.hom ℤ :=
      Functor.CommShift.ofComp_compatibility e ℤ
    have hh := NatTrans.shift_app_comm e.hom n K
    dsimp only [e, ObjectProperty.liftCompιIso, Iso.refl_hom, NatTrans.id_app] at hh
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hh
    simp only [constructibleToPadicAlgCl, Functor.commShiftIso_comp_hom_app] at hh ⊢
    exact hh

private theorem normalizedStageTensorNormalization :
    letI := normalizedStageData X ℓ
    CondensedCoefficientStageTensorNormalization X ℓ := by
  let := normalizedStageData X ℓ
  refine
    { unitNormalization := ?_
      compNormalization := ?_
      closureCompNormalization := normalizedClosureComp_fac X ℓ
      unitRestriction := ?_
      compRestriction := ?_
      thetaRestriction := ?_ }
  · intro E K
    change (normalizedAmbientUnit X ℓ E).hom.app (DerivedCategory.Q.obj K) = _
    simp only [normalizedAmbientUnit, descendIso_hom_app, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Category.comp_id]
    erw [Category.comp_id]
  · intro E F G h k K
    change (normalizedAmbientComp X ℓ E F G h k).hom.app
      (DerivedCategory.Q.obj K) ≫ _ = _
    simp only [normalizedAmbientComp, descendIso_hom_app, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · intro E K
    let i := (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
    change i.map ((Functor.fullyFaithfulCancelRight
      (F := constructibleExtendScalars X ℓ (le_refl E)) (G := 𝟭 _) i
      (Functor.isoWhiskerLeft i (normalizedAmbientUnit X ℓ E))).hom.app K) = _
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    rfl
  · intro E F G h k K
    let i := (boundedConstructible (padicSubfieldRingObj X ℓ G)).ι
    change i.map ((Functor.fullyFaithfulCancelRight
      (F := constructibleExtendScalars X ℓ h ⋙ constructibleExtendScalars X ℓ k)
      (G := constructibleExtendScalars X ℓ (h.trans k)) i
      (Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
        (normalizedAmbientComp X ℓ E F G h k))).hom.app K) = _
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    rfl
  · intro E F h K
    change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
    unfold constructibleToPadicAlgClCompIso
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    exact Category.id_comp _

private theorem normalizedStageExactness :
    letI := normalizedStageData X ℓ
    CondensedCoefficientStageExactness X ℓ := by
  let := normalizedStageData X ℓ
  have finiteTri (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
      (derivedExtendScalarsSubfield X ℓ h).IsTriangulated := by
    let e := (Mod.extendScalars
      (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory
    have : NatTrans.CommShift e.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility e.symm ℤ
    exact Functor.isTriangulated_of_iso e.symm
  have closureTri (E : FiniteIntermediateField ℓ) :
      (derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated := by
    let e := (Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory
    have : NatTrans.CommShift e.symm.hom ℤ :=
      Functor.CommShift.ofIso_compatibility e.symm ℤ
    exact Functor.isTriangulated_of_iso e.symm
  refine
    { finiteTriangulated := fun hX E ↦ by
        let := hX
        infer_instance
      closureTriangulated := fun hX ↦ by
        let := hX
        infer_instance
      finiteExact := ?_
      closureExact := ?_ }
  · intro hX E F h T hT
    let e := (boundedConstructible (padicSubfieldRingObj X ℓ F)).liftCompιIso
      ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        derivedExtendScalarsSubfield X ℓ h)
      (fun K ↦ boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h K)
    have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
    exact isomorphic_distinguished _
      ((derivedExtendScalarsSubfield X ℓ h).map_distinguished _ hT) _
      ((Functor.mapTriangleCompIso (constructibleExtendScalars X ℓ h)
          (boundedConstructible (padicSubfieldRingObj X ℓ F)).ι).symm.app T ≪≫
        (Functor.mapTriangleIso e).app T ≪≫
        (Functor.mapTriangleCompIso (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
          (derivedExtendScalarsSubfield X ℓ h)).app T)
  · intro hX E T hT
    let e := (boundedConstructible (padicAlgClRingObj X ℓ)).liftCompιIso
      ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
        derivedExtendScalarsToPadicAlgCl X ℓ E)
      (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)
    have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
    exact isomorphic_distinguished _
      ((derivedExtendScalarsToPadicAlgCl X ℓ E).map_distinguished _ hT) _
      ((Functor.mapTriangleCompIso (constructibleToPadicAlgCl X ℓ E)
          (boundedConstructible (padicAlgClRingObj X ℓ)).ι).symm.app T ≪≫
        (Functor.mapTriangleIso e).app T ≪≫
        (Functor.mapTriangleCompIso (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
          (derivedExtendScalarsToPadicAlgCl X ℓ E)).app T)

private theorem normalizedStageData_unique
    (d d' : CondensedCoefficientStageData X ℓ)
    (hd : CondensedCoefficientStageNormalized X ℓ d)
    (hd' : CondensedCoefficientStageNormalized X ℓ d') : d = d' := by
  let := d
  obtain ⟨hs, ht, _, _⟩ := hd
  obtain ⟨hs', ht', _, _⟩ := hd'
  have haf : d.ambientFiniteShift = d'.ambientFiniteShift := by
    funext E F h
    exact normalizedShift_unique DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (derivedExtendScalarsSubfield X ℓ h)
      ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q)
      (finiteScalarLocalizationIso X ℓ h) _ _
      (hs.finiteShiftNormalization E F h)
      ((@CondensedCoefficientStageShiftNormalization.finiteShiftNormalization
        X ℓ _ d' hs') E F h)
  have hac : d.ambientClosureShift = d'.ambientClosureShift := by
    funext E
    exact normalizedShift_unique DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (derivedExtendScalarsToPadicAlgCl X ℓ E)
      ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q)
      (closureScalarLocalizationIso X ℓ E) _ _
      (hs.closureShiftNormalization E)
      ((@CondensedCoefficientStageShiftNormalization.closureShiftNormalization
        X ℓ _ d' hs') E)
  have hsf : d.finiteShift = d'.finiteShift := by
    funext E F h
    apply commShiftData_ext
    intro n
    apply Iso.ext
    ext K
    apply (cancel_mono
      (((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.commShiftIso n).hom.app
        ((constructibleExtendScalars X ℓ h).obj K))).1
    have h' := (@CondensedCoefficientStageShiftNormalization.finiteShiftRestriction
        X ℓ _ d' hs') E F h n K
    rw [← haf] at h'
    exact (hs.finiteShiftRestriction E F h n K).trans h'.symm
  have hsc : d.closureShift = d'.closureShift := by
    funext E
    apply commShiftData_ext
    intro n
    apply Iso.ext
    ext K
    apply (cancel_mono
      (((boundedConstructible (padicAlgClRingObj X ℓ)).ι.commShiftIso n).hom.app
        ((constructibleToPadicAlgCl X ℓ E).obj K))).1
    have h' := (@CondensedCoefficientStageShiftNormalization.closureShiftRestriction
        X ℓ _ d' hs') E n K
    rw [← hac] at h'
    exact (hs.closureShiftRestriction E n K).trans h'.symm
  have hau : d.ambientUnit = d'.ambientUnit := by
    funext E
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro K
    exact (ht.unitNormalization E K).trans
      ((@CondensedCoefficientStageTensorNormalization.unitNormalization
        X ℓ _ d' ht') E K).symm
  have hcmp : d.ambientComp = d'.ambientComp := by
    funext E F G h k
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
    intro K
    apply (cancel_mono ((finiteScalarLocalizationIso X ℓ (h.trans k)).hom.app K)).1
    exact (ht.compNormalization E F G h k K).trans
      ((@CondensedCoefficientStageTensorNormalization.compNormalization
        X ℓ _ d' ht') E F G h k K).symm
  have hu : d.unit = d'.unit := by
    funext E
    apply Iso.ext
    ext K
    rw [ht.unitRestriction, (@CondensedCoefficientStageTensorNormalization.unitRestriction
        X ℓ _ d' ht'), hau]
  have hc : d.comp = d'.comp := by
    funext E F G h k
    apply Iso.ext
    ext K
    rw [ht.compRestriction, (@CondensedCoefficientStageTensorNormalization.compRestriction
        X ℓ _ d' ht'), hcmp]
  cases d
  cases d'
  congr 1

private theorem localized_assoc
    {A B C D a b c d : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category a] [Category b] [Category c] [Category d]
    (q : a ⥤ A) (W : MorphismProperty a) [q.IsLocalization W]
    {qB : b ⥤ B} {qC : c ⥤ C} {qD : d ⥤ D}
    {f : A ⥤ B} {g : B ⥤ C} {h : C ⥤ D}
    {p : A ⥤ C} {r : B ⥤ D} {s : A ⥤ D}
    {F : a ⥤ b} {G : b ⥤ c} {H : c ⥤ d}
    {P : a ⥤ c} {R : b ⥤ d} {S : a ⥤ d}
    (lf : q ⋙ f ≅ F ⋙ qB) (lg : qB ⋙ g ≅ G ⋙ qC)
    (lh : qC ⋙ h ≅ H ⋙ qD) (lp : q ⋙ p ≅ P ⋙ qC)
    (lr : qB ⋙ r ≅ R ⋙ qD) (ls : q ⋙ s ≅ S ⋙ qD)
    (u : f ⋙ g ≅ p) (v : g ⋙ h ≅ r) (w : p ⋙ h ≅ s) (z : f ⋙ r ≅ s)
    (U : F ⋙ G ≅ P) (V : G ⋙ H ≅ R) (Y : P ⋙ H ≅ S) (Z : F ⋙ R ≅ S)
    (hu : ∀ K, u.hom.app (q.obj K) ≫ lp.hom.app K =
      g.map (lf.hom.app K) ≫ lg.hom.app (F.obj K) ≫ qC.map (U.hom.app K))
    (hv : ∀ K, v.hom.app (qB.obj K) ≫ lr.hom.app K =
      h.map (lg.hom.app K) ≫ lh.hom.app (G.obj K) ≫ qD.map (V.hom.app K))
    (hw : ∀ K, w.hom.app (q.obj K) ≫ ls.hom.app K =
      h.map (lp.hom.app K) ≫ lh.hom.app (P.obj K) ≫ qD.map (Y.hom.app K))
    (hz : ∀ K, z.hom.app (q.obj K) ≫ ls.hom.app K =
      r.map (lf.hom.app K) ≫ lr.hom.app (F.obj K) ≫ qD.map (Z.hom.app K))
    (hc : ∀ K, H.map (U.hom.app K) ≫ Y.hom.app K =
      V.hom.app (F.obj K) ≫ Z.hom.app K) (K : A) :
    h.map (u.hom.app K) ≫ w.hom.app K =
      v.hom.app (f.obj K) ≫ z.hom.app K := by
  have heq : Functor.whiskerRight u.hom h ≫ w.hom =
      Functor.whiskerLeft f v.hom ≫ z.hom := by
    apply Localization.natTrans_ext q W
    intro K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    apply (cancel_mono (ls.hom.app K)).1
    simp only [Category.assoc]
    rw [hw, hz, ← h.map_comp_assoc, hu, Functor.map_comp, Functor.map_comp]
    have hn := lh.hom.naturality (U.hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [Category.assoc, Category.assoc, reassoc_of% hn]
    have hn' := v.hom.naturality (lf.hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn'
    rw [← reassoc_of% hn', reassoc_of% hv]
    simp only [← qD.map_comp]
    rw [hc]
  exact congr_app heq K

private theorem localized_leftUnit
    {A B a b : Type*} [Category A] [Category B] [Category a] [Category b]
    (q : a ⥤ A) (W : MorphismProperty a) [q.IsLocalization W] (qB : b ⥤ B)
    {e : A ⥤ A} {f : A ⥤ B} {I : a ⥤ a} {F : a ⥤ b}
    (le : q ⋙ e ≅ I ⋙ q) (lf : q ⋙ f ≅ F ⋙ qB)
    (u : e ≅ 𝟭 A) (m : e ⋙ f ≅ f) (U : I ≅ 𝟭 a) (M : I ⋙ F ≅ F)
    (hu : ∀ K, u.hom.app (q.obj K) = le.hom.app K ≫ q.map (U.hom.app K))
    (hm : ∀ K, m.hom.app (q.obj K) ≫ lf.hom.app K =
      f.map (le.hom.app K) ≫ lf.hom.app (I.obj K) ≫ qB.map (M.hom.app K))
    (hc : ∀ K, M.hom.app K = F.map (U.hom.app K)) (K : A) :
    m.hom.app K = f.map (u.hom.app K) := by
  have heq : m.hom = Functor.whiskerRight u.hom f := by
    apply Localization.natTrans_ext q W
    intro K
    change m.hom.app (q.obj K) = f.map (u.hom.app (q.obj K))
    apply (cancel_mono (lf.hom.app K)).1
    rw [hm, hu, Functor.map_comp, Category.assoc, hc]
    have hn := lf.hom.naturality (U.hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
  exact congr_app heq K

private theorem localized_rightUnit
    {A B a b : Type*} [Category A] [Category B] [Category a] [Category b]
    (q : a ⥤ A) (W : MorphismProperty a) [q.IsLocalization W] (qB : b ⥤ B)
    {e : B ⥤ B} {f : A ⥤ B} {I : b ⥤ b} {F : a ⥤ b}
    (le : qB ⋙ e ≅ I ⋙ qB) (lf : q ⋙ f ≅ F ⋙ qB)
    (u : e ≅ 𝟭 B) (m : f ⋙ e ≅ f) (U : I ≅ 𝟭 b) (M : F ⋙ I ≅ F)
    (hu : ∀ K, u.hom.app (qB.obj K) = le.hom.app K ≫ qB.map (U.hom.app K))
    (hm : ∀ K, m.hom.app (q.obj K) ≫ lf.hom.app K =
      e.map (lf.hom.app K) ≫ le.hom.app (F.obj K) ≫ qB.map (M.hom.app K))
    (hc : ∀ K, M.hom.app K = U.hom.app (F.obj K)) (K : A) :
    m.hom.app K = u.hom.app (f.obj K) := by
  have heq : m.hom = Functor.whiskerLeft f u.hom := by
    apply Localization.natTrans_ext q W
    intro K
    change m.hom.app (q.obj K) = u.hom.app (f.obj (q.obj K))
    apply (cancel_mono (lf.hom.app K)).1
    rw [hm, hc]
    have hn := u.hom.naturality (lf.hom.app K)
    dsimp only [Functor.id_map, Functor.comp_obj] at hn
    rw [← hn, hu]
  exact congr_app heq K

private theorem descendIso_commShift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W] [q.CommShift ℤ]
    {F G : B ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : q ⋙ F ≅ q ⋙ G) [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (descendIso q W e).hom ℤ := by
  have := Localization.essSurj q W
  have heq : Functor.whiskerLeft q (descendIso q W e).hom = e.hom :=
    (Localization.fullyFaithfulWhiskeringLeft q W C).map_preimage e.hom
  have : NatTrans.CommShift (Functor.whiskerLeft q (descendIso q W e).hom) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ q
    (fun K ↦ ⟨_, (q.objObjPreimageIso K).inv, inferInstance⟩)

private theorem localized_compShift
    {A B C a b c : Type*}
    [Category A] [Category B] [Category C] [Category a] [Category b] [Category c]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [HasShift a ℤ] [HasShift b ℤ] [HasShift c ℤ]
    (q : a ⥤ A) (W : MorphismProperty a) [q.IsLocalization W] [q.CommShift ℤ]
    {qB : b ⥤ B} {qC : c ⥤ C} [qB.CommShift ℤ] [qC.CommShift ℤ]
    {f : A ⥤ B} {g : B ⥤ C} {p : A ⥤ C}
    {F : a ⥤ b} {G : b ⥤ c} {P : a ⥤ c}
    [f.CommShift ℤ] [g.CommShift ℤ] [p.CommShift ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [P.CommShift ℤ]
    (lf : q ⋙ f ≅ F ⋙ qB) (lg : qB ⋙ g ≅ G ⋙ qC) (lp : q ⋙ p ≅ P ⋙ qC)
    [NatTrans.CommShift lf.hom ℤ] [NatTrans.CommShift lg.hom ℤ]
    [NatTrans.CommShift lp.hom ℤ]
    (u : f ⋙ g ≅ p) (U : F ⋙ G ≅ P) [NatTrans.CommShift U.hom ℤ]
    (hu : ∀ K, u.hom.app (q.obj K) ≫ lp.hom.app K =
      g.map (lf.hom.app K) ≫ lg.hom.app (F.obj K) ≫ qC.map (U.hom.app K)) :
    NatTrans.CommShift u.hom ℤ := by
  let e := (Functor.associator q f g).symm ≪≫
    Functor.isoWhiskerRight lf g ≪≫ Functor.associator F qB g ≪≫
    Functor.isoWhiskerLeft F lg ≪≫ (Functor.associator F G qC).symm ≪≫
    Functor.isoWhiskerRight U qC ≪≫ lp.symm
  have he : u = descendIso q W e := by
    apply Iso.ext
    apply Localization.natTrans_ext q W
    intro K
    rw [descendIso_hom_app]
    apply (cancel_mono (lp.hom.app K)).1
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact hu K
  rw [he]
  have : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  exact descendIso_commShift q W e

private theorem restricted_transShift
    {A B a b : Type*} [Category A] [Category B] [Category a] [Category b]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift a ℤ] [HasShift b ℤ]
    (iA : a ⥤ A) (iB : b ⥤ B) [iA.CommShift ℤ] [iB.CommShift ℤ] [iB.Faithful]
    {F G : a ⥤ b} {f g : A ⥤ B}
    [F.CommShift ℤ] [G.CommShift ℤ] [f.CommShift ℤ] [g.CommShift ℤ]
    (eF : F ⋙ iB ≅ iA ⋙ f) (eG : G ⋙ iB ≅ iA ⋙ g)
    [NatTrans.CommShift eF.hom ℤ] [NatTrans.CommShift eG.hom ℤ]
    (v : f ⟶ g) [NatTrans.CommShift v ℤ] (u : F ⟶ G)
    (hu : ∀ K, iB.map (u.app K) =
      eF.hom.app K ≫ v.app (iA.obj K) ≫ eG.inv.app K) : NatTrans.CommShift u ℤ := by
  have heq : Functor.whiskerRight u iB =
      eF.hom ≫ Functor.whiskerLeft iA v ≫ eG.inv := by
    ext K
    exact hu K
  have : NatTrans.CommShift (Functor.whiskerRight u iB) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight u iB

private theorem termwise_leftUnit
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {I : A ⥤ A} {F : A ⥤ B} [I.Additive] [F.Additive]
    (u : I ≅ 𝟭 A) (m : I ⋙ F ≅ F)
    (h : ∀ X, m.hom.app X = F.map (u.hom.app X)) (K : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso m (.up ℤ)).hom.app K =
      (F.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex u (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K) := by
  ext n : 1
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
    Iso.trans_hom, NatTrans.comp_app, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  erw [Category.comp_id]
  exact h (K.X n)

private theorem termwise_rightUnit
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {I : B ⥤ B} {F : A ⥤ B} [I.Additive] [F.Additive]
    (u : I ≅ 𝟭 B) (m : F ⋙ I ≅ F)
    (h : ∀ X, m.hom.app X = u.hom.app (F.obj X)) (K : CochainComplex A ℤ) :
    (Functor.mapHomologicalComplexCompIso m (.up ℤ)).hom.app K =
      (NatIso.mapHomologicalComplex u (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso B (.up ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  ext n : 1
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f,
    HomologicalComplex.comp_f, Iso.trans_hom, NatTrans.comp_app,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
  erw [Category.comp_id]
  exact h (K.X n)

private theorem termwise_assoc
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
    {P : A ⥤ C} {R : B ⥤ D} {S : A ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [P.Additive] [R.Additive] [S.Additive]
    (m : F ⋙ G ≅ P) (n : G ⋙ H ≅ R) (p : P ⋙ H ≅ S) (q : F ⋙ R ≅ S)
    (h : ∀ X, H.map (m.hom.app X) ≫ p.hom.app X =
      n.hom.app (F.obj X) ≫ q.hom.app X) (K : CochainComplex A ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso m (.up ℤ)).hom.app K) ≫
      (Functor.mapHomologicalComplexCompIso p (.up ℤ)).hom.app K =
    (Functor.mapHomologicalComplexCompIso n (.up ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Functor.mapHomologicalComplexCompIso q (.up ℤ)).hom.app K := by
  ext i : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (K.X i)

end AlgebraicGeometry.ProEtale

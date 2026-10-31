/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterEvaluationData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterDegreeZeroData
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-scalar-maps). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Mod.monoidalCategory Mod.monoidalCategoryStruct
  Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 20000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

section CachedInstances
variable (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
private theorem pointFour : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (PointModules A)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem pointGood12 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (PointModules A)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem pointGood23 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (PointModules A)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem pointLeft : ∀ (X : PointModules A),
    PreservesColimitsOfShape ℤ ((curriedTensor (PointModules A)).obj X) := inferInstance
private theorem pointRight : ∀ (X : PointModules A),
    PreservesColimitsOfShape ℤ ((curriedTensor (PointModules A)).flip.obj X) := inferInstance
variable (T : Scheme.{u})
private theorem schemeFour : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Modules A T)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem schemeGood12 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem schemeGood23 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem schemeLeft : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).obj X) := inferInstance
private theorem schemeRight : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).flip.obj X) := inferInstance
end CachedInstances
attribute [local instance] pointFour pointGood12 pointGood23 pointLeft pointRight
  schemeFour schemeGood12 schemeGood23 schemeLeft schemeRight


variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

section Scalars
variable (S : Profinite.CondensedRing.{u}) [IsCommMonObj S.X]
  (φ : R.X ⟶ S.X) [IsMonHom φ]



/-- Exact coefficient restriction at the condensed point.
Source: Stacks 03D2 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev restrictPoint : PointModules S ⥤ PointModules R := Mod.comap φ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exact coefficient restriction on the small pro-etale site.
Source: Stacks 03D2 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev restrictScheme (X : Scheme.{u}) : Modules S X ⥤ Modules R X :=
  Mod.comap (coefficientMap φ X)

/-- The action identification for point pullback and restriction of scalars.
Source: Stacks 03D2 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def restrictPointPullD (X : Scheme.{u}) :
    (restrictPoint R S φ).mapDerivedCategory ⋙ pointPullD R X ≅
      pointPullD S X ⋙ (restrictScheme R S φ X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso ((upperStarFromPoint X).mapModComapIso φ) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- K-flat derived extension of scalars, with its recorded scalar adjunction.
Source: Stacks 07A6 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev extendPoint := (Mod.extendScalars φ).leftDerivedFunctor

/-- The derived tensorator of scalar extension, normalized by scalar units at the
ordinary level. This uses preservation of flat objects, never exact scalar extension.
Source: Stacks 07A4 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarTensor (K L : DerivedCategory (PointModules R)) :
    (extendPoint R S φ).obj K ⊗ (extendPoint R S φ).obj L ≅
      (extendPoint R S φ).obj (K ⊗ L) :=
  letI := (Mod.exists_extendScalarsMonoidal φ).choose
  letI := Mod.extendScalars_preservesFlat φ
  letI := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
  letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  Functor.Monoidal.μIso (extendPoint R S φ) K L

/-- The ordinary free-generator coefficient arrow, literally [t] ↦ [t].
Source: Stacks 03EK (blueprint: def-sfb-free-parameter-scalar-maps). -/
def freeGeneratorScalar (P : Profinite.{u}) :
    freeParameter R P ⟶ (restrictPoint R S φ).obj (freeParameter S P) :=
  ((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk R.X)).homEquiv _ _).symm
    ((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk S.X)).unit.app
      (ProfiniteFreeSlice.parameter P))

/-- Derived free scalar extension is the transpose of that very generator arrow.
Source: Stacks 07A6 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def freeScalarMap (P : Profinite.{u}) :
    (extendPoint R S φ).obj (parameterD R P) ⟶ parameterD S P :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _ |>.symm
    ((DerivedCategory.singleFunctor (PointModules R) 0).map (freeGeneratorScalar R S φ P) ≫
      ((restrictPoint R S φ).mapDerivedCategorySingleFunctor 0).inv.app (freeParameter S P))

attribute [local irreducible] freeScalarMap freeGeneratorScalar

private def ordinaryFreeScalarIso (P : Profinite.{u}) :
    (Mod.extendScalars φ).obj (freeParameter R P) ≅ freeParameter S P :=
  (Adjunction.leftAdjointUniq
    ((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk R.X)).comp
      (Mod.extendRestrictAdjunction φ))
    (Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk S.X))).app
      (ProfiniteFreeSlice.parameter P)

omit [IsCommMonObj S.X] in
private lemma ordinaryFreeScalarIso_transpose (P : Profinite.{u}) :
    (Mod.extendRestrictAdjunction φ).homEquiv _ _
      (ordinaryFreeScalarIso R S φ P).hom = freeGeneratorScalar R S φ P := by
  apply (Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk R.X)).homEquiv
    _ _ |>.injective
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk R.X)).comp
      (Mod.extendRestrictAdjunction φ))
    (Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk S.X))
    (ProfiniteFreeSlice.parameter P)
  rw [Adjunction.comp_homEquiv] at h
  change
    (Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk R.X)).homEquiv _ _
      ((Mod.extendRestrictAdjunction φ).homEquiv _ _
        (ordinaryFreeScalarIso R S φ P).hom) = _ at h
  simpa only [freeGeneratorScalar, Equiv.apply_symm_apply] using h

private lemma scalarAdjunction_unit_fac
    (K : HomotopyCategory (PointModules R) (.up ℤ)) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).unit.app
        (DerivedCategory.Qh.obj K) ≫
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctorCounit.app K) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory _).obj K) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).unit.app K) := by
  have h₁ := (Mod.extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso (PointModules R) (.up ℤ))
    (Mod.extendScalars φ).leftDerivedFunctorCounit (Mod.comap φ).rightDerivedFunctorUnit K
  have h₂ := NatTrans.congr_app
    (Mod.comap φ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    (((Mod.extendScalars φ).mapHomotopyCategory _).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  have h₃ := (Mod.comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((Mod.extendScalars φ).leftDerivedFunctorCounit.app K)
  simp only [Mod.derivedExtendMapDerivedCategoryAdjunction,
    Mod.derivedExtendRestrictAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  erw [← reassoc_of% h₃, reassoc_of% h₁]
  rw [reassoc_of% h₂, Iso.inv_hom_id_app]
  exact Category.comp_id _

omit [IsCommMonObj R.X] [IsCommMonObj S.X] in
private lemma restriction_factorsh (K : CochainComplex (PointModules S) ℤ) :
    (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient (PointModules S) (.up ℤ)).obj K) =
    (Mod.comap φ).mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change (Mod.comap φ).mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    DerivedCategory.Qh.map (𝟙 _) = _
  erw [(Mod.comap φ).mapDerivedCategory.map_id, (DerivedCategory.Qh (C := PointModules R)).map_id]
  simp only [Category.id_comp, Category.comp_id]

omit [IsCommMonObj S.X] in
private lemma scalar_single_unit (M : PointModules R) :
    (DerivedCategory.singleFunctor (PointModules R) 0).map
        ((Mod.extendRestrictAdjunction φ).unit.app M) ≫
      ((Mod.comap φ).mapDerivedCategorySingleFunctor 0).inv.app
        ((Mod.extendScalars φ).obj M) ≫
      (Mod.comap φ).mapDerivedCategory.map
        (DerivedCategory.Q.map
          (((Mod.extendScalars φ).mapCochainComplexSingleFunctor 0).inv.app M)) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient (PointModules R) (.up ℤ)).obj
            ((CochainComplex.singleFunctor (PointModules R) 0).obj M))) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient (PointModules R) (.up ℤ)).obj
          ((CochainComplex.singleFunctor (PointModules R) 0).obj M))) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change _ ≫ _ ≫ _ ≫ (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient (PointModules S) (.up ℤ)).obj
      (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (PointModules R) 0).obj M))) = _
  rw [restriction_factorsh R S φ]
  erw [(Mod.comap φ).mapDerivedCategoryFactors_hom_naturality]
  erw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  change (DerivedCategory.Q (C := PointModules R)).map _ ≫
    (DerivedCategory.Q (C := PointModules R)).map _ ≫
    (DerivedCategory.Q (C := PointModules R)).map _ =
    (DerivedCategory.Q (C := PointModules R)).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  ext n : 1
  by_cases hn : n = 0
  · subst n
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors, Functor.comp_obj,
      CochainComplex.shiftFunctor_obj_X', Functor.id_obj, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
      Adjunction.mapHomologicalComplex_unit_app_f, HomologicalComplex.single_map_f_self]
    erw [(Mod.extendScalars φ).map_id, (Mod.comap φ).map_id]
    erw [Category.comp_id]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _

private lemma scalar_single_transpose (M : PointModules R) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _
      ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient (PointModules R) (.up ℤ)).obj
            ((CochainComplex.singleFunctor (PointModules R) 0).obj M)) ≫
        DerivedCategory.Q.map
          (((Mod.extendScalars φ).mapCochainComplexSingleFunctor 0).hom.app M)) =
    (DerivedCategory.singleFunctor (PointModules R) 0).map
        ((Mod.extendRestrictAdjunction φ).unit.app M) ≫
      ((Mod.comap φ).mapDerivedCategorySingleFunctor 0).inv.app
        ((Mod.extendScalars φ).obj M) := by
  apply (cancel_mono
    ((Mod.comap φ).mapDerivedCategory.map (DerivedCategory.Q.map
        (((Mod.extendScalars φ).mapCochainComplexSingleFunctor 0).inv.app M)) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient (PointModules R) (.up ℤ)).obj
            ((CochainComplex.singleFunctor (PointModules R) 0).obj M))))).mp
  rw [Adjunction.homEquiv_apply]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  let hc := (DerivedCategory.Q (C := PointModules S)).mapIso
    (((Mod.extendScalars φ).mapCochainComplexSingleFunctor 0).app M)
  let hh := (Mod.comap φ).mapDerivedCategory.mapIso hc
  have hx : hh.hom ≫ hh.inv = 𝟙 _ := hh.hom_inv_id
  dsimp only [hh, hc] at hx
  erw [reassoc_of% hx]
  exact (scalarAdjunction_unit_fac R S φ _).trans (scalar_single_unit R S φ M).symm

@[irreducible] private def freeScalarIso (P : Profinite.{u}) :
    (extendPoint R S φ).obj (parameterD R P) ≅ parameterD S P :=
  have hK := (CochainComplex.kFlat_single_obj_iff_flat (freeParameter R P) 0).mpr
    (freeParameter_flat R P)
  letI : IsIso ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient (PointModules R) (.up ℤ)).obj
        ((CochainComplex.singleFunctor (PointModules R) 0).obj (freeParameter R P)))) :=
    (Mod.extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat _ hK
  asIso ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient (PointModules R) (.up ℤ)).obj
        ((CochainComplex.singleFunctor (PointModules R) 0).obj (freeParameter R P)))) ≪≫
    DerivedCategory.Q.mapIso
      (((Mod.extendScalars φ).mapCochainComplexSingleFunctor 0).app (freeParameter R P)) ≪≫
    (DerivedCategory.singleFunctor (PointModules S) 0).mapIso (ordinaryFreeScalarIso R S φ P)

private lemma freeScalarIso_hom (P : Profinite.{u}) :
    (freeScalarIso R S φ P).hom = freeScalarMap R S φ P := by
  apply (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _ |>.injective
  simp only [freeScalarMap, Equiv.apply_symm_apply, freeScalarIso, Iso.trans_hom,
    asIso_hom, CategoryTheory.Functor.mapIso_hom]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  erw [scalar_single_transpose R S φ (freeParameter R P)]
  simp only [Category.assoc]
  erw [← ((Mod.comap φ).mapDerivedCategorySingleFunctor 0).inv.naturality]
  simp only [CategoryTheory.Functor.comp_map]
  erw [← (DerivedCategory.singleFunctor (PointModules R) 0).map_comp_assoc]
  have h := ordinaryFreeScalarIso_transpose R S φ P
  rw [Adjunction.homEquiv_apply] at h
  rw [h]

set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  DerivedCategory.singleFunctors Profinite.CondensedAction.InternalBar.free
  Mod.comap Mod.extendScalars Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.upperStar CondensedRing.derivedComapUpperStarIso
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

/-- The normalized free scalar arrow is invertible for arbitrary ring maps.
Source: Stacks 03EK, node proof step 10
(blueprint: def-sfb-free-parameter-scalar-maps).
Proof: representable free modules are flat, hence their single complexes are
K-flat. Compute scalar extension on that complex. The scalar and free adjunctions
identify its result with the free S-module on the same representable; the identity
on generators supplies both inverse maps. The triangle identities show these maps
are inverse and that the forward map is exactly freeScalarMap. No scalar flatness
or preservation of K-injectives by restriction is used. -/
@[instance] theorem freeScalarMap_isIso (P : Profinite.{u}) :
    IsIso (freeScalarMap R S φ P) := by
  have h := freeScalarIso_hom R S φ P
  exact h ▸ (freeScalarIso R S φ P).isIso_hom

attribute [local irreducible] scalarTensor restrictPointPullD projectionAdjunction

/-- The closed/scalar double transpose defining the coefficient-Hom comparison.
Source: Stacks 07A6 and 08J7 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarHomPoint (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) (N' : DerivedCategory (PointModules S))
    (n : N ⟶ (restrictPoint R S φ).mapDerivedCategory.obj N') :
    (functions R P).obj N ⟶
      (restrictPoint R S φ).mapDerivedCategory.obj ((functions S P).obj N') :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _
    ((ihom.adjunction (parameterD S P)).homEquiv _ _
      ((inv (freeScalarMap R S φ P) ⊗ₘ 𝟙 _) ≫
        (scalarTensor R S φ (parameterD R P) ((functions R P).obj N)).hom ≫
        (extendPoint R S φ).map ((ihom.ev (parameterD R P)).app N) ≫
        ((Mod.derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _).symm n))

/-- a is pulled-back closed/scalar adjunction, with its coefficient-action identification.
Source: Stacks 07A6 and 08J7 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarHomMap (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) (N' : DerivedCategory (PointModules S))
    (n : N ⟶ (restrictPoint R S φ).mapDerivedCategory.obj N') :
    (pointPullD R X).obj ((functions R P).obj N) ⟶
      (restrictScheme R S φ X).mapDerivedCategory.obj
        ((pointPullD S X).obj ((functions S P).obj N')) :=
  (pointPullD R X).map (scalarHomPoint R S φ P N N' n) ≫
    (restrictPointPullD R S φ X).hom.app ((functions S P).obj N')

/-- Canonical scalar/pullback comparison: transpose pullback of the scalar unit
through the action identification. This definition precedes its isomorphism claim.
Source: Stacks 07A6 and 0D6D (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarPullComparison {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) :
    (Mod.extendScalars (coefficientMap φ Y)).leftDerivedFunctor.obj
      ((CondensedRing.upperStar R.X f).mapDerivedCategory.obj M) ⟶
    (CondensedRing.upperStar S.X f).mapDerivedCategory.obj
      ((Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor.obj M) :=
  ((mateEquiv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ Y))).symm
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)).natTrans.app M

attribute [local irreducible] scalarPullComparison

/-- Scalar extension commutes with exact geometric inverse image in this normalized form.
Source: Stacks 07A4 and 0D6D, node proof step 9
(blueprint: def-sfb-free-parameter-scalar-maps).
Proof: choose a K-flat resolution of M. Geometric inverse image is exact, strong
monoidal and preserves flat objects, so its termwise image computes the pulled
K-flat tensor. The balanced scalar tensor comparison is an isomorphism on each
term, normalized by x ↦ 1 tensor x. It commutes with differentials and descends to
the derived isomorphism. Scalar transposition identifies it with the displayed
scalar-unit formula, so the specified map itself is invertible without flatness
of the coefficient map. -/
@[instance] theorem scalarPullComparison_isIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) : IsIso (scalarPullComparison R S φ f M) := by
  -- Keep the auxiliary ringed-site localization instance local to this call.
  obtain ⟨b, hb⟩ : ∃ b : QuotientChange.D φ X ⋙ QuotientChange.L S.X f ≅
      QuotientChange.L R.X f ⋙ QuotientChange.D φ Y,
      QuotientChange.PullNormalized φ f b := by
    let (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj A] [IsCommMonObj A] (T : Scheme.{u}) :
        HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules A T) :=
      @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
        (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
          (Scheme.ProEt.topology T) _)
    exact QuotientChange.internal_pull_normalization_exists φ f
  let eR : QuotientChange.L R.X f ≅
      (CondensedRing.upperStar R.X f).mapDerivedCategory := by
    unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    exact CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f
  let eS : (CondensedRing.upperStar S.X f).mapDerivedCategory ≅
      QuotientChange.L S.X f := by
    unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f).symm
  let a := (mateEquiv (QuotientChange.scalarAdj φ X)
    (QuotientChange.scalarAdj φ Y)).symm
      (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)
  -- Transport between exact termwise and left-derived geometric pullback.
  have he : (a.whiskerTop eR.hom).whiskerBottom eS.hom =
      (mateEquiv (QuotientChange.scalarAdj φ X)
        (QuotientChange.scalarAdj φ Y)).symm
        (TwoSquare.mk _ _ _ _ (QuotientChange.normalizationRestrictionPull φ f).inv) := by
    apply (mateEquiv (QuotientChange.scalarAdj φ X)
      (QuotientChange.scalarAdj φ Y)).injective
    simp only [a, mateEquiv_whiskerTop_whiskerBottom, Equiv.apply_symm_apply]
    ext M
    delta QuotientChange.normalizationRestrictionPull
    dsimp only [eR, eS, id, TwoSquare.whiskerRight, TwoSquare.whiskerLeft]
    delta QuotientChange.L CondensedRing.moduleObjectDerivedPullback
    dsimp only [TwoSquare.mk, TwoSquare.natTrans, QuotientChange.V, QuotientChange.V₀]
    simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
  have hi : IsIso (((a.whiskerTop eR.hom).whiskerBottom eS.hom).natTrans.app M) := by
    rw [he, ← QuotientChange.normalized_inverse φ f b hb]
    infer_instance
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at hi
  have : IsIso (a.natTrans.app M) := by
    have := IsIso.of_isIso_comp_left
      ((QuotientChange.D φ Y).map (eR.hom.app M))
      (a.natTrans.app M ≫
        eS.hom.app ((QuotientChange.D φ X).obj M))
    exact IsIso.of_isIso_comp_right _
      (eS.hom.app ((QuotientChange.D φ X).obj M))
  dsimp only [a] at this
  delta QuotientChange.scalarAdj QuotientChange.D at this
  dsimp only [id] at this
  unfold scalarPullComparison
  exact this

/-- b is the direct-image coefficient mate, formed by scalar and geometric
adjunctions. Its transpose uses the scalar/pullback comparison and the geometric
counit; no inverse of a reverse direct-image comparison is postulated.
Source: Stacks 07A6 and 07A7 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarPushMap (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) (N' : DerivedCategory (PointModules S))
    (n : N ⟶ (restrictPoint R S φ).mapDerivedCategory.obj N') :
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
      ((pointPullD R (testScheme X P)).obj N) ⟶
    (restrictScheme R S φ X).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward S.X (projection X P)).obj
        ((pointPullD S (testScheme X P)).obj N')) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X)).homEquiv _ _
    ((projectionAdjunction S X P).homEquiv _ _
      (inv (scalarPullComparison R S φ (projection X P)
          ((CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
            ((pointPullD R (testScheme X P)).obj N))) ≫
        (Mod.extendScalars (coefficientMap φ (testScheme X P))).leftDerivedFunctor.map
          ((projectionAdjunction R X P).counit.app _) ≫
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap φ (testScheme X P))).homEquiv _ _).symm
          ((pointPullD R (testScheme X P)).map n ≫
            (restrictPointPullD R S φ (testScheme X P)).hom.app N')))

end Scalars

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Bounded acyclic flat models for the proper coefficient map

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6,
remark-Rf-lower-shriek-change-of-rings (blueprint:
lem-sp-acyclic-flat-proper-coefficient-model).

The scalar extension, its pullback comparison, and the coefficient mate are the
canonical constructions already provided by the étale six-functor interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

/- The three names below expose the canonical objects named in the statement. -/

/-- The derived tensor `T_T = - ⊗ᴸ_{A_T} B_T` used in the coefficient comparison.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientTensor {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  scalarExtension φ T

/-- The canonical tensor/pullback comparison `λ : T_W r_A^* ≅ r_B^* T_V` for the
coefficient extension; `scalarPullbackIso` is its inverse, used in the transpose below.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientPullbackComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  (scalarPullbackIso φ r).symm

/-- The canonical coefficient map `q_r`, defined as the adjoint mate of the
scalar-extended counit through the comparison above.
Source: Stacks Project, Tag 0GL6 (blueprint:
`lem-sp-acyclic-flat-proper-coefficient-model`). -/
abbrev properCoefficientMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :=
  scalarMate φ r

/-- The termwise scalar extension `C_B` of a cochain complex on `W`.
Source: Stacks 0GL6 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
abbrev coefficientExtendedComplex {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ :=
  ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj C

/-- The canonical derived comparison as a natural transformation on complexes.
The additive and zero structures here are those of the abelian category used by Qh.
Source: Stacks 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def acyclicComplexComparisonTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions D]
    (F : D ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) F.rightDerivedFunctorUnit

/-- The acyclic comparison with the concrete sheaf complex functors.
Source: Stacks 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properAcyclicComparisonTransformation
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V) :
    (lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ rightDerivedLowerStar (ModuleCat.{u + 1} A) r :=
  acyclicComplexComparisonTransformation (lowerStar (ModuleCat.{u + 1} A) r)

/-- The canonical acyclic-complex comparison, including the homotopy quotient factor.
Source: Stacks 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properAcyclicComparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj (DerivedCategory.Q.obj C) :=
  (properAcyclicComparisonTransformation A r).app C

/-- The ordinary B-linear projection map: the mate of scalar extension of the A-counit
through the ordinary scalar/pullback isomorphism. Its degreewise adjunct is precisely
pullback/tensor reassociation followed by counit tensor identity.
Source: Stacks 0GL6, 07A4 (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properSheafCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    lowerStar (ModuleCat.{u + 1} A) r ⋙ ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ W ⋙ lowerStar (ModuleCat.{u + 1} B) r :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom)).natTrans

/-- The termwise projection chain map pi_C. Mapping the ordinary natural transformation
on complexes guarantees that its components commute with the differentials.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def properCoefficientComplexMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    coefficientExtendedComplex φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj
        (coefficientExtendedComplex φ W C) :=
  { f n := (properSheafCoefficientMap φ r).app (C.X n)
    comm' i j _ := ((properSheafCoefficientMap φ r).naturality (C.d i j)).symm }

/-- The bounded, termwise flat and direct-image-acyclic hypotheses for this model.
Flatness of a term is exactness of tensoring with it (Stacks 03ER), the predicate
`exactFunctor` on the sheaf `tensorRight` recorded for this encoding by def-pc-flat-sheaf-modules.
Both coefficient rings and the proper Noetherian morphism are bound by the theorem.
Source: Stacks 0GL6, 015E (blueprint: lem-sp-acyclic-flat-proper-coefficient-model). -/
def IsAcyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) : Prop :=
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (C.X n)) ∧
    (∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (C.X n))) ∧
    (∀ n : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight
      ((lowerStar (ModuleCat.{u + 1} A) r).obj (C.X n)))) ∧
    (∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj
            ((DerivedCategory.singleFunctor
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (C.X n))))) ∧
    (∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℤ)).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} B) r).obj
            ((DerivedCategory.singleFunctor
              (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj
              ((coefficientExtendedComplex φ W C).X n)))))

private abbrev modelPullback
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V) :
    DerivedCategoryModule A V ⥤ DerivedCategoryModule A W :=
  (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor

private abbrev modelGeometricAdjunction
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V) :
    modelPullback A r ⊣ rightDerivedLowerStar (ModuleCat.{u + 1} A) r :=
  derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r

private abbrev modelScalarAdjunction
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtension φ T ⊣ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
  Adjunction.ofIsRightAdjoint _

private theorem flat_of_exact_tensorRight
    {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]
    (X : D) (h : exactFunctor _ _ (MonoidalCategory.tensorRight X)) :
    ObjectProperty.flat X := by
  refine ⟨?_, h⟩
  exact (exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight X).symm h

private theorem model_kFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : IsAcyclicFlatProperCoefficientModel φ r C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) := by
  obtain ⟨a, b, hb⟩ := hC.1
  have : C.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff C a).2
    (fun n hn ↦ hb n (Or.inl hn))
  have : C.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff C b).2
    (fun n hn ↦ hb n (Or.inr hn))
  exact ⟨CochainComplex.kFlat_of_bounded_of_flat C a b
      (fun n ↦ flat_of_exact_tensorRight _ (hC.2.1 n)),
    CochainComplex.kFlat_of_bounded_of_flat _ a b
      (fun n ↦ flat_of_exact_tensorRight _ (hC.2.2.1 n))⟩

private theorem Qh_map_quotient_map
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    {C C' : CochainComplex D ℤ} (h : C ⟶ C') :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map h) =
      DerivedCategory.Q.map h := by
  have hn := DerivedCategory.quotientCompQhIso_hom_naturality h
  have h₁ : (DerivedCategory.quotientCompQhIso D).hom.app C = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso D).hom.app C' = 𝟙 _ := rfl
  erw [h₁, h₂, Category.id_comp, Category.comp_id] at hn
  exact hn

private theorem properAcyclicComparison_naturality
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    {C C' : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (h : C ⟶ C') :
    DerivedCategory.Q.map
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
        properAcyclicComparison A r C' =
      properAcyclicComparison A r C ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) := by
  simpa only [Functor.comp_map, properAcyclicComparison] using
    (properAcyclicComparisonTransformation A r).naturality h

private abbrev modelHomotopyQuotient
    (D : Type*) [Category D] [Abelian D] :=
  HomotopyCategory.quotient D (.up ℤ)

private theorem rightDerivedUnit_isIso_of_acyclic
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [EnoughInjectives D]
    [Abelian.HasKInjectiveResolutions D]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F]
    (C : CochainComplex D ℤ) (a : ℤ) [C.IsStrictlyGE a]
    (hacyc : ∀ n : ℤ, F.rightAcyclic (C.X n)) :
    IsIso (F.rightDerivedFunctorUnit.app ((modelHomotopyQuotient _).obj C)) := by
  let L : CochainComplex.Plus D := ⟨C, a, inferInstance⟩
  have hi := F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hacyc
  have heq := F.ι_map_rightDerivedFunctorPlusUnit_app_comp
    ((HomotopyCategory.Plus.quotient _).obj L)
  change IsIso (F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.Plus.quotient _).obj L).obj)
  rw [← heq]
  infer_instance

private theorem acyclicComplexComparisonTransformation_isIso
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions D]
    (F : D ⥤ E) [F.Additive] (C : CochainComplex D ℤ)
    [IsIso (F.rightDerivedFunctorUnit.app ((modelHomotopyQuotient _).obj C))] :
    IsIso ((acyclicComplexComparisonTransformation F).app C) := by
  dsimp only [acyclicComplexComparisonTransformation, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

private theorem properAcyclicComparison_isIso_of_unit
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [IsIso ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorUnit.app
      ((modelHomotopyQuotient _).obj C))] :
    IsIso (properAcyclicComparison A r C) := by
  exact acyclicComplexComparisonTransformation_isIso
    (lowerStar (ModuleCat.{u + 1} A) r) C

private theorem properAcyclicComparison_isIso
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hb : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (C.X n))
    (ha : ∀ (n : ℤ) (q : ℕ), 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj
          ((DerivedCategory.singleFunctor
            (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (C.X n))))) :
    IsIso (properAcyclicComparison A r C) := by
  obtain ⟨a, hba⟩ := hb
  have : C.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff C a).2 hba
  have hacyc (n : ℤ) : (lowerStar (ModuleCat.{u + 1} A) r).rightAcyclic (C.X n) :=
    fun q ↦ (ha n (q + 1) (Nat.succ_pos q)).of_iso
      ((lowerStar (ModuleCat.{u + 1} A) r).homologyRightDerivedFunctorObjSingleFunctorIso
        (C.X n) (q + 1)).symm
  have := rightDerivedUnit_isIso_of_acyclic (lowerStar (ModuleCat.{u + 1} A) r) C a hacyc
  exact properAcyclicComparison_isIso_of_unit A r C

private theorem preservesKFlatQuasiIso_of_restrict_tensor
    {D : Type w} {E : Type*} [Category.{v} D] [Category E] [Abelian D] [Abelian E]
    [IsGrothendieckAbelian.{v} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [HasDerivedCategory.{v} D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : D ⥤ E) (U : E ⥤ D) [F.Additive] [U.Additive] [U.Faithful]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (X : D) (e : F ⋙ U ≅ MonoidalCategory.tensorRight X) : F.PreservesKFlatQuasiIso := by
  apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa X
  have hFU := ht.of_iso ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
  have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
    hFU.of_iso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (F ⋙ U)) (.up ℤ)).app K)
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)

private theorem etaleSheafExtendScalars_preservesKFlatQuasiIso
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso := by
  classical
  let J := T.smallEtaleTopology
  let E : Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const T.Etaleᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
  exact preservesKFlatQuasiIso_of_restrict_tensor E U (a.obj X) e

private theorem mapDerivedCategoryFactorsh_hom_app_eq
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex D ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  have h := F.mapDerivedCategoryFactorsh_hom_app P
  have h₁ : (DerivedCategory.quotientCompQhIso D).hom.app P = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso E).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have h₃ : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  erw [h₁, h₂, h₃, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  exact h

private theorem mapDerivedCategoryFactorsh_inv_app_eq
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex D ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.inv.app P := by
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).1
  rw [← mapDerivedCategoryFactorsh_hom_app_eq F P, Iso.inv_hom_id_app,
    mapDerivedCategoryFactorsh_hom_app_eq F P, Iso.inv_hom_id_app]
  rfl

private theorem scalarDerivedRepresentativeUnit_eq
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : F ⊣ U)
    (P : CochainComplex D ℤ) :
    (scalarDerivedRepresentativeUnit adj).app P =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        U.mapDerivedCategoryFactorsh.inv.app
          ((F.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change _ = DerivedCategory.Q.map _ ≫ U.mapDerivedCategoryFactorsh.inv.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P))
  rw [mapDerivedCategoryFactorsh_inv_app_eq]
  dsimp only [scalarDerivedRepresentativeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  congr 2
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Iso.refl_inv, NatTrans.id_app,
    Functor.comp_obj, Functor.id_obj,
    Category.id_comp]
  erw [Category.comp_id]

private theorem scalarExtensionRepresentative_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {C C' : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (h : C ⟶ C') :
    (scalarExtension φ T).map (DerivedCategory.Q.map h) ≫
        scalarExtensionRepresentative φ T C' =
      scalarExtensionRepresentative φ T C ≫ DerivedCategory.Q.map
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).map h) := by
  simpa only [scalarExtensionRepresentative, Functor.comp_map] using
    (scalarExtensionRepresentativeTransformation φ T).naturality h

private def properCoefficientComplexTransformation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    (lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⋙
        (ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ) ⟶
      (ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ) ⋙
        (lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ) :=
  { app C := properCoefficientComplexMap φ r C
    naturality C C' h := by
      ext n : 1
      exact (properSheafCoefficientMap φ r).naturality (h.f n) }

private theorem isIso_transpose_of_unit_comparison
    {D E : Type*} [Category D] [Category E]
    {F F' : D ⥤ E} {U : E ⥤ D} (adj : F ⊣ U) (adj' : F' ⊣ U)
    {X : D} {Y : E} (e : F'.obj X ⟶ Y) [IsIso e]
    (δ : X ⟶ U.obj Y) (hδ : adj'.unit.app X ≫ U.map e = δ) :
    IsIso ((adj.homEquiv X Y).symm δ) := by
  have he : (adj.homEquiv X Y).symm δ =
      (Adjunction.leftAdjointUniq adj adj').hom.app X ≫ e := by
    apply (adj.homEquiv X Y).injective
    rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact hδ.symm
  rw [he]
  infer_instance

private theorem transportedUnitFac
    {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {R S : E ⥤ D} (ad : L ⊣ R) (e : R ≅ S)
    {X Z : D} {Y : E} (a : L.obj X ⟶ Y) (s : S.obj Y ≅ Z)
    (u : X ⟶ Z) (v : Z ⟶ R.obj Y)
    (hu : ad.unit.app X ≫ R.map a = u ≫ v)
    (hv : v ≫ e.hom.app Y = s.inv) :
    (ad.ofNatIsoRight e).unit.app X ≫ S.map a ≫ s.hom = u := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality_assoc, ← Category.assoc, hu]
  simp only [Category.assoc]
  rw [reassoc_of% hv, Iso.inv_hom_id, Category.comp_id]

private theorem scalarRepresentative_isIso_of_kFlat
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
    [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
    [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasKInjectiveResolutions E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive] [F.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : F ⊣ U)
    {L : DerivedCategory D ⥤ DerivedCategory E} (ad : L ⊣ U.mapDerivedCategory)
    (P : CochainComplex D ℤ) (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((scalarDerivedRepresentativeTransformation adj ad).app P) := by
  change IsIso ((ad.homEquiv _ _).symm ((scalarDerivedRepresentativeUnit adj).app P))
  let adj' := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e := F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P)
  have : IsIso e := by
    have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
    dsimp only [e]
    infer_instance
  apply isIso_transpose_of_unit_comparison (F := L) ad adj' e
  change adj'.unit.app (DerivedCategory.Q.obj P) ≫ U.mapDerivedCategory.map e =
    (scalarDerivedRepresentativeUnit adj).app P
  have hraw := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    U.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have h : adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
      U.rightDerivedFunctor.map (F.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      U.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    rw [Adjunction.derivedAdjunction, Adjunction.derived_unit]
    exact hraw
  have hu := NatTrans.congr_app U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  have he : e = F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    have hi : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
    dsimp only [e]
    erw [hi, CategoryTheory.Functor.map_id, Category.comp_id]
  have hnorm := transportedUnitFac adj.derivedAdjunction
    U.rightDerivedFunctorIsoMapDerivedCategory
    (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    (U.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (U.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) h hu
  rw [he, scalarDerivedRepresentativeUnit_eq]
  apply (cancel_mono (U.mapDerivedCategoryFactorsh.hom.app
    ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))).1
  simp only [adj', Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact hnorm

private theorem scalarExtensionRepresentative_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (scalarExtensionRepresentative φ T P) := by
  have : (ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso :=
    etaleSheafExtendScalars_preservesKFlatQuasiIso φ T
  exact scalarRepresentative_isIso_of_kFlat (L := scalarExtension φ T)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T) (modelScalarAdjunction φ T) P hP

private theorem derivedComparison_counit
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive] (adj : F ⊣ U)
    (L : DerivedCategory D ⥤ DerivedCategory E) (R : DerivedCategory E ⥤ DerivedCategory D)
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (β : U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (ε : R ⋙ L ⟶ 𝟭 _) (C : CochainComplex E ℤ)
    (h : L.map (β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≫
        ε.app (DerivedCategory.Q.obj C) =
      α.app ((U.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) :
    L.map (DerivedCategory.Qh.map ((U.mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
        β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≫
        ε.app (DerivedCategory.Q.obj C) =
      (α.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((U.mapHomologicalComplex (.up ℤ)).obj C)) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app
          ((U.mapHomologicalComplex (.up ℤ)).obj C))) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app C) := by
  have hiU : (U.mapHomotopyCategoryFactors (.up ℤ)).inv.app C = 𝟙 _ := rfl
  have hiF : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      ((U.mapHomologicalComplex (.up ℤ)).obj C) = 𝟙 _ := rfl
  erw [hiU, CategoryTheory.Functor.map_id, Category.id_comp, hiF,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient, Qh_map_quotient_map] at h
  exact h

private def leftComparisonTransformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] (L : DerivedCategory D ⥤ DerivedCategory E)
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) α ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh

private theorem derivedComparison_counit_transformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive] (adj : F ⊣ U)
    (L : DerivedCategory D ⥤ DerivedCategory E) (R : DerivedCategory E ⥤ DerivedCategory D)
    (α : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (β : U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (ε : R ⋙ L ⟶ 𝟭 _)
    (h : ∀ X : HomotopyCategory E (.up ℤ),
      L.map (β.app X) ≫ ε.app (DerivedCategory.Qh.obj X) =
        α.app ((U.mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app X)) :
    Functor.whiskerRight
        (Functor.whiskerRight (U.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
          Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) β) L ≫
        Functor.whiskerLeft DerivedCategory.Q ε =
      Functor.whiskerLeft (U.mapHomologicalComplex (.up ℤ))
          (leftComparisonTransformation F L α) ≫
        Functor.whiskerRight ((adj.mapHomologicalComplex (.up ℤ)).counit)
          DerivedCategory.Q := by
  ext C
  dsimp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    acyclicComplexComparisonTransformation, leftComparisonTransformation]
  exact derivedComparison_counit adj L R α β ε C
    (h ((HomotopyCategory.quotient _ (.up ℤ)).obj C))

private theorem nativeDerivedComparison_counit_transformation
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
    [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).obj X)]
    [∀ (X : D), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor D).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasKInjectiveResolutions E]
    {F : D ⥤ E} {U : E ⥤ D} [F.Additive] [U.Additive] [F.PreservesKFlatQuasiIso]
    (adj : F ⊣ U) :
    Functor.whiskerRight (acyclicComplexComparisonTransformation U) F.leftDerivedFunctor ≫
        Functor.whiskerLeft DerivedCategory.Q adj.derivedAdjunction.counit =
      Functor.whiskerLeft (U.mapHomologicalComplex (.up ℤ))
          (leftComparisonTransformation F F.leftDerivedFunctor F.leftDerivedFunctorCounit) ≫
        Functor.whiskerRight ((adj.mapHomologicalComplex (.up ℤ)).counit)
          DerivedCategory.Q := by
  apply derivedComparison_counit_transformation adj F.leftDerivedFunctor
    U.rightDerivedFunctor F.leftDerivedFunctorCounit U.rightDerivedFunctorUnit
    adj.derivedAdjunction.counit
  intro X
  rw [Adjunction.derivedAdjunction, Adjunction.derived_counit]
  exact (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    U.rightDerivedFunctorUnit X

private def geometricComplexCounit
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V) :
    (lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⋙
        (upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⟶
      𝟭 (CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r).mapHomologicalComplex
    (.up ℤ)).counit

private def geometricRepresentativeTransformation
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V) :
    DerivedCategory.Q ⋙ modelPullback A r ⟶
      (upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  leftComparisonTransformation (upperStar (ModuleCat.{u + 1} A) r) (modelPullback A r)
    (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctorCounit

private theorem geometricRepresentativeTransformation_app
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (geometricRepresentativeTransformation A r).app P = scalarGeometricRepresentative A r P := by
  rfl

private theorem geometric_counit_transformation
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V) :
    Functor.whiskerRight (properAcyclicComparisonTransformation A r) (modelPullback A r) ≫
        Functor.whiskerLeft DerivedCategory.Q (modelGeometricAdjunction A r).counit =
      Functor.whiskerLeft
          ((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ))
          (geometricRepresentativeTransformation A r) ≫
        Functor.whiskerRight
          (geometricComplexCounit A r) DerivedCategory.Q := by
  exact nativeDerivedComparison_counit_transformation
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)

private theorem geometric_counit_comparison
    (A : Type (u + 1)) [CommRing A] {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (modelPullback A r).map
        (properAcyclicComparison A r C) ≫
        (modelGeometricAdjunction A r).counit.app
          (DerivedCategory.Q.obj C) =
      scalarGeometricRepresentative A r
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((geometricComplexCounit A r).app C) := by
  simpa only [properAcyclicComparison, geometricRepresentativeTransformation_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map] using
    NatTrans.congr_app (geometric_counit_transformation A r) C

private theorem properCoefficientComplexMap_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
        (properCoefficientComplexMap φ r C) ≫
        (geometricComplexCounit B r).app (coefficientExtendedComplex φ W C) =
      (scalarSheafPullbackComplexIso φ r).hom.app
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
        ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map
          ((geometricComplexCounit A r).app C) := by
  ext n : 1
  simp only [properCoefficientComplexMap, scalarSheafPullbackComplexIso,
    geometricComplexCounit,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.refl_inv, NatTrans.id_app,
    Functor.comp_obj, Functor.id_obj]
  exact mateEquiv_counit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom) (C.X n)

private theorem mate_model_square
    {XA YA XB YB : Type*} [Category XA] [Category YA] [Category XB] [Category YB]
    {LA : YA ⥤ XA} {RA : XA ⥤ YA} {LB : YB ⥤ XB} {RB : XB ⥤ YB}
    (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) {TX : XA ⥤ XB} {TY : YA ⥤ YB}
    (c : TY ⋙ LB ⟶ LA ⋙ TX) {K : XA} {D : YA} {M : YB} {E : XB}
    (a : D ⟶ RA.obj K) (b : TX.obj K ⟶ E) (d : TY.obj D ⟶ M)
    (p : M ⟶ RB.obj E)
    (h : c.app D ≫ TX.map (LA.map a ≫ adjA.counit.app K) ≫ b =
      LB.map d ≫ LB.map p ≫ adjB.counit.app E) :
    TY.map a ≫ (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ c)).app K ≫ RB.map b =
      d ≫ p := by
  apply (adjB.homEquiv _ _).symm.injective
  rw [adjB.homEquiv_counit, adjB.homEquiv_counit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [adjB.counit_naturality]
  rw [reassoc_of% (mateEquiv_counit adjA adjB (TwoSquare.mk _ _ _ _ c) K)]
  have hc := c.naturality a
  dsimp only [Functor.comp_map] at hc
  rw [reassoc_of% hc]
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h

private theorem mate_model_square_of_factorizations
    {XA YA XB YB : Type*} [Category XA] [Category YA] [Category XB] [Category YB]
    {LA : YA ⥤ XA} {RA : XA ⥤ YA} {LB : YB ⥤ XB} {RB : XB ⥤ YB}
    (adjA : LA ⊣ RA) (adjB : LB ⊣ RB) {TX : XA ⥤ XB} {TY : YA ⥤ YB}
    (c : TY ⋙ LB ⟶ LA ⋙ TX) {K N : XA} {D : YA} {M H : YB} {E N' P Q : XB}
    (a : D ⟶ RA.obj K) (b : TX.obj K ⟶ E) (d : TY.obj D ⟶ M)
    (π : M ⟶ H) (p : H ⟶ RB.obj E)
    (γA : LA.obj D ⟶ N) (εA : N ⟶ K) (bN : TX.obj N ⟶ N') (eφ : N' ⟶ E)
    (γM : LB.obj M ⟶ P) (l : P ⟶ N') (γH : LB.obj H ⟶ Q)
    (s : P ⟶ Q) (εB : Q ⟶ E)
    (ha : LA.map a ≫ adjA.counit.app K = γA ≫ εA)
    (hb : TX.map εA ≫ b = bN ≫ eφ)
    (hn : c.app D ≫ TX.map γA ≫ bN = LB.map d ≫ γM ≫ l)
    (hp : l ≫ eφ = s ≫ εB)
    (hg : LB.map π ≫ γH = γM ≫ s)
    (he : LB.map p ≫ adjB.counit.app E = γH ≫ εB) :
    TY.map a ≫ (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ c)).app K ≫ RB.map b =
      d ≫ π ≫ p := by
  apply mate_model_square adjA adjB c a b d (π ≫ p)
  calc
    _ = c.app D ≫ TX.map γA ≫ (TX.map εA ≫ b) := by
      rw [ha, Functor.map_comp]
      simp only [Category.assoc]
    _ = (c.app D ≫ TX.map γA ≫ bN) ≫ eφ := by
      rw [hb]
      simp only [Category.assoc]
    _ = (LB.map d ≫ γM ≫ l) ≫ eφ := by rw [hn]
    _ = LB.map d ≫ γM ≫ (s ≫ εB) := by
      simp only [Category.assoc]
      rw [hp]
    _ = LB.map d ≫ (LB.map π ≫ γH) ≫ εB := by
      rw [hg]
      simp only [Category.assoc]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [he]

private theorem properCoefficientModel_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (C : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hD : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C)) :
    (properCoefficientTensor φ V).map (properAcyclicComparison A r C) ≫
        (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
          (scalarExtensionRepresentative φ W C) =
      scalarExtensionRepresentative φ V
          (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map (properCoefficientComplexMap φ r C) ≫
        properAcyclicComparison B r (coefficientExtendedComplex φ W C) := by
  let D := ((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C
  let M := coefficientExtendedComplex φ V D
  let E := coefficientExtendedComplex φ W C
  let H := ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj E
  let LB := (modelPullback B r)
  let eA : ((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj D ⟶ C :=
    (geometricComplexCounit A r).app C
  let eB : ((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).obj H ⟶ E :=
    (geometricComplexCounit B r).app E
  let π := properCoefficientComplexMap φ r C
  let eφ := ((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map eA
  have hn := (scalarPullbackIso_existsUnique φ r).choose_spec.1 D hD
  have hg : LB.map (DerivedCategory.Q.map π) ≫ scalarGeometricRepresentative B r H =
      scalarGeometricRepresentative B r M ≫ DerivedCategory.Q.map
        (((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map π) :=
    by
      simpa only [geometricRepresentativeTransformation_app, Functor.comp_map] using
        (geometricRepresentativeTransformation B r).naturality π
  apply mate_model_square_of_factorizations
    (RA := rightDerivedLowerStar (ModuleCat.{u + 1} A) r)
    (RB := rightDerivedLowerStar (ModuleCat.{u + 1} B) r)
    (modelGeometricAdjunction A r) (modelGeometricAdjunction B r)
    (scalarPullbackIso φ r).hom (properAcyclicComparison A r C)
    (scalarExtensionRepresentative φ W C) (scalarExtensionRepresentative φ V D)
    (DerivedCategory.Q.map π) (properAcyclicComparison B r E)
    (scalarGeometricRepresentative A r D) (DerivedCategory.Q.map eA)
    (scalarExtensionRepresentative φ W
      (((upperStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj D))
    (DerivedCategory.Q.map eφ) (scalarGeometricRepresentative B r M)
    (DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ r).hom.app D))
    (scalarGeometricRepresentative B r H)
    (DerivedCategory.Q.map
      (((upperStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map π))
    (DerivedCategory.Q.map eB)
  · exact geometric_counit_comparison A r C
  · exact scalarExtensionRepresentative_naturality φ W eA
  · simpa only [scalarPullbackIso] using hn
  · simpa only [Functor.map_comp] using
      congrArg DerivedCategory.Q.map (properCoefficientComplexMap_counit φ r C).symm
  · exact hg
  · exact geometric_counit_comparison B r E

/-- A bounded acyclic flat model computes the canonical proper coefficient mate termwise.
The comparisons alpha_A and alpha_B are the canonical derived units on complexes;
the scalar-extension comparisons are the canonical flat-model counits. The displayed
square identifies the B-linear coefficient mate with the localization of pi_C.

Source: Stacks 0GL6, 015E, 0FND, 06YQ and 07A4
(blueprint: lem-sp-acyclic-flat-proper-coefficient-model).

Proof:
1. Apply the source-library bounded-flat K-flat theorem to C and its termwise
   direct image. The braiding supplies exactness of tensorLeft from tensorRight.
2. Positive derived homology of single sheaves identifies the terms as right-acyclic.
   The canonical bounded-below derived unit is invertible on these complexes, and
   compatibility with the unbounded derived unit proves the two acyclic comparisons.
3. Ordinary scalar extension followed by exact faithful restriction is tensorRight
   with the sheafified constant B-module. It therefore sends acyclic K-flat complexes
   to acyclic complexes. Its derived counit is invertible on K-flat models. The
   derived unit factorization and uniqueness of left adjoints identify this counit
   with each specified scalarExtensionRepresentative, proving invertibility.
4. The derived counit factorization computes the adjuncts of the acyclic comparisons.
   The defining normalization of scalarPullbackIso on the K-flat direct image model,
   naturality of scalar representatives, and the ordinary coefficient mate's counit
   identity give the same B-adjunct for both sides of the square. Injectivity of the
   derived hom equivalence proves that square, with all its prescribed comparisons.
5. Naturality of the ordinary mate, derived units, quotient factors and scalar units
   gives all six naturality equations. No flatness of B over A is used. -/
theorem acyclicFlatProperCoefficientModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {W V : Scheme.{u}} (r : W ⟶ V) [IsProper r] [IsNoetherian W] [IsNoetherian V]
    (φ : A →+* B)
    (C : CochainComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hC : IsAcyclicFlatProperCoefficientModel φ r C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ∧
      IsIso (properAcyclicComparison A r C) ∧
      IsIso (properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      IsIso (scalarExtensionRepresentative φ W C) ∧
      IsIso (scalarExtensionRepresentative φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ((properCoefficientTensor φ V).map (properAcyclicComparison A r C) ≫
          (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
            (scalarExtensionRepresentative φ W C) =
        scalarExtensionRepresentative φ V
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map (properCoefficientComplexMap φ r C) ≫
          properAcyclicComparison B r (coefficientExtendedComplex φ W C)) ∧
      (∀ (C' : CochainComplex
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (_hC' : IsAcyclicFlatProperCoefficientModel φ r C') (h : C ⟶ C'),
        (properCoefficientMap φ r).app (DerivedCategory.Q.obj C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              ((properCoefficientTensor φ W).map (DerivedCategory.Q.map h)) =
          (properCoefficientTensor φ V).map
              ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
                (DerivedCategory.Q.map h)) ≫
            (properCoefficientMap φ r).app (DerivedCategory.Q.obj C') ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properAcyclicComparison A r C' =
          properAcyclicComparison A r C ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map (DerivedCategory.Q.map h) ∧
        DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ≫
            properAcyclicComparison B r (coefficientExtendedComplex φ W C') =
          properAcyclicComparison B r (coefficientExtendedComplex φ W C) ≫
            (rightDerivedLowerStar (ModuleCat.{u + 1} B) r).map
              (DerivedCategory.Q.map
                (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) ∧
        (properCoefficientTensor φ W).map (DerivedCategory.Q.map h) ≫
            scalarExtensionRepresentative φ W C' =
          scalarExtensionRepresentative φ W C ≫ DerivedCategory.Q.map
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h) ∧
        (properCoefficientTensor φ V).map (DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ≫
            scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C') =
          scalarExtensionRepresentative φ V
              (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).obj C) ≫
            DerivedCategory.Q.map
              (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
                (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h)) ∧
        ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map
            (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h) ≫
            properCoefficientComplexMap φ r C' =
          properCoefficientComplexMap φ r C ≫
            ((lowerStar (ModuleCat.{u + 1} B) r).mapHomologicalComplex (.up ℤ)).map
              (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h)) := by
  obtain ⟨hKC, hKD⟩ := model_kFlat φ r C hC
  obtain ⟨a, b, hbound⟩ := hC.1
  have hA := properAcyclicComparison_isIso A r C
    ⟨a, fun n hn ↦ hbound n (Or.inl hn)⟩ hC.2.2.2.1
  have hB := properAcyclicComparison_isIso B r (coefficientExtendedComplex φ W C)
    ⟨a, fun n hn ↦ (ProEtale.etaleSheafExtendScalars φ W).map_isZero
      (hbound n (Or.inl hn))⟩ hC.2.2.2.2
  refine ⟨hKC, hKD, hA, hB, scalarExtensionRepresentative_isIso φ W C hKC,
    scalarExtensionRepresentative_isIso φ V _ hKD, ?_, ?_⟩
  · exact properCoefficientModel_square φ r C hKD
  · intro C' _ h
    refine ⟨?_, properAcyclicComparison_naturality A r h,
      properAcyclicComparison_naturality B r
        (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).map h),
      scalarExtensionRepresentative_naturality φ W h,
      scalarExtensionRepresentative_naturality φ V
        (((lowerStar (ModuleCat.{u + 1} A) r).mapHomologicalComplex (.up ℤ)).map h),
      (properCoefficientComplexTransformation φ r).naturality h⟩
    exact ((properCoefficientMap φ r).naturality (DerivedCategory.Q.map h)).symm

end AlgebraicGeometry.Etale

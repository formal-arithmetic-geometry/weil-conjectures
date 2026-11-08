/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Submission.WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Submission.WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all Submission.WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all Submission.WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all Submission.WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Submission.WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Submission.WeilConjectures.Algebra.Homology.InternalHom
import all Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
import all Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all Submission.WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedOrdinaryEvaluationLocalization
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Identification of ringed and native K-flat tensor models

Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YT, 06YU and 0FPT.
(blueprint: lem-pd-ringed-kflat-native-model-identification).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w d h

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
open scoped ZeroObject

namespace CategoryTheory.RingedKFlatModel

private theorem isoPair {D : Type d} [Category.{h} D]
    {X Y Z W : D} (f : X ⟶ Y) (g : Z ⟶ W) [IsIso f] [IsIso g] :
    @IsIso (D × D) _ (X, Z) (Y, W) (f, g) :=
  (isIso_prod_iff (f := ((f, g) : (X, Z) ⟶ (Y, W)))).mpr ⟨inferInstance, inferInstance⟩

attribute [local instance] isoPair

section ConstraintPaths
variable {D : Type d} [Category.{h} D]

private theorem map_eq {B : Type*} [Category B] (F : B ⥤ D)
    {X Y : B} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g := congrArg F.map h

private theorem map_eq_comp {B : Type*} [Category B] (F : B ⥤ D)
    {X Y : B} {f g : X ⟶ Y} {Z : D} (k : F.obj Y ⟶ Z)
    (h : f = g) : F.map f ≫ k = F.map g ≫ k := congrArg (fun t ↦ F.map t ≫ k) h

end ConstraintPaths

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The existing abstract native tensor, with its monoidal instance explicitly named.
Source: Stacks 06YU, 0FPT (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
def nativeTensor :=
  @tensor (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
    (RingedDerivedNative.monoidal.{c, v, u, w} J R)

variable
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
  (T : CoefficientTensorModels.{u, c, v, w} J R S)

/-- The resolving-pair normalization determining a tensor comparison uniquely.
Source: Stacks 06YS, 06YU (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
def Normalized (e : nativeTensor.{c, v, u, w} J R ≅ S.tensor) : Prop :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X n)) →
    (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
      e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        (T.iso J R S P Q hP hQ).hom

/-- The type of all-complex localization transformations for the given ringed tensor.
Source: Stacks 06YU (blueprint: lem-pd-ringed-kflat-native-model-identification). -/
abbrev Localization :=
  (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ S.tensor ⟶
    coefficientTotalTensor.{u, c, v} J R ⋙ DerivedCategory.Q.{w}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorCache :
    ∀ (X Y : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)), X.HasTensor Y :=
  RingedDerivedNative.gradedTensor.{c, v, u} J R

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorFourCache :
    ∀ (W X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasTensor₄ObjExt W X Y Z :=
  RingedDerivedNative.gradedTensorFour.{c, v, u} J R

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorLeftCache :
    ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  RingedDerivedNative.gradedTensorLeft.{c, v, u} J R

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private theorem gradedTensorRightCache :
    ∀ (X Y Z : GradedObject ℤ (RingedTensorModules.{c, v, u} J R)),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  RingedDerivedNative.gradedTensorRight.{c, v, u} J R

attribute [local instance 10000] gradedTensorCache gradedTensorFourCache
  gradedTensorLeftCache gradedTensorRightCache

@[reducible]
private def complexMonoidal :
    MonoidalCategory (CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) := inferInstance

@[reducible]
private def derivedMonoidal :
    MonoidalCategory (DerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)) :=
  RingedDerivedNative.monoidal.{c, v, u, w} J R

attribute [local instance 10000] complexMonoidal derivedMonoidal

@[reducible]
private def complexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :=
  (complexMonoidal.{c, v, u} J R).toMonoidalCategoryStruct

attribute [local instance 10000] complexMonoidalStruct

@[no_expose]
private def chainLeftUnitor
    (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    (coefficientTotalTensor.{u, c, v} J R).obj
      (ringedTensorUnitComplex.{c, v, u} J R, P) ≅ P :=
  HomologicalComplex.leftUnitor P

private theorem associator_model_native
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P Q N : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hN : N.IsKFlatIndependentCoefficients) :
    (hc.tensorIso ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) N (Or.inr hN)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)),
          DerivedCategory.Q.{w}.obj N))
        (Y := (S.tensor.obj (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj Q),
          DerivedCategory.Q.{w}.obj N))
        ((T.iso J R S P Q hP hQ).hom, 𝟙 _) ≫
        (S.monoidal.associator (DerivedCategory.Q.{w}.obj P) (DerivedCategory.Q.{w}.obj Q)
          (DerivedCategory.Q.{w}.obj N)).hom =
      DerivedCategory.Q.{w}.map (CategoryTheory.ordinaryAssociator.{c, v, u} J R P Q N).hom ≫
        (hc.tensorIso P ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N)) (Or.inl hP)).hom ≫
          S.tensor.map
            (X := (DerivedCategory.Q.{w}.obj P, DerivedCategory.Q.{w}.obj
              ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N))))
            (Y := (DerivedCategory.Q.{w}.obj P,
              S.tensor.obj (DerivedCategory.Q.{w}.obj Q, DerivedCategory.Q.{w}.obj N)))
            (𝟙 _, (T.iso J R S Q N hQ hN).hom) := by
  obtain ⟨a, ha, he⟩ := hc.associator_model P Q N hP hQ hN
  have heq : a.hom = (CategoryTheory.ordinaryAssociator.{c, v, u} J R P Q N).hom :=
    CategoryTheory.ordinaryAssociator_unique.{c, v, u} J R P Q N a.hom ha
  exact he.trans (map_eq_comp DerivedCategory.Q.{w} _ heq)

private theorem leftUnitor_model_native
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    (hc.tensorIso (ringedTensorUnitComplex.{c, v, u} J R) P (Or.inr hP)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj (ringedTensorUnitComplex.{c, v, u} J R),
          DerivedCategory.Q.{w}.obj P))
        (Y := (S.monoidal.tensorUnit, DerivedCategory.Q.{w}.obj P))
        (hc.unitIso.inv, 𝟙 _) ≫
        (S.monoidal.leftUnitor (DerivedCategory.Q.{w}.obj P)).hom =
      DerivedCategory.Q.{w}.map (chainLeftUnitor.{c, v, u} J R P).hom := by
  obtain ⟨l, hl, he⟩ := hc.leftUnitor_model P hP
  have heq : l.hom = (chainLeftUnitor.{c, v, u} J R P).hom := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := ringedTensorUnitComplex.{c, v, u} J R) (K₂ := P)
      (F := curriedTensor (RingedTensorModules.{c, v, u} J R)) (c := .up ℤ)
    intro p q hpq
    change p + q = k at hpq
    by_cases hp : p = 0
    · subst p
      have hk : k = q := by omega
      subst q
      apply CategoryTheory.pure_ext.{c, v, u} J R
        ((ringedTensorUnitComplex.{c, v, u} J R).X 0) (P.X k) (P.X k)
      intro U a x
      exact (hl k (zero_add k) U a x).trans
        ((RingedDerivedNative.complexConstraints.{c, v, u} J R).leftUnitor
          P k (zero_add k) U a x).symm
    · apply IsZero.eq_of_src
      exact (tensorRight (P.X q)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)
  exact he.trans (map_eq DerivedCategory.Q.{w} heq)

private theorem rightUnitor_model_native
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) :
    (hc.tensorIso P (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl hP)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.{w}.obj P,
          DerivedCategory.Q.{w}.obj (ringedTensorUnitComplex.{c, v, u} J R)))
        (Y := (DerivedCategory.Q.{w}.obj P, S.monoidal.tensorUnit))
        (𝟙 _, hc.unitIso.inv) ≫
        (S.monoidal.rightUnitor (DerivedCategory.Q.{w}.obj P)).hom =
      DerivedCategory.Q.{w}.map (CategoryTheory.ordinaryRightUnitor.{c, v, u} J R P).hom := by
  obtain ⟨r, hr, he⟩ := hc.rightUnitor_model P hP
  have heq : r.hom = (CategoryTheory.ordinaryRightUnitor.{c, v, u} J R P).hom :=
    CategoryTheory.ordinaryRightUnitor_unique.{c, v, u} J R P r.hom hr
  exact he.trans (map_eq DerivedCategory.Q.{w} heq)

-- Preserve the recorded signature, whose second K-flat proof fixes the allowed model pairs.
end CategoryTheory.RingedKFlatModel

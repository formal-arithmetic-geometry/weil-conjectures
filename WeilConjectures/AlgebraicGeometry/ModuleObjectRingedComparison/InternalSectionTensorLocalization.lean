/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionDerivedTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSliceDerivedHomComparison
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization

/-! # Localization of the sectionwise tensor comparison

Source: Stacks Project, Tags 03CV, 03EK, 06YL, 06YS and 08J9
(blueprint: lem-sfb-internal-section-tensor-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local irreducible] CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Mod.monoidalClosed
attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local implicit_reducible] GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory

section Ordinary

variable {A B : Type*} [Category A] [Category B]
  [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B)
  (e : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
  (e₀ : F.obj (𝟙_ A) ≅ 𝟙_ B)
  (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
    F.map (f ⊗ₘ g) ≫ (e M' N').hom =
      (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
  (ha : ∀ M N P, (e (M ⊗ N) P).hom ≫ (e M N).hom ▷ F.obj P ≫ (α_ _ _ _).hom =
    F.map (α_ M N P).hom ≫ (e M (N ⊗ P)).hom ≫ F.obj M ◁ (e N P).hom)
  (hl : ∀ M, (e (𝟙_ A) M).hom ≫ e₀.hom ▷ F.obj M ≫ (λ_ _).hom =
    F.map (λ_ M).hom)
  (hr : ∀ M, (e M (𝟙_ A)).hom ≫ F.obj M ◁ e₀.hom ≫ (ρ_ _).hom =
    F.map (ρ_ M).hom)

end Ordinary

attribute [local irreducible] ordinaryMonoidal

section MonoidalSquare

variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
  (q : C ⥤ D) (r : E ⥤ H) (f : C ⥤ E) (g : D ⥤ H)
  [q.LaxMonoidal] [r.LaxMonoidal] [f.Monoidal] [g.Monoidal]
  (k : q ⋙ g ≅ f ⋙ r) [NatTrans.IsMonoidal k.hom]

end MonoidalSquare

section Abstract

universe a b
variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  (F : A ⥤ B) [F.Additive] [F.Monoidal] [F.IsEquivalence]

end Abstract

attribute [local instance 1000001] sectionRingHasSheafCompose
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

section NormalizationUncurry
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃
variable {C₀ : Type u₀} [Category.{v₀} C₀] {D₀ : Type u₁} [Category.{v₁} D₀]
  {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
  {D : Type u₃} [Category.{v₃} D]
  {qC : C₀ ⥤ C} {qD : D₀ ⥤ D} {f₀ : C₀ ⥤ D₀} {f : C ⥤ D}
  {factor : qC ⋙ f ≅ f₀ ⋙ qD}
  {t₀ : C₀ × C₀ ⥤ C₀} {s : D × D ⥤ D} {s₀ : D₀ × D₀ ⥤ D₀}
  {μ : ∀ P Q : C₀,
    (MonoidalCategory.tensor C).obj (qC.obj P, qC.obj Q) ⟶ qC.obj (t₀.obj (P, Q))}
  {c₀ : ∀ P Q : C₀, f₀.obj (t₀.obj (P, Q)) ≅ s₀.obj (f₀.obj P, f₀.obj Q)}
  {flat : D₀ → Prop}
  {model : ∀ (P Q : D₀), flat P → flat Q →
    (qD.obj (s₀.obj (P, Q)) ≅ s.obj (qD.obj P, qD.obj Q))}
  {c : MonoidalCategory.tensor C ⋙ f ≅ (f.prod f) ⋙ s}

end NormalizationUncurry

section Ringed

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

variable {A : Type*} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  (F : A ⥤ SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  [F.Additive] [F.IsEquivalence] [fMonoidal : F.Monoidal]

variable
  (raw : ∀ P Q : CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} J R).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P,
          (F.mapHomologicalComplex (.up ℤ)).obj Q))
  (hraw : ∀ (P Q : CochainComplex A ℤ) (p q n : ℤ) (h : p + q = n),
    F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (raw P Q).hom.f n =
      Functor.OplaxMonoidal.δ F (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)

end Ringed

attribute [local implicit_reducible] ringedMonoidal RingedDerivedNative.moduleMonoidal
  SheafOfModules.cochainModulesMonoidal ringedSymmetric RingedDerivedNative.moduleSymmetric
  SheafOfModules.cochainModulesSymmetric

attribute [local instance 30000] ringedComplexTensor

attribute [local implicit_reducible] Sheaf.symmetricCategory Sheaf.braidedCategory

attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategoryCochainComplex
  CategoryTheory.Mod.derivedMonoidalCategory CategoryTheory.Mod.laxMonoidalQ
  internalComplexMonoidal sliceCochainMonoidal

section Generic
set_option backward.isDefEq.respectTransparency true

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [(J.W (A := AddCommGrpCat.{u + 1})).IsMonoidal]

attribute [local instance 30001] Sheaf.monoidalCategory
attribute [local instance 30002] Sheaf.symmetricCategory
attribute [local instance 30000] sectionComparisonBraiding

variable
  (R : Sheaf J AddCommGrpCat.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R]

open CategoryTheory.InternalAbelianSheafModule

attribute [local irreducible] sectionModuleFunctor
attribute [local implicit_reducible] sectionModuleEquivalence

attribute [local irreducible] comparison_tensorIso comparison_unitIso

variable
  [sourceClosed : MonoidalClosed (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]
  [sourceGroth : IsGrothendieckAbelian.{u + 1} (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]
  [sourceFlat : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]

end Generic

open CategoryTheory.InternalAbelianSheafModule

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

attribute [local irreducible] complexTensorIso totalComparison ordinaryTensorIso
  CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor

attribute [local implicit_reducible] hom forward localizationIso localizationTensorMap
  complexForward internalTotalTensor sliceDerivedForward sliceComplexForward
  sliceDerivedLocalizationIso sliceLocalizationTensorMap sliceNativeTensor

attribute [local irreducible] sliceEquivalence sliceRingObject
attribute [local instance] ringedMonoidal ringedSymmetric ringedPreadditive
  ringedClosed ringedGrothendieck ringedFlat

attribute [local instance] sectionFunctorAdditive sectionFunctorEquivalence
attribute [local implicit_reducible] sectionModuleEquivalence

set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.IntegralReductionTransitionSemilinear
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all WeilConjectures.CategoryTheory.InjectiveTowerRoos.InjectiveTowerRoosShifts
import WeilConjectures.CategoryTheory.Derived.DerivedInjectiveResolutionNaturality
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.CategoryTheory.Flat.FlatRoosFunctorDescent
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

import all WeilConjectures.SecSmoothPurity.StrictCoefficient.ScalarCalculation.NormalizedScalarTensorTransitionsSupplement
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined

/-! # Well-definedness of integral pullback and completed tensor product

Source: Stacks Project, Tags 06YS, 06YT, 0G7E and 08TC; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9(4)
(blueprint: lem-pur-integral-operations-well-defined).

The natural-number level n denotes exponent n+1. All towers and their maps are
constructed before localization; the Roos complex uses termwise products and the
specified shifted cone. The final descent includes its natural comparison data.

## Main definitions

* `integralOperationsPullbackComplexFunctor`: strict finite pullback followed by Roos.
* `integralOperationsTensorComplexFunctor`: direct-sum finite tensor followed by Roos.

## Main statements

* `integralOperationsWellDefined`: quasi-isomorphism invariance and normalized descent.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 512

universe t u a b c d r a' b' c' d'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

-- Prefer the module's recorded tensor instances during private proof search.
attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits

-- These proof imports carry broad diagram instances; prefer the concrete instances here.
attribute [local instance 1] CategoryTheory.CochainPullback.RingedPullback.additive
  CategoryTheory.CochainPullback.CoefficientSquare.additive'
  CategoryTheory.CochainPullback.StrictCoefficient.Diagram.additive
  CategoryTheory.CochainPullback.extensionFunctorAdditive

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe wForget uForget vForget

open WeilConjectures

attribute [local instance 2000] SheafOfModules.integralOperationsRestrictScalarsZero

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] coefficientProEtaleDirectRingMap
end AlgebraicGeometry.Scheme

attribute [local irreducible] constantSheaf HasDerivedCategory.standard limit

namespace SheafOfModules.IntegralScalarProof
variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {S T : Sheaf J RingCat.{r}} (q : S ⟶ T)
  (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)

section Composition

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
  (hq : f ≫ q = g) (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
include hq in
private theorem coefficient_comp (U : Cᵒᵖ) (s : R.obj.obj U) :
    q.hom.app U (f.hom.app U s) = g.hom.app U s :=
  ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hq) s
private noncomputable def restrictMap (φ : M ⟶ (restrictScalars q).obj N) :
    (restrictScalars f).obj M ⟶ (restrictScalars g).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((restrictScalars f).obj M).val.obj U)
        (Y := ((restrictScalars g).obj N).val.obj U)
        { toFun := φ.val.app U
          map_add' := _root_.map_add _
          map_smul' := fun s x ↦ by
            change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
              g.hom.app U s • (show N.val.obj U from φ.val.app U x)
            have h := (φ.val.app U).hom.map_smul (f.hom.app U s) (show M.val.obj U from x)
            change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
              q.hom.app U (f.hom.app U s) • (show N.val.obj U from φ.val.app U x) at h
            rw [coefficient_comp f g q hq] at h
            exact h }
      naturality := by
        intro U V a
        ext x
        exact PresheafOfModules.naturality_apply φ.val a x }

private noncomputable def restrictComplexMap
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q) :
    (WeilConjectures.integralOperationsRestrictionComplex f).obj P ⟶
      (WeilConjectures.integralOperationsRestrictionComplex g).obj Q where
  f j := restrictMap f g q hq (P.X j) (Q.X j) (φ.f j)
  comm' i j _ := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) (φ.comm i j)

private theorem restrictComplexMap_naturality
    {P P' : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q Q' : CochainComplex (SheafOfModules.{r} T) ℤ}
    (a : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (b : P' ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q')
    (u : P ⟶ P') (v : Q ⟶ Q')
    (h : u ≫ b = a ≫ (WeilConjectures.integralOperationsRestrictionComplex q).map v) :
    (WeilConjectures.integralOperationsRestrictionComplex f).map u ≫
        restrictComplexMap f g q hq b =
      restrictComplexMap f g q hq a ≫
        (WeilConjectures.integralOperationsRestrictionComplex g).map v := by
  apply HomologicalComplex.hom_ext
  intro i
  ext U x
  exact congrArg (fun z ↦ (z.f i).val.app U x) h

end Composition

end SheafOfModules.IntegralScalarProof

namespace SheafOfModules.IntegralPullbackProof
variable {C : Type c} [Category.{d} C] {D : Type c'} [Category.{d'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R₀ R₁ : Sheaf K RingCat.{r}} {S₀ S₁ : Sheaf J RingCat.{r}}
  (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
  (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₀)
  (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₁)
  (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map qR)
private noncomputable def pushRestrictionIso :
    restrictScalars.{r} qR ⋙ pushforward φ₀ ≅
      pushforward φ₁ ⋙ restrictScalars qS :=
  pushforwardComp (G := 𝟭 D) φ₀ qR ≪≫ pushforwardCongr h.symm ≪≫
    (pushforwardComp (F := 𝟭 C) qS φ₁).symm
end SheafOfModules.IntegralPullbackProof

namespace IntegralMateProof
variable {A : Type a} [Category.{a'} A] {B : Type b} [Category.{b'} B]
  {C : Type c} [Category.{c'} C] {D : Type d} [Category.{d'} D]
  {L : A ⥤ B} {G : B ⥤ A} {L' : C ⥤ D} {G' : D ⥤ C}
  (adj : L ⊣ G) (adj' : L' ⊣ G') (U : C ⥤ A) (V : D ⥤ B)
  (e : V ⋙ G ≅ G' ⋙ U)
private def mate {M : A} {N : C} (f : M ⟶ U.obj N) : L.obj M ⟶ V.obj (L'.obj N) :=
  (adj.homEquiv _ _).symm (f ≫ U.map (adj'.unit.app N) ≫ e.inv.app (L'.obj N))
end IntegralMateProof

namespace SheafOfModules.IntegralPullbackProof
variable {C : Type c} [Category.{d} C] {D : Type c'} [Category.{d'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R₀ R₁ : Sheaf K RingCat.{r}} {S₀ S₁ : Sheaf J RingCat.{r}}
  (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
  (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₀)
  (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₁)
  (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map qR)
  {L₀ : SheafOfModules.{r} S₀ ⥤ SheafOfModules.{r} R₀}
  {L₁ : SheafOfModules.{r} S₁ ⥤ SheafOfModules.{r} R₁}
  (adj₀ : L₀ ⊣ pushforward φ₀) (adj₁ : L₁ ⊣ pushforward φ₁)

private noncomputable def mateData {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) :
    L₀.obj M ⟶ (restrictScalars qR).obj (L₁.obj N) :=
  IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
    (pushRestrictionIso F qR qS φ₀ φ₁ h) a

end SheafOfModules.IntegralPullbackProof

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.IntegralPullbackProof.mateData
  SheafOfModules.IntegralPullbackProof.pushRestrictionIso
  IntegralMateProof.mate

private theorem integralHasMap
    {A : Type a} [Category.{b} A] [Preadditive A] [MonoidalCategory A]
    [(MonoidalCategory.curriedTensor A).PreservesZeroMorphisms]
    [∀ M : A, ((MonoidalCategory.curriedTensor A).obj M).PreservesZeroMorphisms]
    [HasCountableCoproducts A] (P Q : CochainComplex A ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor A) (.up ℤ) := by
  infer_instance

private theorem scalarRestrictionAdditive
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) :
    (SheafOfModules.restrictScalars.{r} α).Additive := by
  infer_instance

namespace WeilConjectures

section PrivateTensorTransition
attribute [local semireducible] constantSheaf HasDerivedCategory.standard limit
  SheafOfModules.tensorObjIsoSheafification
attribute [-instance] SheafOfModules.integralOperationsRestrictScalarsZero
set_option backward.isDefEq.respectTransparency true
attribute [local instance 2001] scalarRestrictionAdditive
attribute [local instance] CategoryTheory.CochainPullback.RingedPullback.additive
  CategoryTheory.CochainPullback.CoefficientSquare.additive'
  CategoryTheory.CochainPullback.StrictCoefficient.Diagram.additive
  CategoryTheory.CochainPullback.extensionFunctorAdditive
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2001] integralHasMap
attribute [local instance 3001]
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.tensorCoproducts
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.hasTensorTotal

universe v u' v'

namespace TensorTotalProof
open MonoidalCategory
variable {C : Type a} [Category.{b} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).PreservesZeroMorphisms]
  [∀ X : C, ((curriedTensor C).obj X).PreservesZeroMorphisms]
  {P Q A B : CochainComplex C ℤ}
private theorem totalTensor_map
    (a : P ⟶ A) (b : Q ⟶ B)
    [∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)] :
    (Functor.uncurry.obj (curriedTensor C).map₂CochainComplex).map
      (X := (P, Q)) (Y := (A, B)) (a, b) =
      HomologicalComplex.mapBifunctorMap a b (curriedTensor C) (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap a (𝟙 Q) _ _ ≫
    HomologicalComplex.mapBifunctorMap (𝟙 A) b _ _ = _
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

private theorem composite_map
    {D : Type a'} [Category.{b'} D] {B : Type c} [Category.{d} B]
    [HasZeroMorphisms B] (F : D ⥤ CochainComplex C ℤ) (R : C ⥤ B)
    [R.PreservesZeroMorphisms]
    [∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]
    {K L : D × D} (u : K ⟶ L) :
    (integralOperationsTensorComposite F R).map u =
      (R.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (F.map u.1) (F.map u.2)
          (curriedTensor C) (.up ℤ)) := by
  exact congrArg (R.mapHomologicalComplex (.up ℤ)).map
    (totalTensor_map (F.map u.1) (F.map u.2))

end TensorTotalProof

section SignedTensorConstruction

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction

open MonoidalCategory

variable (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)

section GenericTensor

set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.monoidalCategory

@[no_expose] private noncomputable def pureTensor
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv.val.app U
    ((toSheafify J (M.val ⊗ N.val).presheaf).app U (x ⊗ₜ[R.obj.obj U] y))

-- Explicit section maps avoid comparing the two coefficient-ring constructions in coercions.

end GenericTensor

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

namespace TensorChainProof
open CategoryTheory.CochainPullback
open CategoryTheory.CochainPullback.StrictCoefficient
open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
attribute [local instance 2000] SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
  SheafOfModules.cochainModulesMonoidal
  GrothendieckTopology.hasSheafify_of_essentiallySmall
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
  (R S : Sheaf J CommRingCat.{r}) (α : R ⟶ S)

attribute [local instance] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory

private theorem totalMap_eq {A : Sheaf J CommRingCat.{r}}
    {P Q X Y : Complex A} (f : P ⟶ X) (g : Q ⟶ Y) :
    tensorTotalMap f g =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (Modules A)) (.up ℤ) := rfl

@[no_expose] private noncomputable def chainAdjunction :=
  (extensionAdjunction α).mapHomologicalComplex (.up ℤ)

@[no_expose] private noncomputable def transpose {K : Complex R} {L : Complex S}
    (f : K ⟶ (restrictComplex α).obj L) : (extend α).obj K ⟶ L :=
  (chainAdjunction R S α).homEquiv K L |>.symm <| f

private theorem transpose_section {K : Complex R} {L : Complex S}
    (f : K ⟶ (restrictComplex α).obj L) (p : ℤ) (U : Cᵒᵖ) (x : (K.X p).val.obj U) :
    ((transpose R S α f).f p).val.app U
      (extensionTmul α (K.X p) U 1 x) = (f.f p).val.app U x := by
  have h := congrArg (fun z ↦ (z.f p).val.app U x)
    ((chainAdjunction R S α).homEquiv K L
      |>.apply_symm_apply f)
  rw [Adjunction.homEquiv_unit] at h
  change ((transpose R S α f).f p).val.app U
    (((extensionAdjunction α).unit.app (K.X p)).val.app U x) = _ at h
  rw [KappaCalculation.extension_unit] at h
  exact h

@[no_expose] private noncomputable def map
    {P Q : CochainPullback.Complex R} {P' Q' : CochainPullback.Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q') :
    total P Q ⟶ (restrictComplex α).obj (total P' Q') :=
  (chainAdjunction R S α).unit.app (total P Q) ≫
    (restrictComplex α).map
      ((tensorComparison (extensionPullback α) (extensionComparison α) P Q).hom ≫
        tensorTotalMap (transpose R S α a) (transpose R S α b))

private theorem pure
    {P Q : CochainPullback.Complex R} {P' Q' : CochainPullback.Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q') (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) :
    ((map R S α a b).f (p+q)).val.app U
      (totalPure P Q p q (p+q) rfl U x y) =
    totalPure P' Q' p q (p+q) rfl U
      ((a.f p).val.app U x) ((b.f q).val.app U y) := by
  change ((tensorTotalMap (transpose R S α a) (transpose R S α b)).f (p+q)).val.app U
    (((tensorComparison (extensionPullback α) (extensionComparison α) P Q).hom.f
      (p+q)).val.app U
      (((extensionAdjunction α).unit.app ((total P Q).X (p+q))).val.app U
        (totalPure P Q p q (p+q) rfl U x y))) = _
  rw [KappaCalculation.extension_unit, scalarTotal_hom, totalMap_pure,
    transpose_section, transpose_section]
attribute [local irreducible] map transpose
private theorem map_naturality
    {P Q X Y : Complex R} {P' Q' X' Y' : Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q')
    (a' : X ⟶ (restrictComplex α).obj X')
    (b' : Y ⟶ (restrictComplex α).obj Y')
    (f : P ⟶ X) (g : Q ⟶ Y) (f' : P' ⟶ X') (g' : Q' ⟶ Y')
    (ha : f ≫ a' = a ≫ (restrictComplex α).map f')
    (hb : g ≫ b' = b ≫ (restrictComplex α).map g') :
    tensorTotalMap f g ≫ map R S α a' b' =
      map R S α a b ≫ (restrictComplex α).map (tensorTotalMap f' g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply tensor_hom_ext
  intro U x y
  subst n
  change ((map R S α a' b').f (p+q)).val.app U
    (((tensorTotalMap f g).f (p+q)).val.app U
      (totalPure P Q p q (p+q) rfl U x y)) =
    ((tensorTotalMap f' g').f (p+q)).val.app U
      (((map R S α a b).f (p+q)).val.app U
        (totalPure P Q p q (p+q) rfl U x y))
  rw [totalMap_pure, pure, pure, totalMap_pure]
  exact congrArg₂ (totalPure X' Y' p q (p+q) rfl U)
    (congrArg (fun k ↦ (k.f p).val.app U x) ha)
    (congrArg (fun k ↦ (k.f q).val.app U y) hb)

end TensorChainProof

attribute [local irreducible] TensorChainProof.map TensorChainProof.transpose
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.tensorTotalMap
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.totalPure

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

namespace TensorNaturalProof
open CategoryTheory.CochainPullback
open CategoryTheory.CochainPullback.StrictCoefficient
open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
open MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.monoidalPreadditive_independent
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {D : Type c} [Category.{d} D]
  {R₀ : Sheaf J RingCat.{r}} (S T : Sheaf J CommRingCat.{r})
  (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
  (g : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj T)
  (q₀ : S ⟶ T)
  (hq₀ : f ≫ ((integralOperationsForgetSheaf J).map q₀) = g)
  (F : D ⥤ CochainComplex (SheafOfModules.{r}
    ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
  (G : D ⥤ CochainComplex (SheafOfModules.{r}
    ((integralOperationsForgetSheaf.{r} J).obj T)) ℤ)
  (θ : F ⟶ G ⋙ integralOperationsRestrictionComplex ((integralOperationsForgetSheaf J).map q₀))

@[no_expose] private noncomputable abbrev level
    (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
    (F : D ⥤ CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ) :
    D × D ⥤ CochainComplex (SheafOfModules.{r} R₀) ℤ :=
  integralOperationsTensorComposite F (SheafOfModules.restrictScalars f)

@[no_expose] private noncomputable def sectionPure
    (F : D ⥤ CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
    (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
    (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U) :
    ((total (F.obj P) (F.obj Q)).X (p + q)).val.obj U :=
  (integralOperationsSectionApply
    (tensorι (A := S) (F.obj P) (F.obj Q) p q (p+q) rfl) U)
    (pureTensor S _ _ U x y)

@[no_expose] private noncomputable def component (K : D × D) :
    (level S f F).obj K ⟶
      (level T g G).obj K :=
  SheafOfModules.IntegralScalarProof.restrictComplexMap f g ((integralOperationsForgetSheaf
    J).map q₀) hq₀
    (TensorChainProof.map S T q₀ (θ.app K.1) (θ.app K.2))

private theorem level_map_eq {K L : D × D} (a : K ⟶ L) :
    (level S f F).map a =
      (WeilConjectures.integralOperationsRestrictionComplex f).map
        (tensorTotalMap (F.map a.1) (F.map a.2)) := by
  exact (TensorTotalProof.composite_map F (SheafOfModules.restrictScalars f) a).trans
    (congrArg (WeilConjectures.integralOperationsRestrictionComplex f).map
      (TensorChainProof.totalMap_eq (F.map a.1) (F.map a.2)).symm)

@[no_expose] private noncomputable def candidate [Presheaf.IsLocallySurjective J f.hom] :
    level S f F ⟶ level T g G where
  app := component S T f g q₀ hq₀ F G θ
  naturality {K L} u := by
    rw [level_map_eq, level_map_eq]
    exact SheafOfModules.IntegralScalarProof.restrictComplexMap_naturality f g
      ((integralOperationsForgetSheaf J).map q₀) hq₀
      (TensorChainProof.map S T q₀ (θ.app K.1) (θ.app K.2))
      (TensorChainProof.map S T q₀ (θ.app L.1) (θ.app L.2))
      (tensorTotalMap (F.map u.1) (F.map u.2))
      (tensorTotalMap (G.map u.1) (G.map u.2))
      (TensorChainProof.map_naturality S T q₀ (θ.app K.1) (θ.app K.2)
        (θ.app L.1) (θ.app L.2) (F.map u.1) (F.map u.2) (G.map u.1) (G.map u.2)
        (θ.naturality u.1) (θ.naturality u.2))

attribute [local irreducible] component

end TensorNaturalProof

end SignedTensorConstruction

end PrivateTensorTransition

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients

attribute [local instance 2000] integralOperationsFiniteHasMap

section IntegralTensorTransitionProof

section FiniteLinearization

attribute [local irreducible] unrestrictedIntegralReductionExistence
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingProjectionUnrestricted

end FiniteLinearization

attribute [local irreducible]
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint

attribute [local irreducible] unrestrictedIntegralReductionExistence
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingProjectionUnrestricted

end IntegralTensorTransitionProof

section TensorTransitionSpecialization
attribute [local instance 2001] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

end TensorTransitionSpecialization

section Roos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

end Roos

attribute [local instance 3000] Algebra.toModule

-- Prefer the exact completed-module presentation during private proof search.
attribute [local instance 3000] integralTowerHasDerivedCategory

section IntegralOperationsRoosQuasiIsoInvariantProof
set_option Elab.async true

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

private theorem cofiberMap_eq_coneMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L K' L' : CochainComplex A ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      CochainComplex.mappingCone.map s s' a b h := by
  exact CategoryTheory.cofiberMap_eq_coneMap s s' a b h

/-- A levelwise quasi-isomorphism induces a quasi-isomorphism of strict Roos complexes.
Source: Stacks Project, Derived Categories, Tags 07KC, 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: exact countable products make the product of the component maps a
quasi-isomorphism. The commutative square for 1-s gives a morphism of the
mapping-cone triangles. Its first two components become isomorphisms under
localization, so the third does as well. Reflection by localization and shift
invariance give the assertion for the recorded diagonal shifted-cone map. -/
private theorem roosMap_quasiIso
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (α : C ⟶ C') (hα : ∀ n : ℕ, QuasiIso (α.app (op n))) :
    QuasiIso (integralOperationsRoosMap α) := by
  classical
  let p := Limits.Pi.map (fun n ↦ α.app (op n))
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n ↦ C.obj (op n)))
        (G := Discrete.functor (fun n ↦ C'.obj (op n)))
        (fun n ↦ α.app (op n.as))).app n) := hα n.as
  have hp : QuasiIso p := HomologicalComplex.quasiIso_limMap
    (Discrete.natTrans (F := Discrete.functor (fun n ↦ C.obj (op n)))
      (G := Discrete.functor (fun n ↦ C'.obj (op n))) (fun n ↦ α.app (op n.as)))
  let s := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
    (integralOperationsTowerStep C)
  let s' := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
    (integralOperationsTowerStep C')
  have hcone : QuasiIso (CochainComplex.mappingCone.map s s' p p
      (integralOperationsRoos_square α)) :=
    CochainComplex.mappingCone.quasiIso_map_of_quasiIso s s' p p
      (integralOperationsRoos_square α)
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square α)]
  infer_instance

end IntegralOperationsRoosQuasiIsoInvariantProof

section IntegralOperationsPullbackQuasiIsoInvariantProof

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local irreducible] SheafOfModules.monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRestriction_exact
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ) := by
  let U := SheafOfModules.restrictScalars.{u} φ
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf R)⟩

set_option backward.isDefEq.respectTransparency false

end IntegralOperationsPullbackQuasiIsoInvariantProof

section IntegralOperationsTensorQuasiIsoInvariantProof

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence

namespace IntegralTensorProof

universe x y z

open SheafOfModules MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

end IntegralTensorProof

set_option backward.isDefEq.respectTransparency false

end IntegralOperationsTensorQuasiIsoInvariantProof

section IntegralOperationsGoodLocalizationProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Good completed-coefficient complexes localize to the entire derived category.
Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YT.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: the canonical functorial flat cover gives a reduced left resolution functor.
Its filtered-colimit construction has flat terms and is K-flat, and its natural
augmentation is a quasi-isomorphism. The inclusion of good complexes is fully
faithful. The augmentation and its restriction to good complexes give inverse
localized functors, so the inclusion is a localized equivalence. Composing with
the standard derived localization gives the claimed localization. -/
private theorem goodComplexes_isLocalization
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{u}]
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u}
      ((integralOperationsForgetSheaf.{u} J).obj R))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((integralOperationsForgetSheaf.{u} J).obj R)) ℤ))
    (hp : ∀ K, P K ↔ CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (K.X i)) :
    (P.ι ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage P.ι) := by
  have hP : P = CategoryTheory.TensorFlatRepresentative (J := J) (R := R) := by
    funext K
    exact propext (hp K)
  subst P
  exact CategoryTheory.flat_representative_localization J R

end IntegralOperationsGoodLocalizationProof

section IntegralOperationsTensorDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsPullbackOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

end IntegralOperationsTensorDescentProof

section IntegralOperationsComparisonExistsProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

end IntegralOperationsComparisonExistsProof

section IntegralOperationsNormalizedDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsPullbackOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

end IntegralOperationsNormalizedDescentProof

section IntegralOperationsRoosDerivedLimitProof

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

end IntegralOperationsRoosDerivedLimitProof

section IntegralOperationsDerivedDescentProof

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

end IntegralOperationsDerivedDescentProof

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsDerivedLimitProperty
  integralOperationsGoodComplex integralOperationsGoodLocalization
  integralOperationsPullbackOnGood

end WeilConjectures

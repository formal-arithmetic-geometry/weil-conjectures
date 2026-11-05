/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
/-! # Normalized tensor comparison for scalar extension

Source: Stacks Project, Tags 07A4 and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- A pure scalar-extension section, transported along the specified object equality.
It is the sheafification unit applied to s tensor x; no basis is used.
Source: Stacks 03EK, 08J9
(blueprint: lem-sf-ringed-finite-free-hom-base-change). -/
def ringedFiniteFreeScalarSection
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U)
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

open SheafOfModules WeilConjectures CategoryTheory.MonoidalCategory

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory coefficientTotalTensor

private theorem scalarComparison_natural
    [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
    (M : ScalarHomModels.{c, v, r, w} J) (μ : ScalarHomTensorComparison M φ)
    {P P' Q Q' : CochainComplex (scalarModules J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    ((scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive).map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g))) ≫
        (μ.complexIso P' Q').hom =
      (μ.complexIso P Q).hom ≫ (coefficientTotalTensor.{r, c, v} J S).map
        (Prod.mkHom
          ((scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive).map f)
          ((scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive).map g)) := by
  let s := M.scalar φ
  let := s.extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  apply (s.ordinaryAdjunction.homEquiv _ _).injective
  apply ScalarHomTensor.total_pure_hom_ext
  intro p q h V x y
  have hu {X Y : scalarModules J R} (a : X ⟶ Y) (z : X.val.obj V) :
      (s.extension.map a).val.app V (scalarHomUnitSection M φ X V z) =
        scalarHomUnitSection M φ Y V (a.val.app V z) :=
    (congrArg (fun k ↦ k.val.app V z) (s.ordinaryAdjunction.unit.naturality a)).symm
  change ((μ.complexIso P' Q').hom.f n).val.app V
      ((s.extension.map (((coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom f g)).f n)).val.app V (scalarHomUnitSection M φ _ V _)) =
    (((coefficientTotalTensor.{r, c, v} J S).map (Prod.mkHom
      ((scalarComplex s.extension s.extension_additive).map f)
      ((scalarComplex s.extension s.extension_additive).map g))).f n).val.app V
      (((μ.complexIso P Q).hom.f n).val.app V (scalarHomUnitSection M φ _ V _))
  rw [hu, ScalarHomTensor.tensor_generator_map, μ.generators, μ.generators,
    ScalarHomTensor.tensor_generator_map]
  change _ = coefficientTensorGenerator.{r, c, v} J S
    ((scalarComplex s.extension s.extension_additive).obj P')
    ((scalarComplex s.extension s.extension_additive).obj Q') p q n h V
    ((s.extension.map (f.f p)).val.app V (scalarHomUnitSection M φ _ V x))
    ((s.extension.map (g.f q)).val.app V (scalarHomUnitSection M φ _ V y))
  rw [hu, hu]

end Site
end CategoryTheory

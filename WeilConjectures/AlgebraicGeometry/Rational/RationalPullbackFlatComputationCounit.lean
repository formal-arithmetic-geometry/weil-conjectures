/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalRealizationPullbackComparison
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.Site.SitePullbackAbelianUnderlyingSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Rational pullback computation on flat-term K-flat complexes

Source: Stacks Tags 0G7E and 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-rational-pullback-flat-computation-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  Functor.sheafPullbackConstruction.sheafPullback proEtaleRingInverseImageComp
  LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

private noncomputable def rationalScalarTensorExtension {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcModules T R ⥤ pbcModules T R :=
  (show pbcModules T R ⥤ _root_.PresheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj from
    { obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙 R)
      map a :=
        { app := fun V ↦ (ModuleCat.extendScalars ((𝟙 R : R ⟶ R).hom.app V).hom).map (a.val.app V)
          naturality := SheafOfModules.changeOfRingsHom_naturality (𝟙 R) _ a }
      map_id M := by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        simp
        rfl
      map_comp a b := by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        simp }) ⋙ PresheafOfModules.sheafification
          (𝟙 ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)

/-- The rational pullback computation counit is invertible on flat-term K-flat complexes.
Source: Stacks Tags 0G7E and 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-rational-pullback-flat-computation-counit).

Proof: present pro-etale module inverse image by its algebraic inverse-image data.
The underlying inverse-image functor preserves finite limits. The ringed-topos
K-flat pullback theorem therefore says that inverse image followed by identity
scalar extension preserves a K-flat complex whose terms are flat on the site.
On this pulled-back K-flat complex the scalar-extension computation counit is
invertible. The other factors in the rational pullback computation counit are
images or components of natural isomorphisms, so their composite is invertible. -/
theorem rationalPullComplexCounit_isIso_of_flatTerms {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := rationalCoefficientSheaf l T E) (P.X n)) :
    IsIso (rationalPullComplexCounit l E g c P) := by
  let R := rationalCoefficientSheaf l T E
  let RI := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists g R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage g (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g (𝟙 T)).2.2.2.1
  let U := I.modules ⋙ rationalScalarTensorExtension RI
  have hUeq : U = proEtaleRingModulePullback g R RI (Iso.refl _) := by
    dsimp only [U]
    rw [hI]
    rfl
  have : U.Additive := by rw [hUeq]; infer_instance
  have hobj (M) : U.obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (𝟙 RI) (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (f : M ⟶ N), U.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (𝟙 RI)
        (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm := by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hU := (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage g (Type (u + 1)))
    (proEtaleSheafDirectImage g (Type (u + 1)))
    (proEtaleSheafAdjunction g (Type (u + 1))) I (𝟙 RI) U hobj hmap P hp hf).1
  simp only [U, hI] at hU
  have := pbcExtensionCounit_isIso c
    (((proEtaleRingModulePullback g R RI (Iso.refl _)).mapHomologicalComplex
      (.up ℤ)).obj P) hU
  unfold rationalPullComplexCounit pbcComplexCounit
  infer_instance

end AlgebraicGeometry.Scheme

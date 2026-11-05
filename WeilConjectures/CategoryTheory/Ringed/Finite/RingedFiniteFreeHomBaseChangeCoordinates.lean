/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.IndFiniteFree.IndFiniteFreeScalarModel
import all WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
/-! # Finite-free coordinates for the scalar-Hom comparison

Source: Stacks Project, Tags 08J9 and 08JA.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory

namespace FiniteFreeLocalizationProof

end FiniteFreeLocalizationProof

namespace FiniteFreeClosedProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open WeilConjectures
variable {A B : Type*} [Category A] [Category B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (AR : CoefficientClosedStructure H) (AS : CoefficientClosedStructure I)
  {T : A ⥤ B} {U : B ⥤ A} (δ : T ⊣ U)
  (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
  [Preadditive B] (K : Type*) [Ring K] [Linear K B]

end FiniteFreeClosedProof

namespace RingedFiniteFreeCoordinatesProof
open SheafOfModules MonoidalCategory
universe u₀ v₀ r₀
variable {C : Type u₀} [Category.{v₀} C] [EssentiallySmall.{r₀} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [HasSheafify J AddCommGrpCat.{r₀}]
  {R S : Sheaf J CommRingCat.{r₀}}

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  Abelian.hasFiniteBiproducts
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w₁
variable [HasDerivedCategory.{w₁} (scalarModules J R)]
  [HasDerivedCategory.{w₁} (scalarModules J S)]

attribute [local irreducible] scalarModel

attribute [local irreducible] ordinaryBasisIso regularTensorIso moduleBasisIso

attribute [local irreducible] modelIso

attribute [local irreducible] chainBasis moduleBasis

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] scalarDerivedRestriction scalarRestrictionComparison
  FiniteFreeLocalizationProof.adjunction

attribute [local irreducible] derivedAdjunction

attribute [local irreducible] chainBasisE localizedBasis

end RingedFiniteFreeCoordinatesProof

attribute [local irreducible] derivedSectionLinear

section Site
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

namespace FiniteFreeScalarProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules MonoidalCategory WeilConjectures
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  derivedInternalHomOfUniverses SheafOfModules.homLinear SheafOfModules.homModule

attribute [local irreducible] coefficientTotalTensor DerivedCategory.instLinear
  CoefficientClosedStructure.tensor

end FiniteFreeScalarProof

namespace FiniteFreeScalarProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules

end FiniteFreeScalarProof

attribute [-instance] sectionLinearIndependent derivedSectionLinear sectionQLinear

attribute [local irreducible] FiniteFreeLocalizationProof.adjunction
  derivedInternalHomOfUniverses WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.scalarDerivedRestriction SheafOfModules.scalarRestrictionComparison
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  WeilConjectures.CoefficientTensorModels.iso
  RingedFiniteFreeCoordinatesProof.derivedAdjunction
  RingedFiniteFreeCoordinatesProof.scalarModel RingedFiniteFreeCoordinatesProof.modelIso
  RingedFiniteFreeCoordinatesProof.chainBasisE
  RingedFiniteFreeCoordinatesProof.moduleBasisIso
  RingedFiniteFreeCoordinatesProof.localizedBasis
  RingedFiniteFreeCoordinatesProof.restrictionFactors
  ringedFiniteFreeScalarSection WeilConjectures.coefficientTensorGenerator
  RingedFiniteFreeBasisCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end Site
end CategoryTheory

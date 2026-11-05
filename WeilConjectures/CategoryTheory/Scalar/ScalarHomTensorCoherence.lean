/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Coherence of normalized scalar tensor comparisons

Source: Stacks 07A4 and 0D6D. The pure-generator equations determine the chain
comparisons before their coherence descends to unbounded derived categories.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures SheafOfModules CategoryTheory.Functor
namespace CategoryTheory.ScalarHomTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R : Sheaf J CommRingCat.{max c v r}}
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] derivedInternalHomOfUniverses CoefficientClosedStructure.tensor
attribute [local irreducible] monoidalCategory
  Functor.mapHomologicalComplexUpToQuasiIso
  Functor.mapHomologicalComplexUpToQuasiIsoFactors

-- The categorical pasting calculation underlying the composition equation.

attribute [local instance] ScalarDerivedPair.extension_additive

variable [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (M : ScalarHomModels.{c, v, r, w} J) {S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

@[simp] private theorem chainAdj_unit_f
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    ((chainAdj M a).unit.app P).f n = (M.scalar a).ordinaryAdjunction.unit.app (P.X n) := rfl

attribute [local irreducible] chainAdj

attribute [local irreducible] pairComparison scalarPairComplexComparison coefficientTotalTensor
  coefficientTensorGenerator

attribute [local irreducible] scalarHomOrdinaryRestrictionComp

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
@[simp] private theorem chainRestrictionComp_f {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (H : CochainComplex (scalarModules J T) ℤ) (n : ℤ) :
    (((chainRestrictionComp.{c, v, r} a b).hom.app H).f n) =
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b).hom.app (H.X n) := rfl

attribute [local irreducible] ordinaryComp

@[simp] private theorem complexComp_f {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    (((complexComp M a b).hom.app P).f n) = (ordinaryComp M a b).hom.app (P.X n) := by
  change (𝟙 _ ≫ _) = _
  exact Category.id_comp _

attribute [local irreducible] complexComp

attribute [local irreducible] scalarHomRestrictionComp

attribute [local irreducible] scalarHomExtensionComp

attribute [local semireducible] scalarHomOrdinaryRestrictionComp

attribute [local irreducible] scalarHomOrdinaryRestrictionId

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
@[simp] private theorem chainRestrictionId_f (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    (((chainRestrictionId.{c, v, r} R).hom.app P).f n) =
      (scalarHomOrdinaryRestrictionId.{c, v, r} R).hom.app (P.X n) := by
  exact mapComplex_unit_comparison_f (scalarRestriction (𝟙 R))
    (scalarHomOrdinaryRestrictionId.{c, v, r} R) P n

attribute [local irreducible] scalarHomRestrictionId

attribute [local irreducible] scalarHomExtensionId

attribute [local semireducible] scalarHomOrdinaryRestrictionId

attribute [local irreducible] complexId

attribute [local irreducible] CoefficientTensorModels.iso

end CategoryTheory.ScalarHomTensor

namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

end CategoryTheory

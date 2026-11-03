/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import WeilConjectures.ProperBaseChange.SliceAwayLocalizationFreeResolution
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.AlgebraicGeometry.Picard.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.ProperBaseChange.LocalCoefficientTelescopeDual
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # Normalizing completed coefficients on the small pro-etale site

Source: Stacks Tags 00YY, 093M and 099C; Bhatt--Scholze, Lemma 6.5.8.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace SfbCompletionNormalization

private local instance standardDerived {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

private theorem projection (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    (coefficients X I).hom ≫
        ConstantCompletion.projection (proEtaleModelTopology X) A I n =
      (sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op n)) ≫
        (constants X).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  dsimp only [coefficients, Iso.trans_hom, ConstantCompletion.projection]
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    preservesLimitIso_hom_π]
  rfl

end SfbCompletionNormalization

end AlgebraicGeometry.Scheme

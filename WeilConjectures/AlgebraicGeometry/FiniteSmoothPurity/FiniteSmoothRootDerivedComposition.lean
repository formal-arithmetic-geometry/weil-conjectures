/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import all WeilConjectures.ConstructibleSheaf.Defs
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import all WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import all WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import all WeilConjectures.CategoryTheory.IntTensorFamilyIso
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import all WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import all Mathlib.CategoryTheory.Abelian.Refinements
import all Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import all WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.Topology.Defs.Filter
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.SixFunctors.Etale.Derived.Tensor
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SixFunctors.Etale.Derived.Shift
import all WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.CoefficientLineComparison.FiniteSmoothRootDerivedNormalization

/-! # Composition of normalized ordinary derived root comparisons

Source: smooth-purity reduction compatibilities, part (3).
(blueprint: lem-pur-finite-smooth-root-derived-composition).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem quotient_comp (ell : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :
    FiniteReduction.quotient.{u} ell (hnm.trans hmr) =
      (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) := by
  exact RingHom.ext (fun x ↦
    congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} ell n))
      (DFunLike.congr_fun
        (Subsingleton.elim
          (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
          ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
            (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down))

private theorem root_comp
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m)
    (a : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (b : CoefficientLineComparison (FiniteReduction.quotient ell hnm)
      (ell ^ m) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (c : CoefficientLineComparison (FiniteReduction.quotient ell (hnm.trans hmr))
      (ell ^ r) (ell ^ n) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    a.roots ≫ b.roots = c.roots := by
  apply (cancel_mono (kernel.ι ((ell ^ n) • 𝟙 T.gmSheaf))).1
  rw [Category.assoc, b.roots_power, Preadditive.comp_nsmul, a.roots_power,
    c.roots_power, smul_smul]
  congr 1
  rw [Nat.pow_div hnm (Fact.out : ell.Prime).pos,
    Nat.pow_div hmr (Fact.out : ell.Prime).pos,
    Nat.pow_div (hnm.trans hmr) (Fact.out : ell.Prime).pos,
    ← pow_add]
  congr 1
  omega

end AlgebraicGeometry.Etale.FiniteSmoothPurity

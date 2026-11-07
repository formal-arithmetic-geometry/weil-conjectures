/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Submission.WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import Submission.WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import Submission.WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import Submission.WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Submission.WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import Submission.WeilConjectures.ConstructibleSheaf.Pullback
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Submission.WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Submission.WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Submission.WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Shift
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical arrows for the inverse-twist projective-line decomposition

The unit and Chern adjoint are explicit, independently of the proof of their splitting.
The comparison and untwisting lemmas use this common interface.
Source: main-20261015, thm-amb-p1-decomposition.md and its proof
(blueprint: def-asd-ordinary-finite-p1-decomposition-maps).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

set_option backward.isDefEq.respectTransparency false in
/-- The normalized inverse product is the actual evaluation.
Source: Stacks Tag 03PK (blueprint: def-asd-ordinary-finite-p1-decomposition-maps).
Proof: take the n=0 negative-evaluation normalization of the canonical finite-twist data. -/
theorem p1DecompositionSheafProduct_hom (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (p1DecompositionSheafProduct A N hN hA T hT).hom =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
        (Scheme.finiteEtaleTateSheaf A N T hA 0) := by
  have h := (p1DecompositionTwistTransport A N hN hA).product_normalization T hT
  simpa only [p1DecompositionSheafProduct, eqToHom_refl, Category.comp_id] using h

/-- The unit component A_S -> Rq_* A_P under the constant-object comparison.
Source: the component 1 in the blueprint (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionUnit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFiniteUnit A S ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine S ↘ S)).homEquiv _ _
      (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom

/-- Form a tensor-evaluation adjoint in arbitrary categories.
Source: the tensor-Hom adjunction (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionTensorAdjoint {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (tensor : D ⥤ D ⥤ D)
    (K : C) (U L V K' : D)
    (unit : F.obj K ≅ (tensor.obj (F.obj K)).obj U) (pull : F.obj K ≅ K')
    (eval : (tensor.obj K').obj L ⟶ V) (c : U ⟶ L) : K ⟶ G.obj V :=
  adj.homEquiv _ _ (unit.hom ≫ (tensor.obj (F.obj K)).map c ≫
    (tensor.map pull.hom).app L ≫ eval)

/-- The component h is the adjoint of the tensor-with-Chern-class/evaluation
composite, using the canonical negative-twist pullback and tensor unit.
Source: the explicit definition of h in the node (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionChernAdjoint (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    p1DecompositionTwist A N hA S (-1) (-2) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  p1DecompositionTensorAdjoint (ordinaryFinitePullback A (ProjectiveLine S ↘ S))
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S))
    (ordinaryFiniteTensor A (ProjectiveLine S)) (p1DecompositionTwist A N hA S (-1) (-2))
    (ordinaryFiniteUnit A (ProjectiveLine S))
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (ordinaryFiniteUnit A (ProjectiveLine S))
    (p1DecompositionTwist A N hA (ProjectiveLine S) (-1) (-2))
    (derivedTensorSingleUnitIso _).symm
    (p1DecompositionTwistPullback A N hN hA (ProjectiveLine S ↘ S) hS (-1) (-2))
    (p1DecompositionEvaluation A N hN hA (ProjectiveLine S)
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom)) c

/-- The specified ordered map (1,h), with no independent choice of decomposition.
Source: the displayed isomorphism in the node (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    (ordinaryFiniteUnit A S ⊞ p1DecompositionTwist A N hA S (-1) (-2)) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) :=
  biprod.desc (p1DecompositionUnit A S) (p1DecompositionChernAdjoint A N hN hA S hS c)

/-- Assemble two component comparisons on a pulled-back biproduct.
Source: the universal property of the biproduct (blueprint: thm-amb-p1-decomposition). -/
@[irreducible]
def p1DecompositionBiprodMap {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) (X Y : C) (X' Y' : D) (e : F.obj X ≅ X') (e' : F.obj Y ≅ Y') :
    F.obj (X ⊞ Y) ⟶ X' ⊞ Y' :=
  biprod.lift (F.map biprod.fst ≫ e.hom) (F.map biprod.snd ≫ e'.hom)

/-- The canonical pullback map on A_S plus A_S(-1)[-2], assembled from the
images of the two projections and the constant and signed-twist comparisons.
Source: the arbitrary-base compatibility clause (blueprint: thm-amb-p1-decomposition). -/
def p1DecompositionSourceMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePullback A g).obj
        (ordinaryFiniteUnit A S ⊞ p1DecompositionTwist A N hA S (-1) (-2)) ⟶
      (ordinaryFiniteUnit A S' ⊞ p1DecompositionTwist A N hA S' (-1) (-2)) :=
  p1DecompositionBiprodMap (ordinaryFinitePullback A g)
    (ordinaryFiniteUnit A S) (p1DecompositionTwist A N hA S (-1) (-2))
    (ordinaryFiniteUnit A S') (p1DecompositionTwist A N hA S' (-1) (-2))
    (ordinaryFiniteUnitPullback A g) (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2))

end AlgebraicGeometry.Etale

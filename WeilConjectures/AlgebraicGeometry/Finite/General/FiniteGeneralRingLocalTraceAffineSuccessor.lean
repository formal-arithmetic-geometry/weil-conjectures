/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.AffineSuccessorPasting
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingLocalTraceAffineSuccessorFactor

/-! # Successor step for the ordered affine Kummer counit

Source: general-ring smooth purity, proof (3), exponent independence, the
ordered affine tower induction.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-affine-successor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Assemble the successor affine counit square from the one-coordinate square.

Source: general-ring smooth purity, proof (3), exponent independence, the
successor step in the ordered affine tower.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-affine-successor).

Proof: expand the counit of the composite affine adjunction using
`affineTraceAdjunctionTower_counit_succ`.  The recursive definition of
`finiteGeneralRingLevelPower` tensors the induction transition with the line
comparison.  Apply the one-coordinate equation to the last line, use its
naturality at the preceding transition, and then use the induction hypothesis.
The generic-A descent and tensor comparison identities paste these three
squares without permuting factors.
-/
theorem finiteGeneralRingLocalTraceExponent_affine_successor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (hMunit : IsUnit (M : Γ(T, ⊤))) (hNunit : IsUnit (N : Γ(T, ⊤)))
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN T q b)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (DN : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hN tN T hT)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (DM : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM tM T hT)
    (d : ℕ)
    (eD : (Etale.affineTraceRight A M hM T d).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T d).obj
        (Etale.ordinaryFiniteUnit A T))
    (heD : eD =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit d).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T d)).map
          (finiteGeneralRingLevelPower A M N hM hN T b d).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit d).inv)
    (eSucc : (Etale.affineTraceRight A M hM T (d + 1)).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T (d + 1)).obj
        (Etale.ordinaryFiniteUnit A T))
    (heSucc : eSucc =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit (d + 1)).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T (d + 1))).map
          (finiteGeneralRingLevelPower A M N hM hN T b (d + 1)).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit (d + 1)).inv)
    (eLine : (Etale.affineTraceRight A M hM T 1).obj
        (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hN T 1).obj
        (Etale.ordinaryFiniteUnit A T))
    (heLine : eLine =
      (Etale.affineLinearCoefficientDescent A M hM tM T hMunit 1).hom ≫
        (Etale.ordinaryFinitePullback A (affineTraceProjection T 1)).map
          (finiteGeneralRingLevelPower A M N hM hN T b 1).hom ≫
        (Etale.affineLinearCoefficientDescent A N hN tN T hNunit 1).inv)
    (ih :
      (Etale.affineTraceLeft A T d).map
          eD ≫
        Etale.affineTraceCounit A N hN tN DN T hNunit d =
        Etale.affineTraceCounit A M hM tM DM T hMunit d)
    (hline : (Etale.affineTraceLineLeft A T).map eLine ≫
        Etale.affineTraceCounit A N hN tN DN T hNunit 1 =
      Etale.affineTraceCounit A M hM tM DM T hMunit 1) :
    (Etale.affineTraceLeft A T (d + 1)).map
          eSucc ≫
        Etale.affineTraceCounit A N hN tN DN T hNunit (d + 1) =
      Etale.affineTraceCounit A M hM tM DM T hMunit (d + 1)  := by
  let := affineTraceNoetherian T d
  have hf := finiteGeneralRingLocalTraceExponent_affine_successor_factor
    A M N hMpos hNpos hM hN T hMunit hNunit q b hb tN DN tM DM d eD heD eSucc
    heSucc eLine heLine hline
  let L := fun r ↦ Etale.affineTraceLineLeft A (affineTraceTower T r)
  let R := fun r ↦ Etale.affineTraceLineRight A M hM (affineTraceTower T r)
  let R' := fun r ↦ Etale.affineTraceLineRight A N hN (affineTraceTower T r)
  let a := fun r ↦ Etale.affineTraceLineAdjunction A M hM tM
    (affineTraceTower T r) (affineTraceInvertible M T hMunit r)
    (@DM (affineTraceTower T r) (affineTraceNoetherian T r)
      (affineTraceInvertible M T hMunit r))
  let a' := fun r ↦ Etale.affineTraceLineAdjunction A N hN tN
    (affineTraceTower T r) (affineTraceInvertible N T hNunit r)
    (@DN (affineTraceTower T r) (affineTraceNoetherian T r)
      (affineTraceInvertible N T hNunit r))
  have hp := Etale.affine_successor_pasting (C := fun r ↦
      Etale.DerivedCategoryModule A (affineTraceTower T r))
    (L := L) (R := R) (R' := R') a a' d (Etale.ordinaryFiniteUnit A T)
    eD eSucc hf (by
      simpa [L, a, a', Etale.affineTraceCounit, Etale.affineTraceAdjunction,
        Etale.affineTraceLeft] using ih)
  simpa only [L, R, R', a, a', Etale.affineTraceCounit,
    Etale.affineTraceAdjunction, Etale.affineTraceLeft] using hp

end AlgebraicGeometry.ProEtale

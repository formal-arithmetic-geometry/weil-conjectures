/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
public import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalComparisonData
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SmoothPurity.FiniteP1ChernMapBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.SmoothPurity.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
public import Mathlib.Logic.Small.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import Mathlib.Tactic.SuppressCompilation
public import WeilConjectures.ConstructibleSheaf.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Ring.Int.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineProjectionReassociation
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineTowerTensorCounit
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Tensor normalization of the ordered ordinary affine-space counit

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-affine-space-top-trace.proof.md,
last paragraph, expanded coefficient normalization; Stacks Project, Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization).

The geometric model is the existing ordered coordinate tower, canonically isomorphic
to affine d-space. Reassociation is constructed from the normalized line comparisons;
no isomorphism is selected from the existential right-normal-form theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open OrdinaryAffineCounitTensorNormalization

/-- Tensor normalization of the actual ordered affine counit for every unbounded complex.
The isomorphism is constrained to have exactly the canonical projection as its hom;
its inverse is therefore the inverse specified in the node, not an arbitrary arrow.
Source: affine-space top trace proof, last paragraph; Stacks, Tags 0B56 and 0GL1
(blueprint: lem-pur-ordinary-affine-counit-tensor-normalization).

Proof:
1. The finite-coefficient proper projection and the derived open tensor comparison
are invertible on arbitrary unbounded inputs. Their specified compactification
composite gives the required projection isomorphism with its hom fixed.
2. Cancel that forward projection. The structural projection/reassociation equality
rewrites its composite with the inverse source and left-functor comparisons as the
ordered tensor action, right strength, and mapped right unitor.
3. The normalized projective-line counit has a coefficient-action square by the
associativity of the actual proper projection. Transporting the exact open adjunction
along its canonical right comparison gives its open counit square. Paste the two
squares and induct over the ordered coordinate tower to obtain the actual tower
counit's coefficient square.
4. Naturality of this counit at the right unitor, followed by the tower square,
moves the coefficient outside the counit. Functoriality identifies the remaining
composite with the unchanged definition of the unit trace.
5. This uses exactly the given ordered adjunction and comparisons, including their
identity stage. No truncation, generator choice, scalar division or determination
of arbitrary natural transformations from their unit values is used.
-/
theorem ordinaryAffineCounit_tensor_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A S) :
    ∃ P : (((derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
          (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d))) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        (((derivedTensor (ModuleCat.{u + 1} A) (affineTraceTower S d)).obj
          ((upperStar (ModuleCat.{u + 1} A)
            (affineTraceProjection S d)).mapDerivedCategory.obj K)).obj
          (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d)),
      P.hom = compactSupportProjectionMap A (affineTraceProjection S d)
        (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K ∧
      counit A N hN hA t D S hS d K = P.inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
          (trace A N hN hA t D S hS d) ≫ (derivedTensorSingleUnitIso K).hom := by
  have hp := isIso_projectionMap_of_finite A (affineTraceProjection S d)
  have hi : IsIso (compactSupportProjectionMap A (affineTraceProjection S d)
      (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K) := by
    unfold compactSupportProjectionMap compactSupportProjectionMapOfCompactification
    change IsIso (_ ≫ ((projectionMap (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).app _).app K ≫ _ ≫ _)
    infer_instance
  refine ⟨asIso (compactSupportProjectionMap A (affineTraceProjection S d)
    (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K),
    rfl, ?_⟩
  apply (cancel_epi (compactSupportProjectionMap A (affineTraceProjection S d)
    (SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower S d) d) K)).mp
  simp only [asIso_inv, IsIso.hom_inv_id_assoc]
  unfold counit trace
  have hr := ordinaryAffine_projection_reassociation N hN A hA t S hS d K
  rw [reassoc_of% hr]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (affineTraceAdjunction A N hA t D S hS d).counit.naturality
    (derivedTensorSingleUnitIso K).hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have ht := ordinaryAffineTower_tensorCounit A N hA t D S hS d K
    (ordinaryFiniteUnit A S)
  erw [reassoc_of% ht]
  simp only [affineTraceCounit]
  rfl

end AlgebraicGeometry.Etale

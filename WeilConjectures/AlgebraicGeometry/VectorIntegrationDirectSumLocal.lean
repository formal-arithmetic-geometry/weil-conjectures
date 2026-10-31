/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumTotalCounit
import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumIteratedCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Ordered vector integration on a simultaneous frame open

Source: blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, simultaneous trivializations.
(blueprint: lem-pur-vector-integration-direct-sum-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

attribute [local irreducible] AlgebraicGeometry.Etale.rightDerivedLowerShriek
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  AlgebraicGeometry.VectorBundleZeroSection.π AlgebraicGeometry.VectorBundleZeroSection.scheme
  AlgebraicGeometry.Etale.leftDerivedUpperStarComp
  AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory vectorIntegrationCoefficient vectorIntegrationSource

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  vectorBundleIntegration vectorIntegrationGluing
  unboundedEtaleLowerShriekId affineLinearPullbackId
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensorSymmetry projectionMapOfCompactification

set_option linter.unusedVariables false in
-- The original statement names equality witnesses for callers; its conclusion ignores them.
set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- The coefficient transports involve deeply nested derived-functor expressions.
/-- The ordered multiplication calculation after restriction to one common frame open.
Only the restriction to W is asserted; no cover or global descent is assumed.
The map parameters are constrained to the existing product-presentation constructions,
written out to avoid importing the global geometric-descent theorem in its own proof.
Source: blueprint vector-bundle purity proof, paragraph 2, simultaneous trivializations;
geometric-descent Steps 4--6.
(blueprint: lem-pur-vector-integration-direct-sum-local).

Proof: restrict the supplied frames on V and U along the inclusions of W. The
symmetric-algebra generator formulas identify q with the rank-r affine projection
over the rank-s affine space, with the s base coordinates before the r fibre
coordinates. The defining normalization of each glued integration replaces it on
these frames by the corresponding ordered affine counit. The trace for the pulled
back fibre bundle has this same normalization on the pulled-back frame. Expand the
composite-adjunction counit in coordinate order. Associativity of the normalized
compact-support compositor gives the rank-(r+s) counit, with exactly the product
exchange and coefficient transport c displayed below. Apply ordinary affine counit
tensor normalization over the rank-s affine space at its coefficient W_p. Its inverse
projection, tensor of the fibre trace, and right unitor give exactly the right side.
Tate pullback composition and the ordered additivity comparison identify its source
with d; linear frame invariance removes any change of the sum frame. Compatibility
of compact-support projection with open exchange transports the same formula back
to W. Cancel the common invertible constant-sheaf comparison. This proves equality
only after restriction to W; degree-zero descent is a separate global argument.
For a zero rank the corresponding coordinate tower is the identity adjunction.
For empty W or the zero coefficient ring all displayed arrows are unique.
-/
theorem vectorIntegration_directSum_local (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    [hP : IsIso (compactSupportProjectionMap A
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F))
      (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F))
      (vectorIntegrationCoefficient A N hA S s G))]
    (V U : S.Opens) (eF : VectorBundleZeroSection.Trivialization S r F V)
    (eG : VectorBundleZeroSection.Trivialization S s G U)
    (W : S.Opens) (hWV : W ≤ V) (hWU : W ≤ U) :
    let fibre :=
      (Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F;
    let q :=
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
      (fibre);
    let h :=
      q ≫ VectorBundleZeroSection.π S s G;
    let Wh :=
      (ordinaryFinitePullback A (h)).obj
      (affineLinearBaseCoefficient A N hA S (r + s));
    ∀ (c : (ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅ Wh)
      (hc : c =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (VectorTraceGeometry.sumIso S r s F G).hom
      (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
      (h)
      (by simpa only [Category.comp_id] using
        (VectorTraceGeometry.sumIso_isPullback S r s F G).w.symm)).symm.app _),
    ∀ (ex : (ordinaryFinitePullback A (𝟙 S)).obj
        (vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj
        ((ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))))
      (hex : ex = (by
      have hex := (unboundedEtaleCompactSupport_baseChange A
        (VectorTraceGeometry.sumIso_isPullback S r s F G)).1
      have hexa := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hex
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))
      exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)).app _ ≪≫
        @asIso _ _ _ _ ((unboundedEtaleCompactSupportBaseChange A
          (VectorTraceGeometry.sumIso_isPullback S r s F G)).app
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)))
          hexa ≪≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (VectorTraceGeometry.sumIso S r s F G).hom).symm.app _))),
    let kh :=
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (h)).map
        (c).inv ≫
      (ex).inv ≫
      (affineLinearPullbackId A S).hom.app _ ≫
      vectorBundleIntegration N hN A hA S hS (r + s) (VectorTraceGeometry.sum S F G);
    ∀ (d : Wh ≅
      ((ordinaryFiniteTensor A _).obj
        ((upperStar (ModuleCat.{u + 1} A) q).mapDerivedCategory.obj
          (vectorIntegrationCoefficient A N hA S s G))).obj
        (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r fibre))
      (hd : d =
      (ordinaryFinitePullback A (h)).mapIso
        (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm r s)) ≪≫
          WeilConjectures.PurityFiniteSetting.purityPowerAdd A N hA S s r) ≪≫
      ordinaryFiniteTensorPullback A (h)
        (affineLinearBaseCoefficient A N hA S s) (affineLinearBaseCoefficient A N hA S r) ≪≫
      ordinaryFiniteTensorRightMapIso A _
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (q)
          (VectorBundleZeroSection.π S s G)).app _ ≪≫
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
            (q)).app (vectorIntegrationCoefficient A N hA S s G))
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (q)
          (VectorBundleZeroSection.π S s G)).app _ ≪≫
          (ordinaryFinitePullback A (q)).mapIso
            (vectorIntegrationBaseCoefficientPullback A N hA t
              (VectorBundleZeroSection.π S s G) hS r))),
    (ordinaryFinitePullback A W.ι).map
      ((unboundedEtaleLowerShriekCompIso A (q)
        (VectorBundleZeroSection.π S s G)).hom.app
        (Wh) ≫
      kh) =
    (ordinaryFinitePullback A W.ι).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S s G)).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (q)).map
          (d).hom ≫
        @inv _ _ _ _ (compactSupportProjectionMap A (q)
          (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r
            (fibre)) (vectorIntegrationCoefficient A N hA S s G)) hP ≫
        ((ordinaryFiniteTensor A _).obj (vectorIntegrationCoefficient A N hA S s G)).map
          (vectorBundleIntegration N hN A hA (VectorBundleZeroSection.scheme S s G)
            (affineTracePullbackInvertible N (VectorBundleZeroSection.π S s G) hS) r
            (fibre)) ≫
        (derivedTensorSingleUnitIso (vectorIntegrationCoefficient A N hA S s G)).hom) ≫
      vectorBundleIntegration N hN A hA S hS s G) := by
  classical
  obtain ⟨t', D, _⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  have ht : t' = t := ordinaryFiniteTwistTransport_unique A N hA t' t
  subst t'
  let : TopologicalSpace.NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian W.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  dsimp only
  intro c hc ex hex d hd
  have hnSum : VectorIntegrationNormalization N hN A hA S hS (r + s)
      (VectorTraceGeometry.sum S F G)
      (vectorBundleIntegration N hN A hA S hS (r + s) (VectorTraceGeometry.sum S F G)) := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact
      (existsUnique_vectorIntegrationGluing N hN A hA S hS (r + s)
        (VectorTraceGeometry.sum S F G)).2.exists.choose_spec.2
  have hnG : VectorIntegrationNormalization N hN A hA S hS s G
      (vectorBundleIntegration N hN A hA S hS s G) := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact
      (existsUnique_vectorIntegrationGluing N hN A hA S hS s G).2.exists.choose_spec.2
  have hSum := hnSum t D W
    (VectorIntegrationDirectSumCounit.sumFrame S r s F G V U eF eG W hWV hWU)
  have hG := hnG t D W (VectorIntegrationDirectSumCounit.restrictedFrame hWU eG)
  have h := (vectorIntegration_directSum_total_counit N hN A hA t D S hS r s F G
    V U eF eG W hWV hWU c hc ex hex).trans
    (vectorIntegration_directSum_iterated_counit N hN A hA t D S hS r s F G
      V U eF eG W hWV hWU d hd).symm
  rw [← hSum, ← hG] at h
  apply (cancel_mono (ordinaryFiniteUnitPullback A W.ι).hom).mp
  simpa only [← Functor.map_comp, ← Category.assoc] using h


end AlgebraicGeometry.Etale

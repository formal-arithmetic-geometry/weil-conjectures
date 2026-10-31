/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedCompactificationScalarSquare
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Logic.Small.Defs
public import Mathlib.Tactic.SuppressCompilation
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSupportedDiagonalUnitSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineCompactCompatibility
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.InternalHom
public import WeilConjectures.ConstructibleSheaf.LisseRankOne
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
public import WeilConjectures.SmoothPurity.FiniteP1ChernMapBaseChange
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.SmoothPurity.SupportedDerivedUnitForget
public import WeilConjectures.Topology.RingedSpaceModuleCohomology

/-! # Restricting the ordered ambient compactification comparison to D+

Source: blueprint Charts, ordered compactification comparison; the bounded/unbounded
proper/open comparison equations (blueprint: lem-sp-affine-compactification-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private lemma tower_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L Q V : C ⥤ D} {F P : D ⥤ E} {R H : C ⥤ E}
    (a : L ≅ Q) (b : V ≅ Q) (e : F ≅ P)
    (t : V ⋙ P ≅ R) (r : R ≅ H) (k : Q ⋙ P ≅ H) (K : C)
    (hk : k.hom.app K = P.map (b.inv.app K) ≫ t.hom.app K ≫ r.hom.app K) :
    F.map (a.hom.app K ≫ b.inv.app K) ≫ e.hom.app (V.obj K) ≫
        t.hom.app K ≫ r.hom.app K =
      F.map (a.hom.app K) ≫ e.hom.app (Q.obj K) ≫ k.hom.app K := by
  rw [hk, F.map_comp]
  simp only [Category.assoc]
  rw [e.hom.naturality_assoc]

-- Comparing first to the chosen candidate removes the auxiliary compactification
-- from the induction while retaining the actual proper/open tower maps.

private theorem affine_left_chosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (K : DerivedCategoryModule A (affineTraceTower S d)) :
    (ProEtale.reductionEtaleAffineLeftIso A S d c).hom.app K ≫
        (rightDerivedLowerShriekIso A c).hom.app K =
      (affineTraceUnboundedCompactComparison A S d).hom.app K := by
  induction d with
  | zero =>
    have h := (unboundedEtaleCompactSupport_comparison_coherence A (𝟙 S)).2
      (Compactification.ofIsProper (𝟙 S)) c
      (HasCompactification.compactification (𝟙 S))
    let i := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S
    change (i.inv.app K ≫
      (rightDerivedLowerShriekOfCompactificationIso A
        (Compactification.ofIsProper (𝟙 S)) c).hom.app K) ≫
        (rightDerivedLowerShriekIso A c).hom.app K = _
    rw [affineTraceUnboundedCompactComparison,
      VectorTraceScalar.identity_comparison A S]
    simpa only [i, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, rightDerivedLowerShriekIso, Compactification.ofIsProper,
      affineTraceProjection, Category.assoc] using
      congrArg (fun z ↦ i.inv.app K ≫ z.hom.app K) h
  | succ d ih =>
    have := affineTraceNoetherian S d
    have := affineTraceNoetherian S (d + 1)
    have : IsNoetherian (AffineSpace PUnit.{u + 1} (affineTraceTower S d)) :=
      affineTraceNoetherian S (d + 1)
    let q := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d
    let cp := HasCompactification.compactification (affineTraceProjection S d)
    let ce := c.ofComp cp
    have hcp : rightDerivedLowerShriekIso A cp = Iso.refl _ :=
      (unboundedEtaleCompactSupport_comparison_coherence A
        (affineTraceProjection S d)).1 cp
    have hp := ih cp
    simp only [hcp, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at hp
    have ht := congr_app (unboundedEtaleLowerShriekCompIso_tower A q
      (affineTraceProjection S d) cp ce) K
    simp only [hcp, Iso.refl_inv, NatTrans.hcomp, NatTrans.comp_app,
      NatTrans.id_app, rightDerivedLowerShriek_eq, Category.assoc] at ht
    have ht' := ht.trans (Category.id_comp _)
    have hc := congrArg (fun z ↦ z.hom.app K)
      ((unboundedEtaleCompactSupport_comparison_coherence A
        (affineTraceProjection S (d + 1))).2 (cp.comp ce) c
          (HasCompactification.compactification (affineTraceProjection S (d + 1))))
    have hl := congrArg (fun z ↦ z.hom.app K)
      ((unboundedEtaleCompactSupport_comparison_coherence A q).2
        (affineTraceLineCompactification (affineTraceTower S d)) ce.restrict
        (HasCompactification.compactification q))
    simp only [Iso.trans_hom, NatTrans.comp_app] at hc hl
    have hline :
        (rightDerivedLowerShriekOfCompactificationIso A
          (affineTraceLineCompactification (affineTraceTower S d)) ce.restrict).hom.app K =
        (rightDerivedLowerShriekIso A
          (affineTraceLineCompactification (affineTraceTower S d))).hom.app K ≫
          (rightDerivedLowerShriekIso A ce.restrict).inv.app K := by
      apply (cancel_mono ((rightDerivedLowerShriekIso A ce.restrict).hom.app K)).1
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
        rightDerivedLowerShriekIso]
      exact hl
    change ((affineTraceLeft A S d).map _ ≫
      (ProEtale.reductionEtaleAffineLeftIso A S d cp).hom.app _ ≫
      (rightDerivedLowerShriekOfCompactificationCompIso A cp ce).hom.app K ≫
      (rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c).hom.app K) ≫
      (rightDerivedLowerShriekIso A c).hom.app K = _
    simp only [Category.assoc]
    rw [hp]
    simp only [rightDerivedLowerShriekIso]
    erw [hc, hline]
    exact tower_paste _ _ _ _ _ _ K ht'

/-- The ambient recursive comparison restricts to the same bounded-below comparison.
Source: blueprint Charts, ordered compactification scalar square, steps 3 and 7
(blueprint: lem-sp-affine-compactification-normalization).

Proof: Induct on the coordinate number. At zero both comparisons are inverse identity
normalization followed by the pairwise comparison from the identity candidate to c.
The exact identity open functor and proper identity functor give the same normalization
under the bounded-below inclusion. At a successor expand both recursive tower maps.
The bounded/unbounded pairwise comparison equation identifies the standard line
comparison; inclusion naturality moves the preceding tower comparison through it.
Apply the induction hypothesis to the chosen preceding compactification. The
bounded/unbounded composition equation identifies the binary compositor, after the
pairwise conjugations describing the chosen compatible triangle. Finally pairwise
comparison transitivity identifies the composite compactification with c. The
coherent triangle equations make this independent of the auxiliary triangle.
Every intermediate input is bounded below since compact support preserves D+;
this assertion involves no scalar extension or coefficient Tor assumption. -/
theorem affineCompactificationComparison_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    (S : Scheme.{u}) [IsNoetherian S] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (d : ℕ) (c : Compactification (affineTraceProjection S d))
    (M : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ProEtale.reductionEtaleAffineLeftIso A S d c).hom.app M.obj =
      (orderedCompactificationComparison A k S d c M).hom := by
  rw [comparison_eq A k S d c M]
  apply (cancel_mono ((rightDerivedLowerShriekIso A c).hom.app M.obj)).1
  rw [Category.assoc]
  have := affineTraceNoetherian S d
  have h := congrArg (fun z ↦ z.hom.app M.obj)
    ((unboundedEtaleCompactSupport_comparison_coherence A
      (affineTraceProjection S d)).2
      (HasCompactification.compactification (affineTraceProjection S d)) c
      (HasCompactification.compactification (affineTraceProjection S d)))
  rw [(unboundedEtaleCompactSupport_comparison_coherence A
    (affineTraceProjection S d)).1] at h
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app] at h
  rw [show (rightDerivedLowerShriekOfCompactificationIso A
      (HasCompactification.compactification (affineTraceProjection S d)) c).hom.app M.obj ≫
      (rightDerivedLowerShriekIso A c).hom.app M.obj = 𝟙 _ from h]
  simpa only [rightDerivedLowerShriek_eq, Category.comp_id] using
    affine_left_chosen A S d c M.obj

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationChartCoordinates
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationUnitTranspose

import WeilConjectures.AlgebraicGeometry.VectorBundleIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.AlgebraicGeometry.VectorIntegrationFrameAdjoint
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
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
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom

/-! # Restriction of the vector integration adjunct to a linear chart

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-amb-vector-bundle-purity.proof.md, second paragraph, before the ordered-purity
identification (blueprint: lem-pur-vector-chart-restricted-affine-transpose).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart

open AffineLinePurity AffineSpacePurity VectorIntegrationSite
open CategoryTheory.Limits

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 20001]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.rightDerivedLowerShriek Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction Etale.affineLinearCompactComparison
  Etale.affineTraceCounit affineTraceProjection Etale.singleFunctorObjUnitIso

attribute [local implicit_reducible] Scheme.Modules Etale.vectorIntegrationCoefficient

set_option maxHeartbeats 800000 in
-- Kernel checking the ordinary derived-category unit identifications needs this budget.
private theorem raw_chart_equation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t Y hY)
    (Z : Scheme.{u}) [IsNoetherian Z] (hZ : IsUnit (N : Γ(Z, ⊤)))
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) [IsNoetherian U.toScheme]
    (e : VectorBundleZeroSection.Trivialization Z d F U) :
    letI := (Etale.vectorIntegration_geometry Z d F).1
    letI := (Etale.vectorIntegration_geometry Z d F).2.1
    let hU := affineTracePullbackInvertible N U.ι hZ
    let a := Etale.vectorIntegrationChart Z d F U e
    let f := VectorBundleZeroSection.π Z d F
    let p := affineTraceProjection U.toScheme d
    let sq := Etale.vectorIntegrationChart_isPullback Z d F U e
    (Etale.vectorIntegrationBaseCoefficientPullback A N hA t (a ≫ f) hZ d).inv ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a f).hom.app _ ≫
      (Etale.ordinaryFinitePullback A a).map
        ((Etale.vectorBundlePurityAdjunction A Z d F).homEquiv _ _
          (Etale.vectorBundleIntegration N hN A hA Z hZ d F)) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app (Etale.ordinaryFiniteUnit A Z) ≫
      (Etale.rightDerivedUpperShriek A p).map (Etale.ordinaryFiniteUnitPullback A U.ι).hom =
    (Etale.rightDerivedUpperShriekAdjunction A p).homEquiv _ _
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
          ((Etale.affineLinearCoefficientDescent A N hA t U.toScheme hU d ≪≫
            Etale.vectorIntegrationBaseCoefficientPullback A N hA t p hU d).inv) ≫
        (Etale.affineLinearCompactComparison N hN A hA U.toScheme hU d).inv ≫
        Etale.affineTraceCounit A N hA t D U.toScheme hU d) := by
  let := (Etale.vectorIntegration_geometry Z d F).1
  let := (Etale.vectorIntegration_geometry Z d F).2.1
  let hU := affineTracePullbackInvertible N U.ι hZ
  let a := Etale.vectorIntegrationChart Z d F U e
  let f := VectorBundleZeroSection.π Z d F
  let p := affineTraceProjection U.toScheme d
  let sq := Etale.vectorIntegrationChart_isPullback Z d F U e
  let B := Etale.vectorIntegrationCoefficient A N hA Z d F
  let g := Etale.vectorBundleIntegration N hN A hA Z hZ d F
  let adj := Etale.rightDerivedUpperShriekAdjunction A f
  let adj' := Etale.rightDerivedUpperShriekAdjunction A p
  let L := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) p
  let k : L.obj ((Etale.affineTraceRight A N hA U.toScheme d).obj
      (Etale.ordinaryFiniteUnit A U.toScheme)) ⟶ Etale.ordinaryFiniteUnit A U.toScheme :=
    (Etale.affineLinearCompactComparison N hN A hA U.toScheme hU d).inv ≫
    Etale.affineTraceCounit A N hA t D U.toScheme hU d
  have hu (Y : Scheme.{u}) :
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom = 𝟙 _ := by
    apply (cancel_mono (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).inv).mp
    rw [Iso.hom_inv_id, Etale.singleFunctorObjUnitIso_inv]
    exact (Category.id_comp _).symm
  have hp : (Etale.ordinaryFiniteUnitPullback A U.ι).hom =
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) U.ι).hom := by
    have h := Etale.ordinaryFiniteUnitPullback_hom_unit A U.ι
    erw [hu, hu, Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  have ht := Etale.vectorIntegration_frameAdjoint N hN A hA t D Z hZ d F U e
  unfold Etale.dualizingComplexBaseChangeMap at ht
  erw [← hp] at ht
  unfold Etale.CoordinateCounitArrows.towerAdjoint at ht
  erw [hu, Category.comp_id] at ht
  let b := Etale.vectorIntegrationBaseCoefficientPullback A N hA t (a ≫ f) hZ d
  let b' := Etale.vectorIntegrationBaseCoefficientPullback A N hA t p hU d
  let v := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a f
  change (Etale.ordinaryFinitePullback A a).map (adj.homEquiv B _ g) ≫
    (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app _ ≫
    (Etale.rightDerivedUpperShriek A p).map (Etale.ordinaryFiniteUnitPullback A U.ι).hom =
    v.inv.app _ ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p U.ι (a ≫ f) sq.w).hom.app _ ≫
      (Etale.ordinaryFinitePullback A p).map
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t U.ι hZ d).hom ≫
      (Etale.affineLinearCoefficientDescent A N hA t U.toScheme hU d).inv ≫
      adj'.homEquiv _ _ k at ht
  have hc := Etale.vectorIntegrationBaseCoefficientPullback_comp A N hA t
    p U.ι (a ≫ f) sq.w hZ hU d
  change (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    p U.ι (a ≫ f) sq.w).hom.app _ ≫
    (Etale.ordinaryFinitePullback A p).map
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA t U.ι hZ d).hom ≫
    b'.hom = b.hom at hc
  have hc' : b.inv ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        p U.ι (a ≫ f) sq.w).hom.app _ ≫
      (Etale.ordinaryFinitePullback A p).map
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t U.ι hZ d).hom = b'.inv := by
    apply (cancel_mono b'.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id] using congrArg (fun z ↦ b.inv ≫ z) hc
  change b.inv ≫ v.hom.app _ ≫
    (Etale.ordinaryFinitePullback A a).map (adj.homEquiv B _ g) ≫
    (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app _ ≫
    (Etale.rightDerivedUpperShriek A p).map (Etale.ordinaryFiniteUnitPullback A U.ι).hom =
    adj'.homEquiv _ _ (L.map
      ((Etale.affineLinearCoefficientDescent A N hA t U.toScheme hU d ≪≫ b').inv) ≫ k)
  erw [ht, Iso.hom_inv_id_app_assoc v]
  trans b'.inv ≫ (Etale.affineLinearCoefficientDescent A N hA t U.toScheme hU d).inv ≫
    adj'.homEquiv _ _ k
  · simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
      (Etale.affineLinearCoefficientDescent A N hA t U.toScheme hU d).inv ≫
      adj'.homEquiv _ _ k) hc'
  symm
  simpa only [L, Functor.id_obj, Iso.trans_inv, Category.assoc] using adj'.homEquiv_naturality_left
    ((Etale.affineLinearCoefficientDescent A N hA t U.toScheme hU d ≪≫ b').inv) k

/-- Restriction through any inverse linear frame of the actual global integration adjunct
is the ordinary affine counit adjunct, after exact site comparison and endpoint transport.
This equation uses no ordered affine purity identification; zero rank and empty opens
are included.

Source: latest blueprint, sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, second paragraph
(blueprint: lem-pur-vector-chart-restricted-affine-transpose).

Proof in words:
1. Apply the proved vectorIntegration_frameAdjoint equation. The inverse unit comparison
   is the identity, hence so is its forward map. The ordinary-unit pullback square then
   identifies ordinary unit pullback with the monoidal unit comparison. Expand the
   coordinate tower adjunct to obtain the ordinary affine counit adjunct.
2. Precompose with inverse base-coefficient pullback and the inverse-frame compositor.
   Cancel that compositor against its inverse. Apply the proved base-coefficient pullback
   composition equation to the affine projection and open immersion, using the specified
   Cartesian-square equality. Cancelling the resulting coefficient isomorphisms leaves
   inverse projection coefficient pullback followed by inverse affine coefficient descent.
3. Apply adjunction source naturality and exact site comparison. The HEq specification
   of affineTranspose identifies the resulting affineTransposeRaw with the requested
   endpoint transport. No ordered affine purity is used; rank zero and empty opens
   follow from the same equations.
-/
theorem chartTranspose_eq_affine (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    HEq (restrictedRaw P Z aZ d F U e r hA)
      (@affineTranspose P U.toScheme
        (isNoetherian_of_locallyOfFiniteType (U.ι ≫ aZ)) (U.ι ≫ aZ) d r hA) := by
  let : IsNoetherian U.toScheme := isNoetherian_of_locallyOfFiniteType (U.ι ≫ aZ)
  let N := P.coefficients.l ^ (r + 1)
  let hN : 0 < N := pow_pos P.coefficients.prime.out.pos (r + 1)
  let hZ : IsUnit (N : Γ(Z, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (primeUnit P Z aZ).pow (r + 1)
  let t := Etale.projectiveLineTraceTransport N hN (Ring P) hA
  let D := fun Y (_ : IsNoetherian Y) (hY : IsUnit (N : Γ(Y, ⊤))) ↦
    Etale.projectiveLineTraceDatum N hN (Ring P) hA Y hY
  have h := raw_chart_equation N hN (Ring P) hA t D Z hZ d F U e
  have hraw : restrictedRaw P Z aZ d F U e r hA =
      affineTransposeRaw P U.toScheme (U.ι ≫ aZ) d r hA := by
    unfold restrictedRaw affineTransposeRaw
    apply congrArg ((comparison (Ring P) (affineTraceTower U.toScheme d)).map)
    simpa only [N, t, D, Etale.affineTraceCounit,
      Etale.vectorIntegrationCoefficient, Etale.ordinaryFinitePullback] using h
  exact (heq_of_eq hraw).trans
    (affineTranspose_existsUnique P U.toScheme (U.ι ≫ aZ) d r hA).exists.choose_spec.symm

end AlgebraicGeometry.ProEtale.VectorIntegrationChart

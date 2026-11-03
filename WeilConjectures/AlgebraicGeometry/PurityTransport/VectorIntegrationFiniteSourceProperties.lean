/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleVectorIntegration
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineTrace
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleVectorIntegration
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarDescent
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistConstructionsSupplement
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines

import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.CompatibleKummerCoefficients.CompatibleKummerCoefficientData
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.AlgebraicGeometry.Vector.VectorTraceGeometricDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-! # Finite vector integration source properties
Source: thm-pur-vector-bundle-thom Step 3, finite-source refinement steps 1 and 2.
(blueprint: lem-pur-vector-integration-finite-source-properties). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (A : CommRingCat.{0}) [fin : Finite A]
  (n : ℕ) (hA : (ell ^ (n + 1) : A) = 0)
local instance : TopologicalSpace A := ⊥
local instance : DiscreteTopology A := discreteTopology_bot A

variable (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
  (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
  (hS : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(S, ⊤)))
  (hV : IsUnit ((ell ^ (n + 1) : ℕ) :
    Γ(VectorBundleZeroSection.scheme S d F, ⊤)))

/-- The specified compact-support site comparison on this bounded finite input.
Source: thm-pur-vector-bundle-thom Step 3, finite-source refinement step 10
(blueprint: lem-pur-vector-integration-finite-source-properties). -/
def finiteSourceVectorSite :=
  (ProEtale.compactSupportSiteComparison (ULift.{u + 1} A)
    (Etale.vectorBundlePurityCompactification S d F)).app
      ⟨_, finiteSourceCoefficient_plus ell A n hA S d F hS⟩

/-- The actual finite integration in ordinary pro-etale coordinates: compact-support
site comparison followed by comparison of the existing, locally normalized etale
integration. This introduces no freely chosen trace.
Source: thm-pur-vector-bundle-thom Step 3, finite-source refinement step 10
(blueprint: lem-pur-vector-integration-finite-source-properties). -/
def finiteSourceProIntegration :=
  (finiteSourceVectorSite ell A n hA S d F hS).hom ≫
    (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1} A) S).map
      (Etale.vectorBundleIntegration (ell ^ (n + 1))
        (pow_pos (Fact.out : ell.Prime).pos _) (ULift.{u + 1} A)
        (finiteLiftAnnihilator ell A n hA) S hS d F)

/-- The coefficient-presentation source arrow uses the actual scalar/site mate,
the actual vector compact-support scalar map and the normalized root balancing.
It compares the small finite-ring source to the published DVR-quotient source.
Source: thm-pur-vector-bundle-thom Step 3, finite-source refinement step 10
(blueprint: lem-pur-vector-integration-finite-source-properties). -/
def finiteSourcePresentationSource
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (m : ℕ) (hE : ((ell ^ (n + 1) : ℕ) : Scheme.finiteTateCoefficient ell E m) = 0)
    (e : ULift.{u + 1} A ≃+* Scheme.finiteTateCoefficient ell E m)
    (hSell : IsUnit (ell : Γ(S, ⊤))) :=
  (Etale.FiniteSmoothPurity.proScalar e.toRingHom S).map
      (finiteSourceVectorSite ell A n hA S d F hS).hom ≫
    (ProEtale.pbcComparisonReduction S e.toRingHom).hom.app _ ≫
    (Etale.FiniteSmoothPurity.comparison (Scheme.finiteTateCoefficient ell E m) S).map
      (Etale.VectorTraceScalar.vector e.toRingHom (ell ^ (n + 1))
        (pow_pos (Fact.out : ell.Prime).pos _) (finiteLiftAnnihilator ell A n hA)
        hE S hS d F) ≫
    (VectorIntegrationSite.vectorSite ell E m S n hE d F hSell).inv

/-- The coefficient-presentation unit arrow is the scalar/site mate followed by
multiplication on the constant coefficient complex, using the same scalar e.
Source: thm-pur-vector-bundle-thom Step 3, finite-source refinement step 10
(blueprint: lem-pur-vector-integration-finite-source-properties). -/
def finiteSourcePresentationUnit
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (m : ℕ) (e : ULift.{u + 1} A ≃+* Scheme.finiteTateCoefficient ell E m) :=
  (ProEtale.pbcComparisonReduction S e.toRingHom).hom.app
      (Etale.ordinaryFiniteUnit (ULift.{u + 1} A) S) ≫
    (Etale.FiniteSmoothPurity.comparison (Scheme.finiteTateCoefficient ell E m) S).map
      (Etale.VectorTraceScalar.unit e.toRingHom S)

/-- These specified coefficient-presentation arrows identify the exact source and
unit of the published integration, and intertwine the actual integration arrows.
Source: thm-pur-vector-bundle-thom Step 3, finite-source refinement step 10
(blueprint: lem-pur-vector-integration-finite-source-properties).
Proof: restriction along a ring equivalence is exact and inverse to extension,
so its scalar/site mate and the balanced Tate comparisons are invertible. Proper
scalar exchange is likewise invertible under this equivalence; paste with the
open comparison to get the source assertion. On every frame both trace paths
are the same ordered projective-line counit, with balanced root tensors and
multiplication on units. Uniqueness of the locally normalized integration gives
the displayed equality. An arbitrary annihilating exponent is allowed: the
canonical root power map identifies different exponents before this calculation. -/
theorem finiteSourcePresentation_actualIntegration
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (m : ℕ) (hE : ((ell ^ (n + 1) : ℕ) : Scheme.finiteTateCoefficient ell E m) = 0)
    (e : ULift.{u + 1} A ≃+* Scheme.finiteTateCoefficient ell E m)
    (hSell : IsUnit (ell : Γ(S, ⊤))) :
    IsIso (finiteSourcePresentationSource ell A n hA S d F hS E m hE e hSell) ∧
      IsIso (finiteSourcePresentationUnit ell A S E m e) ∧
      (Etale.FiniteSmoothPurity.proScalar e.toRingHom S).map
          (finiteSourceProIntegration ell A n hA S d F hS) ≫
        finiteSourcePresentationUnit ell A S E m e =
      finiteSourcePresentationSource ell A n hA S d F hS E m hE e hSell ≫
        VectorIntegrationSite.vectorIntegration ell E m S n hE d F hSell := by
  let B := ULift.{u + 1} A
  let C := Scheme.finiteTateCoefficient ell E m
  let N := ell ^ (n + 1)
  have hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos _
  let hB := finiteLiftAnnihilator ell A n hA
  let tB := Etale.vectorBundleIntegration N hN B hB S hS d F
  let tC := Etale.vectorBundleIntegration N hN C hE S hS d F
  have hC : IsIso tC :=
    (Etale.vectorBundleIntegration_concentration_and_isIso N hN C hE S hS d F).2
  have hBiso : IsIso tB :=
    (Etale.vectorBundleIntegration_concentration_and_isIso N hN B hB S hS d F).2
  have hU : IsIso (Etale.VectorTraceScalar.unit e.toRingHom S) := by
    dsimp only [Etale.VectorTraceScalar.unit,
      WeilConjectures.PurityFiniteSetting.purityScalarUnitMap,
      WeilConjectures.PurityFiniteSetting.purityTransportUnitMap]
    infer_instance
  have ht : VectorIntegrationSite.vectorIntegration ell E m S n hE d F hSell =
      (VectorIntegrationSite.vectorSite ell E m S n hE d F hSell).hom ≫
        (Etale.FiniteSmoothPurity.comparison C S).map tC := by
    apply (VectorIntegrationSite.existsUniqueVectorIntegration
      ell E m S n hE d F hSell).unique
    · unfold VectorIntegrationSite.vectorIntegration
      exact (VectorIntegrationSite.existsUniqueVectorIntegration
        ell E m S n hE d F hSell).exists.choose_spec
    · apply (VectorIntegrationSite.normalization_comparison
        ell E m S n hE d F hSell tC).2
      exact (Etale.existsUnique_vectorIntegrationGluing
        N hN C hE S hS d F).2.exists.choose_spec.2
  have hEq :
      (Etale.FiniteSmoothPurity.proScalar e.toRingHom S).map
          (finiteSourceProIntegration ell A n hA S d F hS) ≫
        finiteSourcePresentationUnit ell A S E m e =
      finiteSourcePresentationSource ell A n hA S d F hS E m hE e hSell ≫
        VectorIntegrationSite.vectorIntegration ell E m S n hE d F hSell := by
    have hv := (Etale.VectorTraceScalar.vectorTraceScalarDescent
      N hN e.toRingHom hB hE S hS d F).2.2.2.2
    have hn := (ProEtale.pbcComparisonReduction S e.toRingHom).hom.naturality tB
    dsimp only [Functor.comp_map] at hn
    rw [ht]
    simp only [finiteSourceProIntegration, finiteSourcePresentationSource,
      finiteSourcePresentationUnit, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc]
    erw [reassoc_of% hn]
    erw [← Functor.map_comp, ← hv]
    simp only [Functor.map_comp, B, C, N, tC, Etale.FiniteSmoothPurity.comparison,
      Etale.vectorIntegrationSource, Etale.rightDerivedLowerShriek,
      Etale.vectorBundlePurityCompactification, DerivedCategory.Plus.ι, ObjectProperty.ι_obj]
  have hUnit : IsIso (finiteSourcePresentationUnit ell A S E m e) := by
    dsimp only [finiteSourcePresentationUnit]
    infer_instance
  have hIntegration : IsIso (finiteSourceProIntegration ell A n hA S d F hS) := by
    dsimp only [finiteSourceProIntegration]
    infer_instance
  have hPublished : IsIso
      (VectorIntegrationSite.vectorIntegration ell E m S n hE d F hSell) := by
    rw [ht]
    infer_instance
  have hComposite : IsIso
      (finiteSourcePresentationSource ell A n hA S d F hS E m hE e hSell ≫
        VectorIntegrationSite.vectorIntegration ell E m S n hE d F hSell) := by
    rw [← hEq]
    infer_instance
  have hSource : IsIso
      (finiteSourcePresentationSource ell A n hA S d F hS E m hE e hSell) :=
    IsIso.of_isIso_comp_right
      (finiteSourcePresentationSource ell A n hA S d F hS E m hE e hSell)
      (VectorIntegrationSite.vectorIntegration ell E m S n hE d F hSell)
  exact ⟨hSource, hUnit, hEq⟩

set_option maxHeartbeats 1600000 in
-- The pasted derived-support square exceeds the default budget at its final reassociation.
private def finiteSourceEtaleTransport (B : Type (u + 1)) [CommRing B]
    (N : ℕ) (hN : 0 < N) (hB : (N : B) = 0) :
    Etale.OrdinaryFiniteTwistTransport B N hB where
  roots := (Scheme.finiteEtaleTwistPullbackData B N hN hB).r
  line f hY := (Scheme.finiteEtaleTwistPullbackData B N hN hB).c f hY
    (affineTracePullbackInvertible N f hY) 1
  roots_normalization := (Scheme.finiteEtaleTwistPullbackData B N hN hB).laws.2.1
  line_normalization f hY :=
    (Scheme.finiteEtaleTwistPullbackData B N hN hB).laws.2.2.1 f hY
      (affineTracePullbackInvertible N f hY)

private theorem finiteSourceComp_transport (B : Type (u + 1)) [CommRing B]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : h = f ≫ g) (K : Etale.DerivedCategoryModule B Z) :
    (eqToIso (congrArg (Etale.ordinaryFinitePullback B) w)).app K ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g).app K =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f g h w).app K := by
  subst h
  apply Iso.ext
  exact Category.id_comp _

end AlgebraicGeometry.ProEtale.PurityTransport

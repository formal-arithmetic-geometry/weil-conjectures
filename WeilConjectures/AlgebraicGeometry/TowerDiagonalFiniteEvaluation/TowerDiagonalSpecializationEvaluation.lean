/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothTwoLevelReduction
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOrdinaryTwistCocycle
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothProQuotientTransport
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothSiteRealizations
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation

/-! # Evaluation of the inverse zero restriction

Source: latest blueprint, tower-geometric gamma proof (1), specialization at zero
(blueprint: lem-pur-tower-diagonal-specialization-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation

attribute [local implicit_reducible] SpTowerP1.realization reductionSite
  sfIntrinsicDerivedEquivalence CategoryTheory.Equivalence.mapDerivedCategory
  CategoryTheory.Equivalence.mk C family normal vC vNormal vPullC vFamily vFibre

set_option maxHeartbeats 2000000 in
-- Naturality crosses the intrinsic and fixed-module presentations of derived realization.
private theorem pullV_naturality (D : Data.{u}) {T S : Scheme.{u}} (g : T ⟶ S) (n : ℕ)
    {M M' : Sys D S} {K K' : Et D n S} (e : M ⟶ M') (r : K ⟶ K')
    (v : (ev D S n).obj M ⟶ (nu D n S).obj K)
    (v' : (ev D S n).obj M' ⟶ (nu D n S).obj K')
    (he : (ev D S n).map e ≫ v' = v ≫ (nu D n S).map r) :
    (ev D T n).map ((inverseImage D g).map e) ≫
        pullV D.ell (scalars D) D.b D.o g n M' K' v' =
      pullV D.ell (scalars D) D.b D.o g n M K v ≫
        (nu D n T).map ((Etale.ordinaryFinitePullback (An D n) g).map r) := by
  unfold pullV
  let P := proEtaleConstantRingDerivedPullback (SpTowerShriek.R D.ell (scalars D) n) g
  have hp := ((D.o.geometry g).pullEvaluation n).hom.naturality e
  have hs := (reductionSitePullbackIso (SpTowerShriek.R D.ell (scalars D) n) g).hom.naturality r
  dsimp only [Functor.comp_map, reductionSite, sfIntrinsicDerivedEquivalence,
    CategoryTheory.Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk,
    Functor.comp_map] at hs
  change (ev D T n).map ((inverseImage D g).map e) ≫
      ((D.o.geometry g).pullEvaluation n).hom.app M' ≫ P.map v' ≫ _ = _
  rw [reassoc_of% hp]
  simp only [Functor.comp_map, Category.assoc]
  rw [← P.map_comp_assoc, he, P.map_comp]
  simp only [Category.assoc]
  dsimp only [nu, SpTowerP1.nu, SpTowerP1.realization, Functor.comp_map]
  exact congrArg (fun x ↦ ((D.o.geometry g).pullEvaluation n).hom.app M ≫ P.map v ≫ x) hs

private theorem inverse_square {C₁ C₂ C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    (F : C₁ ⥤ C₃) (G : C₂ ⥤ C₃) {M N : C₁} {K L : C₂}
    (i : M ≅ N) (j : K ≅ L) (v : F.obj M ⟶ G.obj K) (w : F.obj N ⟶ G.obj L)
    (h : F.map i.hom ≫ w = v ≫ G.map j.hom) :
    F.map i.inv ≫ v = w ≫ G.map j.inv := by
  apply (cancel_epi (F.map i.hom)).1
  simp only [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]

private theorem chain_three {C : Type*} [Category C]
    {A B C₀ D A' B' C' D' : C}
    {a : A ⟶ B} {b : B ⟶ C₀} {c : C₀ ⟶ D}
    {v₀ : A ⟶ A'} {v₁ : B ⟶ B'} {v₂ : C₀ ⟶ C'} {v₃ : D ⟶ D'}
    {a' : A' ⟶ B'} {b' : B' ⟶ C'} {c' : C' ⟶ D'}
    (ha : a ≫ v₁ = v₀ ≫ a') (hb : b ≫ v₂ = v₁ ≫ b')
    (hc : c ≫ v₃ = v₂ ≫ c') :
    (a ≫ b ≫ c) ≫ v₃ = v₀ ≫ a' ≫ b' ≫ c' := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc b, hb, Category.assoc, ← Category.assoc a, ha]
  simp only [Category.assoc]

private theorem map_chain {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C₀ E : C} {X : D} (v : X ⟶ F.obj A)
    (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ E) :
    v ≫ F.map a ≫ F.map b ≫ F.map c = v ≫ F.map (a ≫ b ≫ c) := by
  simp only [F.map_comp]

set_option maxHeartbeats 4000000 in
-- The specialization equation crosses two derived pullback presentations.
/-- The delta equation follows from evaluation of kappa, its zero-section compositor,
and the exceptional zero-fibre mate. No equality of arbitrary derived maps is inferred
from equality of their levels.

Source: tower-geometric gamma proof (1), inverse restriction at zero
(blueprint: lem-pur-tower-diagonal-specialization-evaluation).

Proof: Invert the kappa evaluation square by composing with the two inverse kappa maps.
Naturality of pullEvaluation and of the ordinary-etale/pro-etale pullback comparison
pulls that square to the zero section. Expand deltaTower as s0, pullback of inverse kappa,
then eta. Substitute the zero-fibre equation, the pulled inverse-kappa square, and the
zero-section equation in that order. Functoriality combines the three finite arrows into
the defining specialization formula delta_n. This uses only inverse and composition laws,
so includes dimension zero, the empty scheme, and the first positive coefficient level.
-/
theorem specialization_evaluation (D : Data.{u}) (U : Evaluations D)
    (finiteκ : ∀ n : ℕ, Kappa D n)
    (κ : family D ≅ (inverseImage D (a D)).obj (C D))
    (s₀ : C D ≅ (inverseImage D (i₀ D)).obj ((inverseImage D (a D)).obj (C D)))
    (η : (inverseImage D (i₀ D)).obj (family D) ≅ normal D)
    (hκ : ∀ n : ℕ,
      (ev D (A D) n).map κ.hom ≫ vPullC D U (a D) n =
        vFamily D U n ≫ (nu D n (A D)).map (finiteκ n).hom)
    (hs : ∀ n : ℕ,
      (ev D D.X n).map s₀.hom ≫
          pullV D.ell (scalars D) D.b D.o (i₀ D) n
            ((inverseImage D (a D)).obj (C D))
            ((Etale.ordinaryFinitePullback (An D n) (a D)).obj
              (Etale.sectionInvariant (An D n) (p₁ D) (Δ D))) (vPullC D U (a D) n) =
        vC D U n ≫ (nu D n D.X).map
          ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} (An D n))
            (i₀ D) (a D) (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) D.X)).inv.app _))
    (hη : ∀ n : ℕ,
      (ev D D.X n).map η.hom ≫ vNormal D U n =
        vFibre D U (i₀ D) n ≫ (nu D n D.X).map
          (Etale.NoetherianSectionSpecialization.atZero (An D n) (p₁ D) (Δ D))) :
    ∀ n : ℕ,
      (ev D D.X n).map (deltaTower D κ s₀ η).hom ≫ vNormal D U n =
        vC D U n ≫ (nu D n D.X).map (delta_n D n (finiteκ n)) := by
  intro n
  have hi := inverse_square (ev D (A D) n) (nu D n (A D)) κ (finiteκ n)
    (vFamily D U n) (vPullC D U (a D) n) (hκ n)
  have hp := pullV_naturality D (i₀ D) n κ.inv (finiteκ n).inv
    (vPullC D U (a D) n) (vFamily D U n) hi
  dsimp only [deltaTower, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [(ev D D.X n).map_comp, (ev D D.X n).map_comp]
  exact (chain_three (hs n) hp (hη n)).trans
    (map_chain (nu D n D.X) (vC D U n)
      ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} (An D n))
        (i₀ D) (a D) (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) D.X)).inv.app _)
      ((Etale.ordinaryFinitePullback (An D n) (i₀ D)).map (finiteκ n).inv)
      (Etale.NoetherianSectionSpecialization.atZero (An D n) (p₁ D) (Δ D)))

end AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation

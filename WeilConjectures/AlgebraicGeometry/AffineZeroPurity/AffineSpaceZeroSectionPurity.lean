/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceCoordinateBoundaries
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientation
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionConstructions
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionProductRecursion
import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionOrientationCoordinates
import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionContractionCoordinates
import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionNormalization
import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineLineComparisonNaturality
import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationFusion
import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingFinitePowers
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange

/-! # Zero-section purity for affine space

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.md, and its eight-step DAG proof
(blueprint: cor-pur-affine-space-zero-section-purity).

The ordinary supported Cartier family and the specified exact site comparison
construct the coordinate boundaries. Their supported cup product, including the
empty unit, determines the Thom map by the closed exceptional Hom bijection.
The inverse uses the actual ordered affine-space comparison and the conjugate
of the specified compact-support compositor. No purity isomorphism is chosen.

## Main definitions

- `supportedClass`, `thom`: the actual coordinate product and its exceptional adjunct.
- `gamma`, `normalization`: the recorded comparison and its normalized inverse candidate.
- `classBaseChange`: the canonical closed exchange followed by derived inverse image.

## Main statements

- `zeroSection_purity`: invertibility and both normalized inverse equations.
- `zeroSection_purity_untwisted`: the equivalent negative twist and shift.
- `zeroSection_purity_baseChange`: compatibility with arbitrary base change.
-/

set_option autoImplicit false

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineLinePurity VectorIntegrationSite

set_option maxHeartbeats 800000 in
-- Comparing the two root exponents unfolds the finite coefficient presentation.
section NormalizedThom

open AffineSpacePurity

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe v w

private theorem transport_normalized {C : Type v} [Category.{w} C]
    {M W R R' S : C} (e : M ≅ W) (d : R ≅ S)
    (u : W ⟶ R) (v : M ⟶ S) (a : R ⟶ R') (a' : R' ⟶ W) (b : S ⟶ M)
    (hv : IsIso v) (hs : u ≫ d.hom = e.inv ≫ v)
    (ht : d.inv ≫ a ≫ a' ≫ e.inv = b) (he : v ≫ b = 𝟙 M) :
    IsIso u ∧ u ≫ a ≫ a' = 𝟙 W := by
  have hu : u = e.inv ≫ v ≫ d.inv := by
    apply (cancel_mono d.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hs
  refine ⟨?_, ?_⟩
  · rw [hu]
    have := hv
    infer_instance
  · apply (cancel_mono e.inv).1
    calc
      (u ≫ a ≫ a') ≫ e.inv = (u ≫ d.hom) ≫ (d.inv ≫ a ≫ a' ≫ e.inv) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = (e.inv ≫ v) ≫ b := by rw [hs, ht]
      _ = 𝟙 W ≫ e.inv := by
        simp only [Category.assoc, he, Category.comp_id, Category.id_comp]

private theorem section_normalization
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    IsIso (sectionAdjunct P n B aB r) ∧
      sectionAdjunct P n B aB r ≫
        (rightDerivedUpperShriek (setting P n).Coefficient (lastSection B r)).map
          (CoordinateTowerNormalization.targetLineGamma P n B aB r) ≫
        CoordinateTowerNormalization.lineCollapse P n B aB r = 𝟙 _ := by
  let := (tower_geometry aB r).1
  let := (tower_geometry aB r).2.1
  let := (tower_geometry aB r).2.2
  let : IsNoetherian (iteratedAffineLine B r) :=
    tower_noetherian (setting P n) B aB r
  obtain ⟨hI, _, _, _, _, _, hNorm⟩ :=
    CoordinateSectionNormalization.twistedCoordinateSectionNormalization
      (setting P n) (iteratedAffineLine B r) (towerBase aB r)
  obtain ⟨hT, _, _, hp⟩ := hNorm (setting P n).level (annihilates (setting P n))
  obtain ⟨hM, hplus, hpf, hunit, hu, _, he⟩ :=
    hp (CoordinateSectionCoordinates.input P n (iteratedAffineLine B r) r)
      (Or.inr ⟨r, rfl⟩)
  exact transport_normalized
    (CoordinateSectionCoordinates.tateComparison P n _ (towerBase aB r) r)
    (CoordinateSectionCoordinates.orientationTargetComparison P n B aB r)
    (sectionAdjunct P n B aB r) _ _ _ _ hu
    (CoordinateSectionCoordinates.sectionAdjunct_coordinates P n B aB r hI hT hpf)
    (CoordinateSectionCoordinates.lineContraction_coordinates P n B aB r hM hplus hunit) he

/-- Pull back a supported product using the actual closed exchange map, exact
inverse image, and the canonical ordered Tate-line pullback identification.
Its exceptional transpose is the closed exceptional base-change mate.
Source: proof Step 7 (blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def classBaseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c) :
    (cupSingle (setting P n) (iteratedAffineLine B' c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)).obj
        ((setting P n).constant B')) ⟶ target P n (iteratedAffineLine B' c) c :=
  (coordinateSourcePullback P n g c).inv ≫
    (AffineSpacePurity.inverseImage (setting P n).Coefficient (spaceMap g c)).map α ≫
    (targetPullbackIso P n (spaceMap g c) (AffineSpacePurity.towerBase aB c) c).hom

attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
  originCompositionAmbient derivedComparisonAdjunction identityUnit
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

end NormalizedThom

end AlgebraicGeometry.ProEtale.AffineZeroPurity

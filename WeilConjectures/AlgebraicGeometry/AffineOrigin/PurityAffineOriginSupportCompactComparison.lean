/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientQuotientLine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.PurityRankOneLocalCalculation
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper

import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardComparison

/-!
# Support at the origin and compact support on the affine line

Source: latest blueprint, sec-smooth-purity/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison).

The coefficient rings, Tate lines, closed-support kernel, open extension by zero,
and derived direct images below are the published constructions. In particular,
the supported and compact objects are objects of the sheaf-valued ordinary derived
category on the small pro-etale site of the geometric point.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineOrigin

/-- The four coefficient cases; finite level n means the positive exponent n+1.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
inductive Stage
  | finite (n : ℕ)
  | integral
  | rational
  | closure

/-- The actual condensed rings, with the finite-subextension-valued closure ring.
Source: coefficient convention in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def ring (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) : Stage →
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  | .finite n => Profinite.continuousMapRingObj (completedResidue l E π n)
  | .integral => Profinite.padicIntegersRingObj l E.1
  | .rational => Profinite.continuousMapRingObj E.1
  | .closure => Profinite.padicAlgClRingObj l

/-- The published positive Tate lines, including every uniformizer quotient.
Source: sk-def-sp-tate-twist and its uniformizer reduction
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def line (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (X : Scheme.{u}) :
    (b : Stage) → CondensedRing.supportModules (ring l E π b) X
  | .finite n => DiagonalCoefficients.quotientLine l E π n X
  | .integral => spIntegralTwist X l E
  | .rational => spRationalTwist X l E
  | .closure => spQbarTwist X l

/-- The canonical chart A^1 -> P^1, with the same one-coordinate presentation as
PurityFiniteSetting.Line. Source: fixed compactification in Step 2
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def chart (s : Scheme.{u}) : WeilConjectures.PurityFiniteSetting.Line s ⟶ ProjectiveLine s :=
  AffineSpace.reindex (fun _ : PUnit.{u + 1} => (ULift.up 0 : ULift.{u} (Fin 1))) s ≫
    ProjectiveLine.affineChart s

/-- The fixed chart lies over the affine-line projection.
Source: fixed compactification in Step 1
(blueprint: lem-pur-affine-origin-support-compact-comparison).
Proof: compose the standard affine-chart projection equation with the singleton
reindexing projection equation; both are the published affine-space structure maps. -/
theorem chart_over (s : Scheme.{u}) :
    chart s ≫ (ProjectiveLine s ↘ s) =
      WeilConjectures.PurityFiniteSetting.lineProjection s := by sorry

/-- The fixed standard compactification, as actual scheme data.
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def compactification (s : Scheme.{u}) :
    Compactification (WeilConjectures.PurityFiniteSetting.lineProjection s) where
  Z := ProjectiveLine s
  g := ProjectiveLine s ↘ s
  i := chart s
  comm := (chart_over s).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Rq_* j_! for the fixed standard projective-line compactification: the published
derived lower shriek of this compactification (exact j_! followed by Rq_*).
Source: Step 1 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev compact (s : Scheme.{u}) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification Λ (compactification s)

/-- The published Tate line in degree zero.
Source: Step 2 (blueprint: lem-pur-affine-origin-support-compact-comparison). -/
def tate (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (b : Stage) (s : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (CondensedRing.supportModules (ring l E π b)
    (WeilConjectures.PurityFiniteSetting.Line s)) 0).obj
      (line l E π (WeilConjectures.PurityFiniteSetting.Line s) b)

set_option maxHeartbeats 1600000 in
-- The retained site-comparison square elaborates several large derived-category instances.
set_option maxHeartbeats 1600000 in
-- Naming the witness objects keeps the compatibility predicate from expanding their data.
set_option maxHeartbeats 1600000 in
-- The semilinear coefficient unit involves the large module-object action instances.
set_option maxHeartbeats 1600000 in
-- The quotient comparison elaborates the integral and finite module actions simultaneously.
/-- The coefficient A_n, regarded as an R_s-module, without deriving a quotient.
Source: source inverse-limit clause
(blueprint: lem-pur-affine-origin-support-compact-comparison). -/
abbrev restrictedUnit (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (s : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology s) Ab.{u + 1})
    (coefficientMap (DiagonalCoefficients.quotientMap l E π n) s)).obj
    (Mod.regular (condensedRingObj (ring l E π (.finite n)) s))

set_option maxHeartbeats 1600000 in
-- The tower legs compare the exact-single and restricted coefficient presentations.
end AlgebraicGeometry.ProEtale.AffineOrigin

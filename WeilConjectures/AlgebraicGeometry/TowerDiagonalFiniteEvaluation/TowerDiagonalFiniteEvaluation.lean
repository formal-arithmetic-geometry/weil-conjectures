/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothTwoLevelReduction
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOrdinaryTwistCocycle
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorComposition
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothProQuotientTransport
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothSiteRealizations
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionAffineCoordinates
import WeilConjectures.AlgebraicGeometry.AffineLineNormalizedDescent.EtaleShiftedLineNormalizedDescent
import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalDualizingComparisons
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationFrameAdjoint
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionGeneralBase
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGlobalChartAdjunction

/-!
# Finite evaluation of the actual tower diagonal and deformation diagram

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md`, paragraph (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation).

This file records the geometric statement.  The input is the actual diagonal and its
extended-Rees deformation over a field, together with the four tower adjunctions supplied
by tower gluing.  The three comparison isomorphisms are witnesses in the conclusion: they
are characterized by the exceptional base-change mate, normalized section specialization,
and Kummer-normalized vector integration evaluation equations.  Thus no orientation,
comparison map, or proposition-valued placeholder is an input field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u


open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale WeilConjectures

namespace AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation

/-- Universe lift of exactly Q_ell. Source: coefficient convention
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev Qell (ell : ℕ) [Fact ell.Prime] := ULift.{u} (Padic ell)


attribute [local instance 1100] CategoryTheory.instOverClass

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (coords : SpTowerCalculus.Coordinates ell E b)

instance (D : Data.{u}) : Fact D.ell.Prime := D.ellPrime
instance (D : Data.{u}) : Field D.k := D.kField
instance (D : Data.{u}) : CharP D.k D.pchar := D.kChar
instance (D : Data.{u}) : IsNoetherian D.X := D.noethX
instance (D : Data.{u}) : IsNoetherian D.Y := D.noethY
instance (D : Data.{u}) : IsSeparated D.Xk := D.sepX
instance (D : Data.{u}) : LocallyOfFiniteType D.Xk := D.ftX
instance (D : Data.{u}) : QuasiCompact D.Xk := D.qcX
instance (D : Data.{u}) : IsSeparated D.Yk := D.sepY
instance (D : Data.{u}) : LocallyOfFiniteType D.Yk := D.ftY
instance (D : Data.{u}) : QuasiCompact D.Yk := D.qcY
instance (D : Data.{u}) : IsOpenImmersion D.j := D.openJ
instance (D : Data.{u}) : IsProper D.p := D.properP
instance (D : Data.{u}) : QuasiCompact (D.j ≫ D.p) := D.qcF
instance (D : Data.{u}) : IsSeparated (D.j ≫ D.p) := D.sepF
instance (D : Data.{u}) : HasCompactification (D.j ≫ D.p) := D.compactF
instance (D : Data.{u}) : HasCompactification (pullback.fst (D.j ≫ D.p) (D.j ≫ D.p)) := D.compactP₁
instance (D : Data.{u}) : HasCompactification
    (Scheme.Hom.normalConeProj (pullback.fst (D.j ≫ D.p) (D.j ≫ D.p))
      (pullback.diagonal (D.j ≫ D.p))) := D.compactPi
instance (D : Data.{u}) : HasCompactification
    (Scheme.Hom.deformationSpaceProj (pullback.fst (D.j ≫ D.p) (D.j ≫ D.p))
      (pullback.diagonal (D.j ≫ D.p))) := D.compactH
instance (D : Data.{u}) : SmoothOfRelativeDimension D.d (D.j ≫ D.p) := D.smoothF
/-- The diagonal geometry is obtained from the finite section theorem, not assumed.
Source: gamma (1), geometric preparation
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
instance (D : Data.{u}) : Etale.FiniteRingSectionDeformation.Geometry D.d
    (pullback.fst (D.j ≫ D.p) (D.j ≫ D.p)) (pullback.diagonal (D.j ≫ D.p)) :=
  Etale.FiniteRingSectionDeformation.geometry D.d
    (pullback.fst (D.j ≫ D.p) (D.j ≫ D.p)) (pullback.diagonal (D.j ≫ D.p))
    (pullback.diagonal_fst (D.j ≫ D.p))

/-- The actual W in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev W (D : Data.{u}) := pullback (D.j ≫ D.p) (D.j ≫ D.p)
/-- The actual p₁ in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev p₁ (D : Data.{u}) : W D ⟶ D.X := pullback.fst (D.j ≫ D.p) (D.j ≫ D.p)
/-- The actual p₂ in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev p₂ (D : Data.{u}) : W D ⟶ D.X := pullback.snd (D.j ≫ D.p) (D.j ≫ D.p)
/-- The actual Δ in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev Δ (D : Data.{u}) : D.X ⟶ W D := pullback.diagonal (D.j ≫ D.p)
/-- The actual N in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev N (D : Data.{u}) := (Δ D).ker.normalCone
/-- The actual π in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev π (D : Data.{u}) : N D ⟶ D.X := Scheme.Hom.normalConeProj (p₁ D) (Δ D)
/-- The actual z in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev z (D : Data.{u}) : D.X ⟶ N D := (Δ D).normalConeZeroSection
/-- The actual A in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev A (D : Data.{u}) := AffineSpace (ULift.{u} (Fin 1)) D.X
/-- The actual a in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev a (D : Data.{u}) : A D ⟶ D.X :=
  (AffineSpace.over (n := ULift.{u} (Fin 1)) (S := D.X)).hom
/-- The actual deformation in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev deformation (D : Data.{u}) := (Δ D).ker.deformationSpace
/-- The actual h in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev h (D : Data.{u}) : deformation D ⟶ A D :=
  Scheme.Hom.deformationSpaceProj (p₁ D) (Δ D)
/-- The actual Δtilde in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev Δtilde (D : Data.{u}) : A D ⟶ deformation D := (Δ D).deformationSpaceSection
/-- The actual i₀ in the diagonal/DNC diagram. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
noncomputable abbrev i₀ (D : Data.{u}) : D.X ⟶ A D :=
  AffineSpace.zeroSection (ULift.{u} (Fin 1)) D.X
instance (D : Data.{u}) : HasCompactification (p₁ D) := D.compactP₁
instance (D : Data.{u}) : HasCompactification (π D) := D.compactPi
instance (D : Data.{u}) : HasCompactification (h D) := D.compactH
instance (D : Data.{u}) : IsNoetherian (N D) := by
  dsimp [N, Δ]
  infer_instance
instance (D : Data.{u}) : IsNoetherian (deformation D) := by
  dsimp [deformation, Δ]
  infer_instance
instance (D : Data.{u}) : IsNoetherian (A D) := by
  dsimp [A]
  infer_instance

/-- The specified inverse image of systems. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev pull {U V : Scheme.{u}} (g : U ⟶ V) :=
  SpTowerShriek.pull ell E b (o.geometry g)

/-- Evaluate pullback and then transport to the ordinary etale inverse image.
Every factor is a published site/evaluation comparison. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def pullV {U V : Scheme.{u}} (g : U ⟶ V) (n : ℕ)
    (M : SpTowerShriek.D ell E V)
    (K : Etale.DerivedCategoryModule (SpTowerP1.levelRing ell E n) V)
    (v : (SpTowerShriek.Ev ell E V n).obj M ⟶ (SpTowerP1.nu ell E n V).obj K) :
    (SpTowerShriek.Ev ell E U n).obj ((pull ell E b o g).obj M) ⟶
      (SpTowerP1.nu ell E n U).obj
        ((Etale.ordinaryFinitePullback (SpTowerP1.levelRing ell E n) g).obj K) :=
  ((o.geometry g).pullEvaluation n).hom.app M ≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R ell E n) g).map v ≫
    (reductionSitePullbackIso (SpTowerShriek.R ell E n) g).hom.app K

/-- The scalar in Q_ell is lifted only to allow schemes in every universe.
Source: gamma (1), E=Q_ell (blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev scalars (D : Data.{u}) := Qell.{u} D.ell

/-- The positive finite ring; index n is the exponent n+1 throughout the tower API.
Source: gamma (1) (blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev An (D : Data.{u}) (n : ℕ) := SpTowerP1.levelRing D.ell (scalars D) n

/-- Ordinary etale finite complexes. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev Et (D : Data.{u}) (n : ℕ) (T : Scheme.{u}) := Etale.DerivedCategoryModule (An D n) T

/-- Actual derived systems. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev Sys (D : Data.{u}) (T : Scheme.{u}) := SpTowerShriek.D D.ell (scalars D) T

/-- Canonical ordinary-etale/pro-etale coefficient transport. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev nu (D : Data.{u}) (n : ℕ) (T : Scheme.{u}) := SpTowerP1.nu D.ell (scalars D) n T

/-- Actual evaluation. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev ev (D : Data.{u}) (T : Scheme.{u}) (n : ℕ) := SpTowerShriek.Ev D.ell (scalars D) T n

/-- Actual pullback. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev inverseImage (D : Data.{u}) {U V : Scheme.{u}} (g : U ⟶ V) :=
  pull D.ell (scalars D) D.b D.o g

/-- The two section invariants and the deformation family, before evaluation.
Source: gamma (1) (blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def C (D : Data.{u}) : Sys D D.X :=
  (inverseImage D (Δ D)).obj (omega D.ell (scalars D) D.b D.o D.coords D.towerP₁)

/-- The deformation section invariant, before evaluation. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def family (D : Data.{u}) : Sys D (A D) :=
  (inverseImage D (Δtilde D)).obj (omega D.ell (scalars D) D.b D.o D.coords D.towerH)

/-- The normal-bundle section invariant, before evaluation. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def normal (D : Data.{u}) : Sys D D.X :=
  (inverseImage D (z D)).obj (omega D.ell (scalars D) D.b D.o D.coords D.towerPi)

/-- Positive ell-powers are units on every scheme over the given field.
Source: gamma (1), characteristic assumption
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev units (D : Data.{u}) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of D.k))
    (n : ℕ) : IsUnit ((D.ell ^ (n + 1) : ℕ) : Γ(T, ⊤)) := by
  have hk : IsUnit (D.ell : D.k) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : D.ell.Prime) D.hne).isUnit
  have hs : IsUnit (D.ell : Γ(Spec (CommRingCat.of D.k), ⊤)) := by
    simpa only [map_natCast] using hk.map (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv.hom
  have ht : IsUnit (D.ell : Γ(T, ⊤)) := by
    simpa only [map_natCast] using hs.map t.appTop.hom
  simpa only [Nat.cast_pow] using ht.pow (n + 1)

/-- The canonical homogeneous Rees comparison followed by the canonical symmetric
normal-bundle comparison. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def coneBundle (D : Data.{u}) :=
  Etale.FiniteSmoothPurity.reesConeComparison (Δ D) ≪≫
    Etale.FiniteRingSectionDeformation.coneBundleIso D.d (p₁ D) (Δ D)

/-- The required square has its four arrows fixed, rather than an arbitrary
cone-to-bundle isomorphism. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def NormalSquare (D : Data.{u}) : Prop :=
  IsPullback (coneBundle D).hom (π D)
    (VectorBundleZeroSection.π D.X D.d (ConormalGradedAlgebra.piece (Δ D) 1)) (𝟙 D.X)

/-- The ordinary finite diagonal mate, exactly the first general-base factor.
Source: gamma (1), finite orientation (blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def beta_n (D : Data.{u}) (n : ℕ) := Etale.finiteSmoothDiagonalFactor (An D n) (D.j ≫ D.p)

/-- The finite normalized deformation comparison type. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
abbrev Kappa (D : Data.{u}) (n : ℕ) :=
  Etale.NoetherianSectionSpecialization.family (An D n) (p₁ D) (Δ D) ≅
    (Etale.ordinaryFinitePullback (An D n) (a D)).obj
      (Etale.sectionInvariant (An D n) (p₁ D) (Δ D))

/-- The finite specialization is the inverse zero restriction of the normalized
comparison, with the fixed zero-fibre mate. Source: gamma (1), finite orientation
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def delta_n (D : Data.{u}) (n : ℕ) (κ : Kappa D n) :=
  Etale.NoetherianSectionSpecialization.specialization (An D n) (p₁ D) (Δ D) κ

/-- The forward finite Kummer-integration adjoint on the canonical normal bundle.
The normal transport is the fixed exceptional mate, and the bundle arrow is the
published adjunct of Kummer/projective-line integration. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def integration_n (D : Data.{u}) (sq : NormalSquare D) (n : ℕ) :=
  Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      (D.ell ^ (n + 1)) (pow_pos (Fact.out : D.ell.Prime).pos _)
      (An D n) (SpTowerP1.levelAnnihilates D.ell (scalars D) n)
      D.X (units D D.Xk n) D.d (ConormalGradedAlgebra.piece (Δ D) 1) ≫
    Etale.FiniteSmoothPurity.normalSectionMap (An D n) D.d (p₁ D) (Δ D)
      (pullback.diagonal_fst (D.j ≫ D.p)) sq

/-- The actual finite inverse integration arrow. Its only parameter is a proof of
invertibility of the specified adjunct, never a choice of a map. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def q_n (D : Data.{u}) (sq : NormalSquare D) (n : ℕ) (hq : IsIso (integration_n D sq n)) :=
  @inv _ _ _ _ (integration_n D sq n) hq

/-- The diagonal pullback of the p1 comparison. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def vC (D : Data.{u}) (U : Evaluations D) (n : ℕ) :=
  pullV D.ell (scalars D) D.b D.o (Δ D) n
    (omega D.ell (scalars D) D.b D.o D.coords D.towerP₁)
    (Etale.dualizingComplex (An D n) (p₁ D)) (vP₁ D U n)

/-- The zero-section pullback of the pi comparison. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def vNormal (D : Data.{u}) (U : Evaluations D) (n : ℕ) :=
  pullV D.ell (scalars D) D.b D.o (z D) n
    (omega D.ell (scalars D) D.b D.o D.coords D.towerPi)
    (Etale.dualizingComplex (An D n) (π D)) (vPi D U n)

/-- The deformation section pullback of the h comparison. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def vFamily (D : Data.{u}) (U : Evaluations D) (n : ℕ) :=
  pullV D.ell (scalars D) D.b D.o (Δtilde D) n
    (omega D.ell (scalars D) D.b D.o D.coords D.towerH)
    (Etale.dualizingComplex (An D n) (h D)) (vH D U n)

/-- Pullback of the diagonal comparison along a morphism into X. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def vPullC (D : Data.{u}) (U : Evaluations D) {T : Scheme.{u}} (g : T ⟶ D.X) (n : ℕ) :=
  pullV D.ell (scalars D) D.b D.o g n (C D)
    (Etale.sectionInvariant (An D n) (p₁ D) (Δ D)) (vC D U n)

/-- The h comparison restricted to a fibre of the affine line. Source: gamma (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def vFibre (D : Data.{u}) (U : Evaluations D) (g : D.X ⟶ A D) (n : ℕ) :=
  pullV D.ell (scalars D) D.b D.o g n (family D)
    (Etale.NoetherianSectionSpecialization.family (An D n) (p₁ D) (Δ D)) (vFamily D U n)

/-- The zero-fibre specialization is built from kappa itself and the fibre mate.
Source: gamma (1), delta=(i0*kappa)^(-1) with the canonical fibre identifications
(blueprint: lem-pur-tower-diagonal-finite-evaluation). -/
def deltaTower (D : Data.{u})
    (κ : family D ≅ (inverseImage D (a D)).obj (C D))
    (s₀ : C D ≅ (inverseImage D (i₀ D)).obj ((inverseImage D (a D)).obj (C D)))
    (η : (inverseImage D (i₀ D)).obj (family D) ≅ normal D) : C D ≅ normal D :=
  s₀ ≪≫ (inverseImage D (i₀ D)).mapIso κ.symm ≪≫ η

private theorem inverse_integration_evaluation (D : Data.{u}) (U : Evaluations D)
    (sq : NormalSquare D) (hq : ∀ n : ℕ, IsIso (integration_n D sq n))
    (u : tate D ≅ normal D)
    (hu : ∀ n : ℕ,
      vTate D U n ≫ (ev D D.X n).map u.hom ≫ vNormal D U n =
        (nu D n D.X).map (integration_n D sq n)) :
    ∀ n : ℕ, (ev D D.X n).map u.inv =
      vNormal D U n ≫ (nu D n D.X).map (q_n D sq n (hq n)) ≫ vTate D U n := by
  intro n
  have := hq n
  have : IsIso (vTate D U n) := tate_word_isIso D U n D.d
  apply (cancel_epi ((ev D D.X n).map u.hom)).1
  apply (cancel_epi (vTate D U n)).1
  calc
    _ = vTate D U n := by
      rw [← Functor.map_comp, Iso.hom_inv_id, (ev D D.X n).map_id]
      exact Category.comp_id _
    _ = (nu D n D.X).map (integration_n D sq n) ≫
        (nu D n D.X).map (q_n D sq n (hq n)) ≫ vTate D U n := by
      simp only [q_n, ← Functor.map_comp_assoc, IsIso.hom_inv_id]
      rw [(nu D n D.X).map_id, Category.id_comp]
    _ = _ := by rw [← hu n]; simp only [Category.assoc]

/-- Finite evaluation of the actual tower diagonal/DNC/integration diagram.
The displayed laws characterize the tower maps against canonical finite constructions;
none of the finite beta, delta, q or v maps is caller-supplied.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md`, paragraph (1)
(blueprint: lem-pur-tower-diagonal-finite-evaluation).

Proof:
1. Use finite type over k for Noetherianity. Apply the finite-ring smooth-section
   geometry theorem to (p1,Delta); centred coordinates x_j=t*u_j give the actual
   extended-Rees fibres. Retain the homogeneous Rees and symmetric-algebra comparisons.
2. Tower gluing and exact evaluation put all four dualizing objects, their section
   pullbacks, and the Tate line in the same shift of actual tower sheaves. Full
   faithfulness of the single embedding makes component equality sufficient here.
3. Compare each evaluated representing pair with its finite pair preserving its
   counit; ordinary right-adjoint uniqueness and the normalized unit give vHom.
   Compactification exchange, its inverse and its exceptional mate evaluate to
   their finite words, separately for f and for both fibre squares of h.
4. Pull the diagonal exceptional mate back by Delta to obtain beta. Evaluate the
   word to obtain beta_n. The two fibre mates give theta and eta, with v_h included.
   Their finite components are the specified atOne and atZero section maps.
5. On centred charts identify the family and diagonal invariants with ordered Tate
   lines via the Kummer/projective-line counits. Normalize the coordinate comparison
   at one by its restriction and the theta mate, as actual tower isomorphisms.
6. Finite shifted-line normalized descent identifies all overlap maps with the
   unique normalized finite kappa. Equality of tower-sheaf maps glues kappa and its
   inverse. Specialization is s0, inverse pullback of kappa, then eta. Evaluation
   gives exactly delta_n, including both fibre comparisons and v_h.
7. Form the vector-bundle adjunct from ordered Kummer/projective-line integrations.
   The finite frame-adjoint theorem identifies its evaluations with integration_n.
   Frame invariance and equality of shifted tower-sheaf maps glue it before evaluation.
8. Invert this bundle orientation and pull back along z; the root-normalized Tate
   word gives q and its displayed equation. Joint conservativity makes all specified
   arrows invertible. The zero-fold tensor and empty affine iteration cover d=0;
   empty schemes give the unique equations, and n=0 means the first positive level.
-/
theorem tower_diagonal_finite_evaluation (D : Data.{u}) :
    ∃ U : Evaluations D, ∃ sq : NormalSquare D,
    ∃ hq : ∀ n : ℕ, IsIso (integration_n D sq n),
    ∃ finiteκ : ∀ n : ℕ, Kappa D n,
    ∃ β : omega D.ell (scalars D) D.b D.o D.coords D.towerF ≅ C D,
    ∃ κ : family D ≅ (inverseImage D (a D)).obj (C D),
    ∃ s₀ : C D ≅ (inverseImage D (i₀ D)).obj ((inverseImage D (a D)).obj (C D)),
    ∃ s₁ : C D ≅ (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).obj
      ((inverseImage D (a D)).obj (C D)),
    ∃ η : (inverseImage D (i₀ D)).obj (family D) ≅ normal D,
    ∃ θ : (inverseImage D (AffineSpace.oneSection (ULift.{u} (Fin 1)) D.X)).obj
      (family D) ≅ C D,
    ∃ q : normal D ≅ tate D, EvaluationLaws D U sq hq finiteκ β κ s₀ s₁ η θ q := by
  classical
  obtain ⟨sq, hq, _hβ, hκ⟩ := finite_foundations D
  choose finiteκ hfinite _hunique using hκ
  obtain ⟨U, β, κ, s₀, s₁, η, θ, laws⟩ := section_diagram D finiteκ hfinite
  obtain ⟨u, hu⟩ := integration_diagram D U sq
  refine ⟨U, sq, hq, finiteκ, β, κ, s₀, s₁, η, θ, u.symm, ?_⟩
  exact
    { finite_normalized := hfinite
      beta_evaluation := laws.beta_evaluation
      kappa_evaluation := laws.kappa_evaluation
      zero_section := laws.zero_section
      one_section := laws.one_section
      zero_fibre := laws.zero_fibre
      one_fibre := laws.one_fibre
      normalized_at_one := laws.normalized_at_one
      delta_evaluation := specialization_evaluation D U finiteκ κ s₀ η
        laws.kappa_evaluation laws.zero_section laws.zero_fibre
      q_evaluation := inverse_integration_evaluation D U sq hq u hu }

end AlgebraicGeometry.ProEtale.TowerDiagonalFiniteEvaluation

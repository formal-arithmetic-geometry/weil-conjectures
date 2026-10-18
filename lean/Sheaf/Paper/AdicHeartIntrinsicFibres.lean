/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.AdicHeartPullbackFibres
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.Paper.CoefficientHeartClosure
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.Paper.ContinuousAffineEtaleLattice
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralPullbackCompletedComparison
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.Paper.LisseIntegralSmallCoefficients
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcScalarExtension
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Adic coefficient fibres in the intrinsic coefficient presentation

Source: Bhatt--Scholze, Section 6.8, especially Propositions 6.8.4 and 6.8.14
(blueprint: lem-per-adic-heart-pullback-fibres).
The original module supplies the raw completed-coefficient statements unchanged.
The declarations below transport their actual section normalization to the intrinsic
rational and common-stage categories used by the constructible Weil heart.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ W)

/-- Completed geometric pullback, H⁰, point sections, then inversion of the uniformizer.
The coefficient-model equivalence is the published constant-section-normalized one.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicIntegralFiber : sfIntegralConstructibleCategory l E W ⥤ ModuleCat.{u + 1} E :=
  (sfIntegralConstructible l E W).ι ⋙ (purCoefficientModel l E W).inverse ⋙
    pbcActualCompletedPull x (pbcIntegralDatum l E) ⋙
    DerivedCategory.homologyFunctor _ 0 ⋙ PerAdic.pointSections l E Ω ⋙
    ModuleCat.extendScalars (PerAdic.integerToField l E)

/-- Unique descent of actual completed sections along raw rationalization.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: the coefficient-model equivalence identifies these sections with integralFiber
of the original module. Uniformizer multiplication becomes invertible over E.
The scalar-localization universal property gives the unique extension, including its
fraction maps; a fraction f/ϖⁿ acts as ϖ⁻ⁿ times the map of completed point sections. -/
theorem sfAdicRationalFiber_existsUnique :
    ∃! F : sfRationalConstructibleCategory l E W ⥤ ModuleCat.{u + 1} E,
      sfRationalConstructibleLocalization l E W ⋙ F = sfAdicIntegralFiber l E W x := by
  sorry

/-- The rational fibre fixed by its section and fraction normalization.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicRationalFiber : sfRationalConstructibleCategory l E W ⥤ ModuleCat.{u + 1} E :=
  (sfAdicRationalFiber_existsUnique l E W x).exists.choose

variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The actual inclusion of a finite coefficient field, with its canonical small model.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def sfAdicCoefficientEmbedding (L : Padic.FiniteCoefficientFields l Qbar) :
    AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L →+* Qbar :=
  L.val.subtype.comp (Shrink.algEquiv (Padic l) L.val).toRingHom

/-- Finite-stage normalization of an adic common-stage fibre. The comparisons are
natural in every rational arrow, including all fractions. Scalar extension is the
ordinary tensor extension along the actual finite-field inclusion.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def SfAdicCommonFiberSpec
    (F : generalAlgebraicallyClosedConstructibleCategory l Qbar W ⥤
      ModuleCat.{max (u + 1) v} Qbar) : Prop :=
  ∀ L : Padic.FiniteCoefficientFields l Qbar,
    Nonempty (GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙ F ≅
      sfAdicRationalFiber l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) W x ⋙
        ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Qbar L))

/-- The existing adic fibre also exists in the intrinsic common-stage presentation.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: the normalized coefficient-model equivalences identify the two integral
presentations, their quotient transitions, and completed point sections. Rationalize
these equivalences using their fraction formulas. Their scalar-tensor comparisons
satisfy the tensor associativity and identity equations, so descend through the
common-stage quotient. Transport the fibre in CommonFiberAssertions along this
comparison. Its finite-stage comparisons are exactly those displayed here. -/
theorem sfAdicCommonFiber_exists :
    ∃ F : generalAlgebraicallyClosedConstructibleCategory l Qbar W ⥤
      ModuleCat.{max (u + 1) v} Qbar, SfAdicCommonFiberSpec l W x Qbar F := by
  sorry


variable {k : Type u} [Field k] [Fact (IsUnit (l : k))]
open PerAdic

/-- All clauses of the recorded adic-heart theorem, with its intrinsic-presentation
coefficient fibres made available as well. The first twelve conjuncts retain the
original raw-category theorem verbatim; the last clause changes only presentation.
Source: BS 6.8.2--6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: construct the integral standard t-structure from good truncations and
cohomology, then rationalize its classes and truncations. Compute completed pullback
on flat representatives; its quotient reductions preserve constructibility and
bounds. Evaluate strict quotient fibres on common finite lisse stratifications and
take their inverse limits, then invert the uniformizer. Lisse representation fibres
are exact and detect zero; finite scalar tensor commutes with their inverse limits.
These comparisons descend to common stages, retaining scalar associativity, identity,
and pullback comparisons. Fibre rank is locally constant on each lisse stratum, so
the nonzero-fibre locus is constructible. These are precisely steps 1--10 of
adicHeartPullbackFibres in the imported module. Finally apply the normalized
coefficient-model equivalence, as in sfAdicRationalFiber_existsUnique and
sfAdicCommonFiber_exists, to express those same fibres in the intrinsic categories. -/
theorem sfAdicHeartPullbackFibres (L : Padic.FiniteCoefficientFields l Qbar)
    (V T : Base k) (h : V.scheme ⟶ T.scheme) :
    (∀ W : Base k, RationalStandardAssertions l (pbcFiniteField.{u} l Qbar L) W) ∧
    RationalPullAssertions l (pbcFiniteField.{u} l Qbar L) V T h ∧
    RationalFiberAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    RationalComparisonAssertions l (pbcFiniteField.{u} l Qbar L) V T h ∧
    RationalSupportAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    RationalLimitAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    ScalarAssertions (k := k) l Qbar ∧
    ScalarFiberAssertions (k := k) l Qbar ∧
    ScalarPullbackFiberAssertions l Qbar V T h ∧
    CommonStandardAssertions (k := k) l Qbar ∧
    CommonPullAssertions l Qbar V T h ∧
    CommonFiberAssertions l Qbar V T h ∧
    ∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ W.scheme),
      ∃ F : generalAlgebraicallyClosedConstructibleCategory l Qbar W.scheme ⥤
        ModuleCat.{max (u + 1) v} Qbar, SfAdicCommonFiberSpec l W.scheme x Qbar F := by
  sorry

end WeilConjectures

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.ConstructibleTruncations
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompactSupportReductionTower
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcCommonStageCones
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.PbcQbarCategory
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.RationalCompactSupportCoefficientCoherence
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.IntrinsicQbarCategory

/-! # Exactness and lower bounds for field-coefficient compact support

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7, Lemmas 6.1.11--6.1.13;
Stacks Project, Tag 0G2A, part (3)
(blueprint: lem-zl-field-shriek-lower-bound).

Both coefficient categories and all morphism actions are the recorded constructions.
The common-stage assertion applies to every normalized compact-support coefficient action.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

/-- Compact support is triangulated, with coherent natural comparisons for every integer
shift, and preserves every lower cohomological bound at both field-coefficient levels.
No separatedness of the structure morphisms is required.

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7, Lemmas 6.1.11--6.1.13;
Stacks Project, Tag 0G2A, part (3)
(blueprint: lem-zl-field-shriek-lower-bound).

Proof (the nine steps of the DAG):
1. Compose the exact coefficient-tower functor of
   lem-weil-compact-support-reduction-tower-functor with the exact strict-tower derived
   limit of lem-weil-pbc-ringed-strict-tower-homotopy-limit. Integral constructibility is
   lem-sf-integral-compact-support-constructible. A finite fibre-dimension bound exists
   by lem-fin-finite-type-fibre-dimension-bound and is unchanged by geometric base change
   by lem-sc-fibre-dimension-after-base-change. The finite functors have the uniform
   interval bound of prop-finite-compact-support-constructibility.
2. Derived completeness and the two-term quotient resolution identify this tower with
   completed Rp_* j_!: open extension commutes with the resolution and derived limits
   by det-sf-open-closed-extension-zero-limits, and proper image commutes with the limit
   by lem-pur-completed-coefficient-pushforward-comparison. The finite restriction maps
   agree by lem-weil-proetale-direct-image-restriction-of-scalars. Finite-type schemes
   over a field are Noetherian and finite-dimensional; the integral conventions agree
   by lem-weil-pbc-integral-stratified-perfect-characterization.
3. prop-weil-pbc-rational-transport rationalizes the exact integral functor and its
   shift comparisons. Its map on a fraction is precisely the recorded finite action.
4. lem-weil-finite-free-completed-scalar-comparison identifies the framework and PBC
   scalar transitions. Its unit, composition, associator and shift equations follow
   from lem-weil-scalar-extension-composition and prop-weil-pbc-scalar-extension.
   Common-stage arrows and cones give an exact equivalence of the two presentations.
   Apply lem-cbc-rational-compact-support-coefficient-coherence to the identity square,
   descend by prop-weil-pbc-descent-functors, and transport back. This is the normalized
   action with output pair (E,F_E K), including all morphisms and shift comparisons.
5. For an integral heart object H, a finite stratification gives finitely presented
   coefficient modules. Their torsion is killed by one common uniformizer power N:
   the valuation ring is a Noetherian DVR and torsion submodules are finitely generated.
   Flat completed coefficients identify the torsion kernels and quotients with these
   local models, so they too are constructible finite-coefficient sheaves.
6. The two-term resolution computes derived reduction of H in degrees -1 and 0.
   The quotient transition is multiplication by the uniformizer in degree -1 and
   identity in degree 0. The truncation triangle and the finite lower bound identify
   degree -1 of the output with H^0 of compact support of the torsion kernel.
   Restriction-of-scalars compatibility identifies its transitions; every N-fold
   transition is zero. This degree -1 tower is therefore pro-zero.
7. Apply the sheaf-valued Milnor sequence det-pe-milnor-sequence. Degrees below -1
   vanish because their adjacent finite cohomology towers vanish. Degree -1 vanishes
   because the preceding tower is zero and the degree -1 tower is pro-zero. Thus
   integral compact support sends heart objects into the nonnegative half.
8. prop-weil-localized-tstructure and the integral-category comparison identify every
   rational heart object with the localization of an integral heart object; t-exact
   rationalization gives the heart lower bound. prop-constructible-truncations makes
   a common-stage heart object isomorphic to the image of a finite-stage heart object,
   giving the same conclusion for the actual common-stage action.
9. Apply exact compact support to the bounded truncation triangles. The heart bound
   and the natural shift comparisons put each degree-q layer in degrees at least q.
   Starting below the first nonzero cohomology and inducting through the finite range,
   the long exact cohomology sequence of lem-weil-heart-short-exact-triangles gives
   the asserted lower bound for every bounded constructible complex. -/
theorem fieldShriek_lowerBound
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [QuasiSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [QuasiSeparated (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : Compactification f) :
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      (∃ comm : (sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) d
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).CommShift ℤ,
        (fun [commInst : (sfCompactSupportFiniteFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) d
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).CommShift ℤ] ↦
          (sfCompactSupportFiniteFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) d
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).IsTriangulated)
          (commInst := comm)) ∧
      ∀ (c : ℤ) (K : Stage l Ω X E),
        (∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfRationalStandardTStructure l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X D hl) i).obj K)) →
        ∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfRationalStandardTStructure l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y D hl) i).obj
              ((sfCompactSupportFiniteFunctor l D.k
                (PurCompactSupport.coefficientPrimeUnit l D hl) d
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj K))) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) Ω d,
      (∃ comm : S.system.functor.CommShift ℤ,
        (fun [commInst : S.system.functor.CommShift ℤ] ↦
          S.system.functor.IsTriangulated) (commInst := comm)) ∧
      ∀ (c : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω X),
        (∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfCommonStageStandardTStructure l X Ω D hl) i).obj K)) →
        ∀ i : ℤ, i < c → IsZero ((constructibleTruncationCohomology
          (sfCommonStageStandardTStructure l Y Ω D hl) i).obj
            (S.system.functor.obj K))) := by
  sorry

end WeilConjectures

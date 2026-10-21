/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.SfDerivedComplete
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.ConstructibleStandardTStructure
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import Sheaf.Paper.ScalarExtensionExactIntrinsic
import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.PbcScalarExtension
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Paper.PbcDescentFunctors

/-! # Truncations on the rational and common-stage constructible categories

Source: Weil blueprint, sec-poincare-duality/sk-lem-finite,
prop-constructible-truncations, main-20261015
(blueprint: prop-constructible-truncations).

The finite fields are the actual finite subextensions of the fixed closure, transported
by the recorded coefficient equivalences to the scheme universe. No t-structure on an
ambient category of rational sheaves is substituted for scalar localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

/-- The cohomology endofunctor specified by the proposition: truncate to degree i,
then shift by i. Its value is a degree-zero heart object.
Source: blueprint prop-constructible-truncations, cohomology display
(blueprint: prop-constructible-truncations). -/
def constructibleTruncationCohomology
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (i : ℤ) : C ⥤ C :=
  (t.truncLE i ⋙ t.truncGE i) ⋙ shiftFunctor C i

/-- The compatibility clause, including the characterizing counit and unit equations.
Uniqueness fixes the comparisons and hence their coherence with scalar tower associators.
This is a package of the proposition's clauses, not a new truncation construction.
Source: blueprint prop-constructible-truncations, scalar and automorphism paragraphs
(blueprint: prop-constructible-truncations). -/
def ConstructibleTruncationCompatibility
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B) (F : C ⥤ B) : Prop :=
  (∀ m : ℤ,
    (∃! α : t.truncLE m ⋙ F ≅ F ⋙ s.truncLE m,
      ∀ K : C, α.hom.app K ≫ (s.truncLEι m).app (F.obj K) =
        F.map ((t.truncLEι m).app K)) ∧
    (∃! α : t.truncGE m ⋙ F ≅ F ⋙ s.truncGE m,
      ∀ K : C, F.map ((t.truncGEπ m).app K) ≫ α.hom.app K =
        (s.truncGEπ m).app (F.obj K))) ∧
  ∀ i : ℤ, Nonempty (constructibleTruncationCohomology t i ⋙ F ≅
    F ⋙ constructibleTruncationCohomology s i)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y : Scheme.{u}) [base : Y.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage stageTransition inclusion)

/-- The complete collection of standard, bounded, scalar-compatible truncations and
scheme-automorphism comparisons on the categories in the proposition. Prime-invertibility
is a conclusion witness, not an added hypothesis on the finite-type scheme.
Source: blueprint prop-constructible-truncations, all clauses
(blueprint: prop-constructible-truncations). -/
def ConstructibleTruncations
    (t : ∀ E : Index l Ω, TStructure (Stage l Ω Y E))
    (s : TStructure (generalAlgebraicallyClosedConstructibleCategory l Ω Y))
    (units : ∀ y : Y, Invertible (l : Y.residueField y)) : Prop :=
  letI := units
  (∀ (E : Index l Ω) (n : ℤ),
    (t E).le n = sfRationalStandardClass l (Coefficient.{u} l Ω E) Y true n ∧
    (t E).ge n = sfRationalStandardClass l (Coefficient.{u} l Ω E) Y false n) ∧
  (∀ n : ℤ, s.le n = sfCommonStageStandardClass l Y Ω true n ∧
    s.ge n = sfCommonStageStandardClass l Y Ω false n) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω Y E), (t E).bounded K) ∧
  (∀ K, s.bounded K) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    ConstructibleTruncationCompatibility (t E) (t L) (stageTransition l Ω Y E L h)) ∧
  (∀ E : Index l Ω,
    ConstructibleTruncationCompatibility (t E) s
      (inclusion (l := l) (Ω := Ω) (Y := Y) E)) ∧
  (∀ (h : Y ≅ Y) (E : Index l Ω),
    ConstructibleTruncationCompatibility (t E) (t E)
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) h.hom)) ∧
  (∀ h : Y ≅ Y, ConstructibleTruncationCompatibility s s
    (commonStageDerivedPullback l Ω h.hom))

include D hl base hft hqc

/-- There are the standard truncations, their canonical maps and distinguished triangles,
bounded t-structures, cohomology functors, scalar-tower and automorphism comparisons.
Source: blueprint prop-constructible-truncations, main-20261015
(blueprint: prop-constructible-truncations).

Proof plan:
1. Finite type over D.k makes Y noetherian, quasi-compact and finite-dimensional;
   l differs from its residue characteristic and is therefore a unit at every point.
   Apply lem-weil-pbc-integral-stratified-perfect-characterization to identify the
   recorded integral category with the completed stratified-perfect convention.
2. Finite-torsion good truncations preserve constructible cohomology and boundedness.
   prop-weil-pbc-integral-tstructure gives the integral standard truncations and triangles.
3. prop-weil-localized-tstructure rationalizes these through the raw localization.
   lem-pod-texact-truncation-comparison identifies their canonical units and counits.
4. lem-weil-finite-free-completed-scalar-comparison makes finite scalar extension exact:
   after forgetting scalars it is a finite direct sum. Homology commutes with this
   exact functor; integral constructibility is preserved. Rationalization is t-exact.
   The comparison lemma gives unique truncation comparisons. Its composition and
   natural-transformation clauses give compatibility with the recorded scalar
   associators, units and pentagon (prop-weil-pbc-scalar-extension).
5. lem-sbc-coherent-pair-functor-descent descends both truncations, maps and triangles
   to the actual common-stage category. Its inclusion comparisons express agreement
   with every finite presentation. At a common field orthogonality holds; directed
   Hom colimits preserve it. Shift inclusions and finite-stage bounds give boundedness.
6. Compose the two truncations and the i-shift to define the displayed cohomology.
   It lies in the heart, and integral/torsion representatives give ordinary cohomology.
7. lem-weil-isomorphism-derived-pullback identifies actual completed pullback along h
   with the termwise exact inverse image equivalence. It preserves both integral
   halves. prop-weil-pbc-rational-transport gives the actual rational triangulated
   pullback, t-exact by its integral representatives. Apply the comparison lemma.
8. lem-pur-integral-operations-scalar-extension and
   lem-pur-semilinear-scalar-localization give the scalar-compatible rational pullback
   comparisons. The natural-transformation and composition clauses of the comparison
   lemma make the finite-stage truncation comparisons compatible with these maps.
   Coherent pair-functor descent gives the common-stage automorphism comparisons.
9. prop-weil-pbc-descent-functors supplies shift compatibility of the actual descended
   pullback. Compose it with the two truncation comparisons to obtain cohomology
   compatibility at both field levels. -/
theorem constructibleTruncations_exists :
    ∃ (t : ∀ E : Index l Ω, TStructure (Stage l Ω Y E))
      (s : TStructure (generalAlgebraicallyClosedConstructibleCategory l Ω Y))
      (units : ∀ y : Y, Invertible (l : Y.residueField y)),
      ConstructibleTruncations l Y Ω t s units := by
  sorry

end WeilConjectures

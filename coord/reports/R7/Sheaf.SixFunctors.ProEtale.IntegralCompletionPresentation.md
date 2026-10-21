## What changed

Replaced both sorry proofs in Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation
by complete Lean arguments from two separate coefficient lemmas. Existing declaration
signatures, definitions and public imports are unchanged. No adopted source module changed.

The generic mateComparison_existsUnique proves existence and unit uniqueness of the finite
derived comparison across equivalences. finiteComparison_existsUnique specializes it to the
actual scalar adjunctions. completedProducts constructs exact countable products on the
completed module side and obtains derived products from the existing theorem.
internal_roos_complete uses AdicCompletion.roos_isDerivedLimit and transports its strict
augmentation triangle to K. map_roos_complete proves the cross-category triangle transport,
including projection equations for its first map and for one minus the tower shift.
The final theorem applies these arguments and sfDerivedComplete_iff_legacy.

Added two modules, each with one public theorem, for ordinary normalized coefficient squares
and quotient-transition compatibility. They state different, strictly smaller parts of the
existing proof plan. Neither asserts the completeness conclusion or merely renames an original
statement. Their statements compile. Both original proofs combine these results with the
proved mate and triangle arguments; the original theorem statements are preserved.

Validation: all three modules compiled together remotely in import order. The final
compile after pruning imports succeeded for both new modules (1.4 and 1.3 seconds) and the
original module (24.6 seconds), with no warnings. No full library build was run. After removing an unnecessary namespace open flagged by preflight, the item compiled
again in 16.4 seconds with no warnings. The normal delivery checks remain required.

## Proved and sorry left

This is a decomposition, not a net proof gain. Original holes closed: 2. New holes added: 2.
There are zero sorry bodies in the original item module and two in the delivery as a whole.

Closed original holes:
- AlgebraicGeometry.ProEtale.IntegralPresentation.integral_completion_reduction_comparisons.
- AlgebraicGeometry.ProEtale.IntegralPresentation.integral_completion_presentation.

Remaining holes, each the entire proof of a public theorem in its own module:
- AlgebraicGeometry.ProEtale.IntegralPresentation.integral_completion_normalized_squares,
  node lem-pe-integral-normalized-restriction-squares, module
  Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares.
- AlgebraicGeometry.ProEtale.IntegralPresentation.integral_completion_transition_comparison,
  node lem-pe-integral-reduction-transition-comparison, module
  Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison.

No definition contains sorry, no arbitrary data construction was introduced, and no new
axiom, unsafe declaration or opaque declaration was added. The pre-existing
AdicCompletion.roos_isDerivedLimit is used as its declared dependency; this delivery does not
claim to prove that imported theorem or to eliminate all transitive axioms.

The first remaining result constructs the projection-normalized ordinary section-action
squares; it needs the integral-limit coefficient theorem and finite-discrete encodings. The
second asserts only the transition equation for supplied normalized squares and unit-normalized
finite derived comparisons. It needs the pure-tensor quotient computation. The actual
construction and uniqueness of those derived comparisons is proved in the original module.
The completeness triangle is also proved there, from the existing strict internal Roos theorem.

## No longer needed

Removed these direct proof imports:
- Sheaf.CategoryTheory.StrictRoosComparison.
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel.
- Sheaf.Paper.IntegralReductionTowerCanonical.
- Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted.
- Sheaf.CategoryTheory.SheafTensorStructure.
- Sheaf.CategoryTheory.SheafTensor.

The original module no longer repeats K-flat tensor construction, strict Roos comparison,
or the legacy augmented-resolution calculation. It uses the declared internal
roos_isDerivedLimit and the proved sfDerivedComplete_iff_legacy instead.
Accordingly its direct proof route no longer cites lem-pc-kflat-resolution,
def-pc-kflat-complex, def-pur-sheaf-tensor-product, lem-pur-derived-change-of-rings,
lem-weil-strict-roos-comparison, lem-weil-integral-reduction-tower-well-defined,
det-def-sfb-sheaf-tensor-structure, sk-def-sfb-sheaf-tensor or
lem-pe-internal-section-tensor-comparison. Several remain transitive dependencies of the
internal Roos theorem or of the two coefficient lemmas: no global pruning or withdrawal of
those modules is claimed. The parent node also drops its obsolete direct tool approvals for
lem-pc-kflat-resolution, lem-pur-derived-change-of-rings, lem-weil-strict-roos-comparison,
lem-weil-integral-reduction-tower-well-defined and
lem-pe-internal-section-tensor-comparison; their remaining transitive uses stay in the DAG.
No module or DAG node was deleted; none is established globally
unnecessary by this packet. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The existing plan combines two different coefficient
calculations with a general categorical argument. The declared library already provides
AdicCompletion.roos_isDerivedLimit, including its crucial fixed-augmentation equation, and a
proved legacy comparison. Reusing them avoids duplicating their resolution and cone arguments.

The remote compile server intermittently returned exit 124 (busy). Retrying produced actual
compiler diagnostics and successful compiles. These were not treated as mathematical blockers.
Elaboration initially unfolded the large scalar constructions; explicit types for localized
squares and local irreducibility of existing scalar-existence witnesses resolved that issue.
No compile limit, launcher script, repository tool or budget metadata was changed.

## New nodes

lem-pe-integral-normalized-restriction-squares realizes the ordinary coefficient portion of
the parent's first proof step. Its conclusion is existence of concrete section-action
encodings with identity-on-abelian-sheaf restriction squares, with no derived comparisons,
transition equations or completeness assertion. Its new module is
Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares.

lem-pe-integral-reduction-transition-comparison realizes the parent's fourth proof step.
For supplied normalized squares and unit-normalized finite derived comparisons it asserts
only the equation for the actual consecutive quotient transitions. Its new module is
Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison. The localized restriction
square and restricted comparison in its statement are exactly the existing formulas;
explicit return types keep them elaboratable without changing their mathematical content.

Both nodes carry complete proofs in words, sources, Mathlib searches, the existing chapter
and unit, and Lean signatures. Edge cases checked: n=0 means exponent 1; zero modules and
complexes, the empty site and arbitrary unbounded complexes obey the same tensor and
identity-map equations. No boundedness, constructibility or Noetherian hypothesis is added.
No change record is needed because no existing statement or definition changed.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

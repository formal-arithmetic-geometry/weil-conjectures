## What changed

Replaced the body of `WeilConjectures.sfCompactSupportTower_presentation` by a complete
categorical assembly proof. Its signature and three public imports are unchanged.
The private `towerIsoOfSteps` constructs a natural transformation using
`NatTrans.ofOpSequence` and proves that it is invertible from its components.
The ordinary-image level comparisons are identities; the underlying finite direct-image
functors are definitionally equal. Support level comparisons are actual `mapIso`
constructions: exact localization of the supplied ordinary open comparison, followed
by finite right-derived direct image and completed coefficient restriction.

Added three modules, each with one remaining named theorem:
`SfFiniteOpenPresentation`, `SfDirectImageTransitionPresentation`, and
`SfSupportTransitionPresentation`. The finite module also proves that the slice
adjacent restriction is the specified finite quotient restriction. Exactness and
additivity needed to localize the finite comparison are transported along that
comparison locally in the new support-level definition; no shared instance changes.
No existing module other than the item is changed, and no change record is needed.

Validation: all four delivered Lean modules compiled through `lcompile.py`. The
final item compiled in 2.2 seconds; the support construction compiled in 3.6 seconds.
The finite-open and direct-image modules also passed the 60-second per-file limit.
The item retains its original theorem signature and all original public imports.

The split statements are separate steps of the original argument, rather than another
existence assertion about the two towers. The first is an ordinary module-functor
coefficient square, the second an explicit ordinary-image adjacent-arrow identity
without an open immersion or completeness assumption, and the third a support
adjacent-arrow identity conditional on the ordinary coefficient square. The original
module constructs both whole inverse-system isomorphisms from these steps.

## Proved and sorry left

One original hole is removed: `WeilConjectures.sfCompactSupportTower_presentation`
(node `lem-sf-compact-support-slice-intrinsic-towers`). Its proof from the three
statements below is complete. This is a decomposition, not a closed mathematical
proof: one upper hole closed and three lower holes added, for net minus two holes.
There are zero sorries in the item module and three in the new modules.

The three sorries left are exactly:

- `WeilConjectures.sfFiniteOpenPresentation`, node
  `lem-sf-finite-open-presentation-coefficients`.
- `WeilConjectures.sfDirectImageTransition_presentation`, node
  `lem-sf-direct-image-adjacent-presentation`.
- `WeilConjectures.sfSupportTransition_presentation`, node
  `lem-sf-support-adjacent-presentation`.

Additionally proved without new holes:
`WeilConjectures.sfFiniteOpenPresentation_restriction_eq` and
`WeilConjectures.sfFiniteDirectImage_presentation`. The restriction comparison and
support-level isomorphisms are real constructions with no choice of data from an
unproved existence theorem. Each remaining theorem has its source and proof in words
in its docstring and matching node. Empty and identity opens, the first coefficient
index n=0, arbitrary unbounded K, and K=0 were checked against the formulas; none
requires a missing nonemptiness, boundedness, flatness or finite-field hypothesis.

## No longer needed

No original public import was removed. There is no global module or node pruning:
the old proof dependencies remain needed under the three new nodes. At the item
node itself they are replaced by those nodes and `def-weil-inverse-system`.
The adopted source tree is untouched.

The support-level construction does not need an additional direct import of
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`: transport of
additivity and exactness along the supplied finite comparison suffices.
This does not declare that existing exactness module globally unused.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies supply the sites, adjunctions, operations and normalized
squares, but none of the inspected declarations directly identifies the slice finite open functor with
the realization-based intrinsic open functor or supplies the two specified adjacent
arrow equalities. Those are the precise missing glue isolated here from original
Steps 1, 3--5. The inverse-system assembly of original Step 6 is now proved in Lean. `integralProperTowerTransition` and
`proper_system_evaluation_transitions` compare other system evaluations and require
a finite-field datum, so they do not supply the arbitrary-scheme identity here.
`sfDirectImageReductionComparison_transition` concerns Roos projection adjuncts and
also has a different conclusion. None is imported as an unnecessary dependency.

The finite direct-image comparison of original Step 2 is shorter than its plan:
both functors use the identical sheafification transpose of the constant-section map,
so their equality is `rfl`. No statement is disputed or weakened. The unit's realized
statement and proof steps are untouched. No forced adaptation is needed.

## New nodes

`lem-sf-finite-open-presentation-coefficients` records the ordinary open natural
isomorphisms and their adjacent coefficient square, including the proved quotient
restriction identification and its explicit identity-presentation isomorphism.
Its module has no proper map or derived tower comparison in its conclusion.

`lem-sf-direct-image-adjacent-presentation` records an equality of the specified
adjacent direct-image arrows for an arbitrary completed-coefficient complex, with
no open immersion, compactification or completeness hypothesis. It also records
the proved definitional equality of the ordinary finite direct-image functors.

`lem-sf-support-adjacent-presentation` records the constructed support level
comparison and one adjacent-square identity, assuming the ordinary coefficient
square of the first node. It contains no tower-isomorphism existence assertion.
All three inherit the original chapter and unit, have source proof steps and recorded
Mathlib searches, and become proof dependencies of the item.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

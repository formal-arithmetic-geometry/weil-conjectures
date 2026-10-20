## What changed

Proved `AlgebraicGeometry.Scheme.completeProetale_isIso` without changing its
signature. The proof transports the finite etale-origin witnesses, applies
four-tower compatibility and finite-level proper base change, detects the tower
isomorphism through evaluated cohomology, and applies the completed exchange
construction.

Also proved `AlgebraicGeometry.Scheme.pbcIntrinsicComplete_towerComplete` in the
new module `Sheaf.Paper.PbcIntrinsicTowerComplete`. This specializes existing
unit-normalized strict/intrinsic completed-pullback and identity comparisons,
then cancels the invertible constant-tower unit. Its categorical helpers prove
full faithfulness of derived constant towers via evaluation at zero and identify
identity tower pullback. The target uses this result to pass from its intrinsic
completeness hypothesis to the quotient-tower predicate.

## Proved and sorry left

Closed the item's one original hole: `completeProetale_isIso` (1 of 1).
Added zero holes. The new `pbcIntrinsicComplete_towerComplete` and all private
helpers are proved. Neither delivered Lean module contains `sorry`.
The proofs use the project's existing named dependencies, some still unproved;
this is a proof from those declarations, not an assertion that the whole
transitive dependency closure is already free of axioms.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.AdicCoefficientDatum`,
`Sheaf.Paper.FiniteLevelProEtaleBaseChange`,
`Sheaf.Paper.CompletedExchangeCoherence`, `Sheaf.Paper.FourArrows`,
`Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones`,
`Sheaf.Paper.CompletedDirectImageLimits`, and
`Sheaf.Paper.CompletedMapReduction`.

The target proof does not use the separate cone criterion
`lem-weil-pbc-levelwise-isomorphism-cones`, the separate completed-map-reduction
node `lemma-weil-pbc-completed-map-reduction`, or the supplementary coherence
node `lemma-weil-pbc-completed-exchange-coherence`. Pointwise derived homology
and exact evaluation replace the cone criterion; four-tower compatibility
provides the required evaluation equation directly. Finite-level proper base
change and direct-image-limit comparison remain transitive dependencies of the
retained constructions. No whole-library module is claimed unreachable.

The new completeness lemma does not directly use
`prop-weil-pbc-koszul-reconstruction`,
`lem-weil-pbc-constant-completion-equivalence`, or
`def-weil-pbc-intrinsic-completion` from its earlier proposed route. The existing
strict/intrinsic completed-pullback comparison supplies the normalized comparison
needed here, and specialization to identity closes the implication categorically.
These nodes may remain transitive prerequisites of that existing comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan treated intrinsic completeness and quotient-tower completeness
as interchangeable without an explicit passage between their different
presentations and units. The new proved lemma supplies that passage. The earlier
sandbox attempt left it as a new hole; this delivery closes it using the existing
normalized completed-pullback comparison instead of rebuilding coefficient
completion theory. The target statement and the unit's finite-level route stay
unchanged.

## New nodes

`lem-weil-pbc-intrinsic-to-tower-complete`, realized by the proved theorem
`pbcIntrinsicComplete_towerComplete` in
`lean/Sheaf/Paper/PbcIntrinsicTowerComplete.lean`, records the identity-pullback
comparison argument and its derived constant-tower adjunction step.

Validation: both delivered modules compile through `lcompile.py --all` with no
warnings. No existing public signature or public import changes; no consumer
adaptation is needed. The comparison is valid for the empty scheme, the zero
complex and the zero ideal: the argument only uses identity coherence and
adjunction units and never selects a nonzero generator or a geometric point.

Change record: `coord/changes/complete-proetale-scoped-proof-context.md`
records the conservatively classified scoped elaboration options and namespace
opening and audits 177 transitive consumers; none is adapted.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

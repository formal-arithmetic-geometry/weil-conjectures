## What changed

Replaced the hole in `WeilConjectures.qcqsCompactSupport_strictReductionData`
by the ordered paste of the native strict proper-image comparison after completed
open extension and native proper image of the strict open comparison. The Lean
proof computes the finite evaluation of that actual paste, uses naturality of
proper evaluation, cancels the middle coefficient coordinates, applies the proved
`PurCompactSupport.comparison_factorization`, and transports through the existing
finite presentation isomorphisms. The private proved `changeCoordinates_comp`
records that last cancellation for arbitrary functors and isomorphisms.

Added `Sheaf.Paper.StrictCoefficientProperReduction` and
`Sheaf.Paper.StrictCoefficientOpenReduction`. Each constructs its evaluation
isomorphism concretely from native geometric evaluation and the existing finite
ringed/intrinsic presentation comparisons, then states the single geometric
factor and its finite normalization. These are separate proper and open factors,
with no compactification or compact-support composite. They do not restate the
item, and the Lean paste between them is substantive.

The existing item's statement, public imports and definitions are unchanged.
The delivery also refines three existing DAG records and adds two lower interface
nodes for already-proved geometric definitions and finite-coordinate helpers. These
metadata changes are recorded in
`coord/changes/strict-coefficient-geometric-dag-interfaces.md`. No other existing
Lean source changes, and no consumer interfaces need adaptation. Local transparency attributes only help
the proof compare the two standard derived-category presentations; they do not
change imported definitions or their interfaces. The geometric section hypotheses
are deliberately retained even though the factorwise map construction does not
need them; the unused-section-variable linter is scoped off for this theorem to
preserve its existing interface.

Validation: both new modules compiled without warnings. The complete item proof
compiled in the profiling run in 46.5 seconds after local unfolding controls were
added, within the unchanged 60-second limit. Profiling options were removed for
delivery; the delivery tool performs the final compile and axiom checks.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.qcqsCompactSupport_strictReductionData`
(node `lem-qcqs-compact-support-strict-reduction-data`) by reduction to two strictly
smaller geometric factors. This is a decomposition, not a net hole reduction:
one original hole closed, two new holes added, net minus one.

The two holes left are:

- `WeilConjectures.strictCoefficientProperReduction`
  (`lem-strict-coefficient-proper-reduction`): the native proper-image scalar mate
  and its evaluation on arbitrary ambient inputs.
- `WeilConjectures.strictCoefficientOpenReduction`
  (`lem-strict-coefficient-open-reduction`): the strict open tensor comparison and
  its finite open-adjunction normalization on arbitrary ambient inputs.

Both holes are the entire proofs of named public theorems. Neither is data in a
definition. Both theorem docstrings give the construction and normalization
argument, including identity morphisms, empty schemes, zero input and exponent
one. The proper comparison only asserts a map; no general proper base-change
isomorphism for arbitrary inputs is smuggled into that statement. The open
construction is exact tensor/extension by zero and needs no completeness
hypothesis. The item contains no remaining hole.

## No longer needed

No existing public import or module is removed or withdrawn. The original module
already publicly exposes the coefficient comparison, evaluation calculus and
native evaluation, and these remain needed by its unchanged statement.

The proof does not use `lem-sf-integral-open-reduction-comparison` or its module
`Sheaf.SixFunctors.IntegralOpenReductionComparison`: its exported strict comparison
is restricted to complete objects and uses another slice presentation. It does
not provide the map required here on every ambient derived input.

The proof does not use `prop-weil-pbc-direct-image-limits` or
`Sheaf.Paper.CompletedDirectImageLimits`: the item has no total-limit conclusion,
and its native varying-coefficient proper factor is handled before a limit.

The proof does not use `lem-weil-compact-support-reduction-tower-functor` or its
`exists_compactSupportReductionTower` theorem. That theorem constructs a functor
to completed-module towers; it does not give this map to the native ringed
sequence system. Its module remains a transitive public import of existing
coefficient definitions, so this delivery does not claim to prune it from the
targets' Lean import closure. The corresponding unused planned edges were removed
from the item's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The old node's one construction step cited three interfaces that do not furnish
the claimed strict comparison in its present form: the open result is restricted
to complete inputs, the direct-image result concerns completed-module towers and
limits, and the reduction-tower existence result supplies no comparison from the
completed ambient proper/open value. The replacement isolates exactly the open
and proper native-system comparisons still needed and writes their paste in Lean.
The source blueprint's Isomorphism paragraph does explicitly factor compact
support into these two geometric comparisons; its route is retained. The unit
`sk-def-sf-operations` has no realized statement or proof step bypassed here.

## New nodes

`lem-strict-coefficient-proper-reduction`, in
`Sheaf.Paper.StrictCoefficientProperReduction`, isolates just the direct-image
mate, before any compactification or open extension, with exact finite scalar
coordinates. Its construction comes from tensor/pullback and the geometric
adjunctions; evaluation is compared by pasting adjunction squares.

`lem-strict-coefficient-open-reduction`, in
`Sheaf.Paper.StrictCoefficientOpenReduction`, isolates just extension by zero on
whole quotient diagrams, without proper image or total limits. Its ordinary
comparison is the identity on the appropriate tensor generators in each open
extension summand; quotient compatibility precedes localization.

Both nodes record actual LeanSearch, LeanFinder, Loogle and Mathlib grep searches. Their dependencies include the lower geometric interface nodes below, the native
evaluation, K-flat descent, and ring-change adjunctions. The complete dependency
graph was checked for paths back to the item after refining the broad owners.
The whole current blueprint was searched for the combined and separate strict
coefficient comparisons; no matching node was found. Existing complete-input
open reduction and completed-module tower interfaces were read and kept distinct.
The metadata-only change record is
`coord/changes/strict-coefficient-geometric-dag-interfaces.md`. No existing shared
Lean signature or definition changes.

`def-strict-coefficient-ringed-geometric-data` reattaches the already-constructed
completed/finite ringed coefficient families and ordinary proper/open operations.
It separates those elementary definitions from the later realization theorem.

`lem-strict-coefficient-finite-geometric-coordinates` reattaches the existing proved
proper/open factorization and finite presentation helpers. It is a DAG interface
refinement, with no new Lean theorem or hole. The native evaluation node now cites
the actual finite ordinary operations used in its proof.

The first pushed packet `4805be2ab4e` had incomplete new-node dependency lists.
This packet supersedes those lists and records the actual lower interfaces rather
than omitting dependencies to pass the cycle gate.

## Statement corrected

The native-evaluation node has the same mathematical statement and unchanged Lean
construction. Its old reference to the later compact-support realization is expanded
as the finite functor `Rp_* j_!`, with direct references to finite ordinary geometric
operations. Its `statement_change` record preserves the old text and audits all
20 current DAG citers as holding: every one still receives exactly
the same specified evaluation isomorphism.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## What changed

Replaced the single sorry in `WeilConjectures.CompletedQuotient.completedComparisonScalarLimitImage`
by a complete assembly argument. Private helpers prove ScalarGenerated closure, normalized tensor,
pullback and scalar preservation, goodness of the scalar expression trees, and invertibility of
scalarSubstitution and scalarBeta. These use the existing normalized reconstruction, strict K-flat
system, and primitive scalar model existence results. The original theorem signature and public
imports are unchanged. Seven private proof imports were added. No existing Lean module besides the
assigned item was changed. The proof-dependency record of
`stage3-pur-normalized-scalar-tower-comparisons` is also repaired to match its existing private
import of the self-contained integral constructor.

Two new modules isolate the uncancelled canonical beta comparison and the strict scalar square
with its two uncancelled coordinates. The main proof chooses the normalized models, supplies all
goodness and invertibility witnesses itself, then postcomposes those equations with the inverse
L target substitution. Equality of the strict routes supplies both coordinates for either route.
This is a decomposition, not a complete proof of the original obligation without new holes.

## Proved and sorry left

The original hole in
`WeilConjectures.CompletedQuotient.completedComparisonScalarLimitImage` is replaced by a Lean proof
from the two new statements. The item's actual remaining hole count is zero. The private closure,
normalization, invertibility and categorical assembly helpers contain no sorry.

Added holes, each exactly `:= by sorry` in a separate module:

- `WeilConjectures.CompletedQuotient.completedScalarBetaComparison`, node
  `lem-pur-completed-scalar-beta-comparison`.
- `WeilConjectures.CompletedQuotient.completedScalarRouteCoordinates`, node
  `lem-pur-completed-scalar-route-coordinates`.

Accounting: one upper hole closed, two lower holes added; net minus one. This is one decomposition,
zero original holes completely discharged without new obligations, and two split-off statements.
Neither statement asserts generated closure, existence of models or invertibility of scalarBeta.
The beta statement does not assert scalar compatibility; the coordinate statement does not
identify the L comparison with the canonical comparison. Thus neither repackages the original
conclusion. The new docstrings give the complete intended arguments. Zero inputs, identity
coefficients, identity morphisms, empty schemes and ramified extensions were checked against the
formulas: only whole-system naturality and normalized counit equations are used, without finite
coefficient-map flatness or detection of derived maps by evaluations.

## No longer needed

No original Lean import was removed and no module is withdrawn. The old proof dependency
`lem-pur-normalized-scalar-comparison-realization` is no longer needed by this node: its claimed
closure and model assertions are proved using the existing more precise normalization and
existence declarations. Its Lean module is absent from the shared snapshot. This delivery does
not remove its node or attachment or assert that other parents no longer need it.

The strict coefficient calculus remains relevant to the new coordinate lemma. The unit route
is preserved; no blueprint unit statement or realized step is bypassed. No global pruning claimed.

## Where the brief, the DAG or earlier work was wrong

The original node's broad normalized scalar comparison dependency names a module absent from
this snapshot. Existing quotient-model, normalized operation-model and scalar tower declarations
suffice for its closure and invertibility portions, so these are used directly. The remaining
canonical-comparison and coordinate arguments require connecting the transported cochain
comparison and recursive substitutions to the existing whole-system normalization squares;
Functor.map_comp alone does not prove them. The explicit smaller statements record those steps.
No existing mathematical statement or definition was changed.

The first delivery preflight exposed a second, stale dependency: the normalized scalar tower
comparison construction cited the broad completed-comparison node, although its Lean source
already privately imports only CompletedPullbackTensorIntegralConstruction for the proved
sequence-ring equality. Its proof/proof_deps/proof_origin records now cite that actual constructor
node. This is a route-record correction, with no change to its Lean declarations or signatures;
it removes the artificial back edge through the theorem currently being proved.

The route-coordinate proof cites the strict coefficient calculus directly, not the much broader
scalar-extension-tower coherence node. The latter has an existing DAG path back through the
completed comparison construction. Using its direct strict calculus and limit-square constituents
avoids introducing that circular proof dependency.

## New nodes

`lem-pur-completed-scalar-beta-comparison` records the uncancelled naturality equation between
recursive scalar quotient substitutions and the canonical completed comparison. Its proof uses
the descended K-flat system comparison normalization and primitive coherent-counit realizations.

`lem-pur-completed-scalar-route-coordinates` records equality of the strict scalar routes and their
two uncancelled completed coordinates. Its proof uses the strict coefficient square and the
existing scalar pullback and tensor limit squares. The two coordinate equations are grouped
because they are the two factorizations of that one strict square, and neither assumes the L
canonical comparison identification.

The blueprint was searched for scalar and pullback/tensor comparisons; these are refinements of
the existing integral comparison proof, not duplicate blueprint assertions. The local proof-transparency
commands are recorded in `coord/changes/H9-completed-scalar-limit-proof-setup.md`; no existing
statement, definition or public interface changes.

The existing-node dependency correction is documented in
`coord/changes/H9-normalized-scalar-dependency-record.md`.

A further citation correction in `def-pod-scalar-completion-tensor-comparisons` replaces only
its completed tensor source reference by `def-pur-integral-derived-operations`. Its maps and
all other statement text stay the same. The broad comparison citation was not the definition
of completed tensor and caused another artificial cycle via the existing right Roos
normalization. The node has a complete statement_change and all direct citers remain valid.
See `coord/changes/H9-scalar-completion-operation-citation.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CompletedComparisonScalarLimitImage": "0702f6a2f6661cb6a9c30768573c3ff0dd7fc862", "Sheaf.Paper.CompletedScalarBetaComparison": "461f26d2fd7e85a9462c24986e39034146fbdc1f", "Sheaf.Paper.CompletedScalarRouteCoordinates": "fe7a1384804771a2172c59347ee5c07894e89454"}, "results": {"Sheaf.Paper.CompletedComparisonQuotientRealization": {"hash": "796a7c0f0e18a4d00281d562698c417dac1b4495", "status": "OK"}, "Sheaf.Paper.CompletedPullbackTensorConstruction": {"hash": "dc3286b509deff76144acaecf65578a6dbd24008", "status": "OK"}}, "seconds": 82, "time": "2026-10-28T15:42:04+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

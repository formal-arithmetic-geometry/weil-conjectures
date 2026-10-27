## What changed

Replaced the hole in `WeilConjectures.integralProjection_reduction_coordinates` by a
categorical diagram calculation. The statement and its public import are unchanged.
The proof imports the existing whole-system normalization and realization modules,
and two new intermediate theorems. Tensor naturality is proved from naturality on
the product category. The compactification square follows by evaluating the existing
whole-system square, using the three evaluation equations, naturality of the quotient
comparison, and faithfulness of the full finite inclusion. The proper square follows
from the analogous system square and an explicit cancellation of proper-identity
conjugations, using the coefficient datum's `properIdentity` equation.

Added `IntegralProjectionFiniteEvaluationData`, containing explicit endpoint
abbreviations, a natural-isomorphism type, its component family, and the actual proper
map conjugated into support coordinates. No data is chosen from a holed theorem in
any definition. Existential witnesses are used only locally inside the theorem proof.

Added `IntegralProjectionFiniteEvaluation` and
`IntegralProperProjectionSystemNormalization`, with the missing geometric calculations
as named public theorems. Updated the item's node to describe the combining proof.
No existing module or node outside the assigned item was changed. The local proof
attribute commands are documented in
`coord/changes/C7-integral-projection-local-proof-attributes.md`; they do not propagate
to importers. The static scanner's advisory treats these commands as interface text.

Validation: all four files compiled through `lcompile.py`; the final item compiled in
16.1 seconds. Profiling options have been removed. The larger heartbeat budget is local
to the theorem and documents the cost of checking the normalized operation types.
The unchanged direct consumer `IntegralStageProjectionStructuralIdentities` also
compiled against the new item. Its temporary source copy was removed before delivery.

Delivery preflight passed twice after the metadata correction. Both pushes were
rejected by the remote Git server with `remote unpack failed: unable to create temporary
object directory` (`unpacker error`). No delivery was pushed. The completed packet is
retained in this sandbox for retry with `deliver3.py C7
Sheaf.Paper.IntegralProjectionReductionCoordinates` after the remote failure is repaired.

## Proved and sorry left

Closed the original body hole of
`WeilConjectures.integralProjection_reduction_coordinates` (one of one original holes).
Its combining proof has no `sorry`. The two private diagram lemmas are proved.

Added two holes:

- `WeilConjectures.IntegralProjectionReduction.integralProjectionFiniteEvaluation`
  (`lem-sf-integral-projection-finite-evaluation`). It evaluates the two fixed endpoint
  maps and the system projection, and never mentions the integral projection map.
- `WeilConjectures.IntegralProjectionReduction.integralProperProjectionSystemNormalization`
  (`lem-sf-integral-proper-projection-system-normalization`). It normalizes the proper
  counit on whole coefficient systems, with no finite tensor comparison or finite
  projection in its statement.

This is a decomposition, not an axiom-free proof: one upper hole closed and two lower
holes added. The already existing hole in
`FixProjectionCompactification.integralProjectionReductionNormalization` is reused
without modification. All three geometric obligations are needed by the combining
proof; neither new obligation is the original statement with renamed hypotheses.

## No longer needed

No existing import was removed and no module is withdrawn. The original node's direct
uses of `lem-pur-normalized-integral-tensor-tower`, `def-fix-six-functor-datum`,
`def-sf-constructible-projection-mates`, and `lem-sf-projection-scalar-square` are replaced
by the more precise evaluation/system-normalization dependencies. The tensor-tower
and scalar-square inputs remain below the new evaluation obligation; this delivery
makes no claim that their modules are globally pruned. The datum and projection-mate
definitions remain available through the original public statement dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier plan did not expose the distinction between evaluating the system tensor
and reaching the datum's mixed finite partial tensor. It also did not state the
endpoint equations relating the explicit whole-system support adjunct to the supplied
finite support comparison. These are mathematical comparisons, not definitional
identities. The new evaluation theorem isolates them. The proper counit uses the direct
comparison, so the proof explicitly checks its two changes of coordinates rather than
assuming a compactification/proper coincidence law from a consumer of this item.

The latest blueprint's unit route is retained: these are the successive coefficient
reduction and proper-counit steps of the same projection map. No target signature,
existing definition, universe, or geometric hypothesis was changed. Edge cases of the
new statements include m = 0, zero inputs, identity opens and empty opens; no additional
separatedness assumption is imposed on the structure maps of X or Y.

## New nodes

`def-sf-integral-projection-finite-evaluation-data` records the explicit functors,
endpoints and proper conjugate in `IntegralProjectionFiniteEvaluationData`. Its
construction uses only given maps and the recorded quotient comparison.

`lem-sf-integral-projection-finite-evaluation` records the common tensor comparison and
three evaluation identities. Its proof instructions specify strict quotient tensor
models, the support/reconstruction triangle, and proper/open evaluation before pasting.

`lem-sf-integral-proper-projection-system-normalization` records the proper counit
square before evaluation. Its proof instructions specify the adjunction transpose and
the identity-open reconstruction cancellation. The local proof attributes have no effect on the public signature or imports. Blueprint search for coefficient/projection nodes and searches
with leanfinder, loogle, leansearch, grep and local rg found the reused system square, but no existing
declaration supplying either new obligation.

Change record: `coord/changes/C7-integral-projection-local-proof-attributes.md`, explaining
why the local proof attributes preserve the public interface and listing its sole
unchanged direct importer.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

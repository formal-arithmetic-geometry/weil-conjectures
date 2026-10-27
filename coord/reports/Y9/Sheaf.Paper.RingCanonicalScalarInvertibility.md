## What changed

Replaced the proof of `ring_canonical_scalar_invertibility` by a categorical transfer
from the existing `ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core`.
The module constructs the full-inclusion comparisons between the given and canonical
left functors and scalar functors, proves normalization of the transported square by
naturality, and uses faithfulness to identify every supplied normalized q with it.
The conjugation/mate identities prove that its mate is invertible. The private
transfer lemma takes underlying functors, adjunctions and realization maps, so
that it works across the algebraic-closure universe lift without identifying
parameterized Operation or Scalar records. The canonical normalization equation
also expresses the ambient comparison as a composite of isomorphisms. No existing declaration signature, attribute, definition, or public
import was changed.

Added `Sheaf.Paper.ExceptionalRingTransportFamily` for the missing operations-only
input to the existing scalar-mate theorem. This is the coherent finite/integral
adjunction family with actual reduction/limit reconstruction and simultaneous
proper/open realization. It asserts no scalar comparison or scalar invertibility.
The source read was Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions
5.24 and 5.26 (PDF pages 36–37 for the latter four places), together with the
published Lean records and dependency statements. The new module is imported only
for the proof.

## Proved and sorry left

Closed the item's one hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.ring_canonical_scalar_invertibility`.

Added one hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_exceptional_ring_transport_family`
(lem-sf-exceptional-ring-transport-family). Its proof is exactly `by sorry`; its
complete construction plan is in its docstring and node. The item has zero holes
left and the new module has one. This is a decomposition (one closed, one added),
not a net hole reduction. The existing scalar-mate core is used as a named
project dependency, with its own existing node and proof obligation.

All private categorical helpers are proved. The inherited geometrical hypotheses
and the complete two-universe statement of the item are preserved. Lifting the
algebraic closure changes no finite or integral stage category. No data is chosen
in a definition from a mere-existence theorem.

Validation: `lcompile.py --all` compiled both modules without errors or warnings.
The item signature was compared verbatim with the library version, line lengths
were checked, and both node files parsed. No proof import is unused.

## No longer needed

No existing import was removed. The former direct dependencies
`lem-sf-exceptional-finite-scalar-mates`, `lem-sf-exceptional-finite-operations`,
`lem-sf-exceptional-system-transport`,
`lem-pur-normalized-reconstruction-adjunction-calculus`,
`lem-weil-finite-free-completed-scalar-comparison`, and
`lem-sf-integral-compactification-system-realization` are no longer assembled
again in this module: the operations/system/reconstruction ones
are used by the new family obligation, and scalar comparison construction is reused
from the existing integral scalar-mate core. The updated node records those two
direct dependencies. No module is claimed globally unused or withdrawn; pruned: none.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted an explicit constructor for the `Transported`
family which `exceptionalIntegralScalarMates_core` takes as input. The record and
its scalar-mate theorem exist, but no theorem constructs this operations-only
family. The new lemma isolates precisely that earlier construction step, rather
than restating scalar invertibility with a new name. The combination proof is
substantive: it performs full-inclusion transport, naturality and cancellation,
and conjugate/mate transport for arbitrary supplied adjunctions and realizations.

Some older compact-support integral comparison lemmas require absolute
separatedness of X and Y. The item has no such hypothesis; none was added. The
system-transport route retains the original generality. Its coefficient-field
universe needs a lift and transport through the induced ring equivalences; this
is included in the new construction plan. The unit's realized lists
are empty, and the chosen route is within the original coefficient construction.

A full dependency scan also encountered a pre-existing cycle at
`lem-pc-ring-hom-extension-differential`, already reachable through the original
item dependencies. No added dependency has a path back to this item; this packet
does not change that unrelated cycle.

## New nodes

`lem-sf-exceptional-ring-transport-family` records the operations/reconstruction
part of the original step 1 before any scalar comparison is constructed. Its
inputs include no Allowed change and its conclusion includes no q or b. Finite
and integral stage constructors are disjoint; empty schemes give zero
adjunctions, and all finite exponents remain positive. These are the edge cases
checked for the new statement. LeanSearch and LeanFinder returned only ordinary
adjunction statements; remote grep returned no hits. Local source search found
the supplied `Transported` record and its consumers but no family constructor.
No change record is needed: no existing interface was changed.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

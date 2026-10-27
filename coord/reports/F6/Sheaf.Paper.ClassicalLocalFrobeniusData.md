## What changed

Replaced the proofs of `WeilConjectures.ClassicalLocalFrobenius.transport_blocks` and
`WeilConjectures.ClassicalLocalFrobenius.sfWeil_blocks` by inductions on the number of blocks.
The inductions use the existing `positivePower_blocks`, proved private congruence helpers,
and two separate addition laws for the old, unchanged generator. The intermediate
endpoint transports are handled by heterogeneous equality, and the conclusions retain
precisely their original `eqToHom` factors. No existing definition or signature changed.

Added proof-only imports of `Sheaf.Paper.LocalFrobeniusLargeTransportAddition` and
`Sheaf.Paper.LocalFrobeniusLargeWeilAddition`. Each new module states one addition law
with a named whole-proof sorry, a source, a complete argument in words, and its own node.
The item node now records the two actual Lean induction arguments. The definitions and
the unit route stay as published.

The generic congruence helpers avoid unfolding the common-stage categories. The new proof
sections respect transparency and keep the large pullback/compositor definitions folded.
Only the assigned sandbox was written, and compilation uses lcompile.py.

## Proved and sorry left

Original holes closed, by real Lean assembly from the two new addition laws:

- `WeilConjectures.ClassicalLocalFrobenius.transport_blocks`.
- `WeilConjectures.ClassicalLocalFrobenius.sfWeil_blocks`.

Both belong to `def-zl-classical-local-frobenius-data`. This is a decomposition of
2 of the original 4 holes, with 2 holes added, not a net reduction in the hole count.
The private helpers `transportStep_heq` and `weilStep_heq` are fully proved.

Unchanged holes left in the item, both at `def-zl-classical-local-frobenius-data`:

- `WeilConjectures.ClassicalLocalFrobenius.classicalComposition_existsUnique`.
- `WeilConjectures.ClassicalLocalFrobenius.classicalWeil_blocks`.

Holes added elsewhere:

- `WeilConjectures.LocalFrobeniusLarge.transportIterate_add`, node
  `lem-zl-large-transport-iterate-addition`.
- `WeilConjectures.LocalFrobeniusLarge.weilIterate_add`, node
  `lem-zl-large-weil-iterate-addition`.

The addition laws combine two old positive iterates. They do not mention the blocked
transport, a changed generator, `sfWeilAlong`, or a blocked Weil structure. Consequently
they are genuine concatenation steps of the original argument, not renamed block laws.
The transport proof generalizes over every N so its induction hypothesis applies to the
pulled-back object; the Weil proof uses the old m+1 map and the induction hypothesis
at product period. Positivity justifies each subtraction by one.

Edge cases checked: transport addition at a=0 and Weil addition at b=0 are exactly the
published successor recursions; a=b=0 means two steps. The block base n=0 means exactly
one block, and m=0 means the original generator. Zero objects and empty geometric fibres
require no nonzero-rank or nonemptiness hypothesis. No integral invariant lattice is
assumed for any rational Weil map.

## No longer needed

None. No import, existing dependency, node, module, or declaration was withdrawn.
The item's pre-existing proof dependency list was empty. Its original public imports
remain because the definitions and their statements use them; both new private imports
are used by the inductions. Searches found ordinary pullback and algebraic Frobenius
results, but no exact concatenation theorem for these specified common-stage maps.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof and proof_deps despite owning four unproved
coherence theorems. Their docstrings supply the intended arguments. The two block-law
arguments are now explicit in Lean, with their remaining addition steps stated separately.
The finite-level point-transport composition theorem and the integral pullback compositor
are relevant inputs to those steps, but do not themselves state these common-stage laws.
No mathematical statement was disputed or weakened, and no unit route changed.

## New nodes

`lem-zl-large-transport-iterate-addition` states concatenation of two positive point
transports using the actual inverse compositor. Its new module is
`Sheaf.Paper.LocalFrobeniusLargeTransportAddition`. Its proof in words starts from
finite restriction/coprojection and completed comparison laws and then inducts on a,
simultaneously for every point object. The existing finite-level composition and
restriction-naturality nodes are generic tools, not changes to the unit route.

`lem-zl-large-weil-iterate-addition` states concatenation of two old Weil iterates using
the actual forward compositor. Its new module is
`Sheaf.Paper.LocalFrobeniusLargeWeilAddition`. Its proof in words uses integral compositor
naturality/associativity, rational/common-stage descent, and an induction on b. The
integral compositor is a generic tool already underlying the local definitions.

Both nodes are in sec-deligne-laumon-general/sk-i-dl-general-real, inherit the current
blueprint ancestor, and record actual searches from searches.jsonl. No change record is
needed: no existing public interface, definition, statement, instance or public import
changed, and there are no consumer adaptations.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

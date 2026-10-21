## What changed

Proved all four declarations of `Sheaf.CategoryTheory.FiniteFreeCompletionTransport`
without changing their signatures. Added private proved helpers for arbitrary-presentation
reflector properties, finite-free coordinates, restriction completeness and categorical
adjunction/reflection transport. All additional imports are private proof imports. Removed the unused public import of
`Sheaf.Paper.WeilCompletedTensorReflector`.

The main comparison is constructed from the scalar adjunction and the two reflector Hom
bijections. The finite-free coordinate theorem supplies the restricted scalar object as a
finite biproduct; closure of the complete triangulated subcategory proves preservation.
The flat restriction comparison and the unit-power theorem identify the two complete
loci. This avoids a new scalar-extension calculation on strict Koszul towers. The existing
finite-free strict-tower theorem is used only to obtain ordinary exactness.

Shift, identity and composition coherence follow by cancellation against the actual units.
The shift argument uses the specified shift-compatible units and idempotence, so it does
not assume a separate compatibility property of the supplied scalar shift structure.

Updated the item's DAG proof, proof dependencies and proof origin to this route. There
are no new modules, nodes, statement changes, definition repairs or forced adaptations.
The public-import removal is recorded in
`coord/changes/finite-free-completion-proof-imports.md`, including the current consumer
and its independent import of the removed reexport.
The only current Lean importer, `Sheaf.Paper.RationalRealizationScalarCoherence`, already
imports `Sheaf.Paper.WeilCompletedTensorReflector` independently, so removal of that
reexport does not remove any declaration it sees. All four theorem signatures are
byte-identical to the original signatures.

Validation: `lcompile.py` compiled the complete delivered module without warnings in
32.8 seconds. Checked all four signatures against the shared source, zero retained holes,
100-character line limit, import-cycle checks and the revised DAG dependency graph.
On resumption, `lcompile.py --all` also compiled a scratch overlay of this module and
the unchanged direct consumer `Sheaf.Paper.RationalRealizationScalarCoherence`; the
consumer compiled cleanly in 44.8 seconds. The scratch files are not delivered.
The first resumed delivery attempt received no answer from the compile server within
645 seconds and pushed nothing; this is the documented busy-server retry condition.

## Proved and sorry left

Closed four existing holes, by declaration:

- `CategoryTheory.finiteFreeCompletionTransport`.
- `CategoryTheory.finiteFreeCompletionTransport_shift`.
- `CategoryTheory.finiteFreeCompletionTransport_id`.
- `CategoryTheory.finiteFreeCompletionTransport_comp`.

Added zero holes. There are zero `sorry`s in the delivered module. No statement has been
split off. Existing theorem dependencies with unfinished proofs are used as stated;
this delivery does not claim to close their holes or eliminate their axiom dependencies.

## No longer needed

Removed the unused public import `Sheaf.Paper.WeilCompletedTensorReflector` and the
direct private import `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`. The generic
ringed-site comparison does not use the scheme-specific `wfCompletionReflector` API;
no dependency from this item on that module is needed.
The item's proof no longer directly uses `lem-weil-pbc-ringed-cech-koszul-dual-limit` or
`def-pc-tensor-complex-sheaves`; their former direct proof-dependency entries are removed.
The dual-limit module is still needed by the existing reflector dependency, so it is not
withdrawn or claimed as globally pruned. No module is withdrawn.

All three existing top-level tool-use approvals remain applicable. In particular,
`lem-sfb-ringed-complete-triangulated` supplies closure under finite products in the main
existence proof, though the shift-coherence proof itself only needs unit idempotence.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but the existing strict scalar Koszul
comparison is stated for restriction, whereas direct tensor-tower transport needs a
scalar-extension comparison. Rather than introduce that extra calculation, the proof uses
restriction to identify complete objects and the existing finite-free coordinates to
prove that scalar extension preserves them. The scalar adjunction then gives the
comparison by the reflector universal property.

The reflector existence theorem supplies one Koszul presentation, while the statement
allows arbitrary prescribed presentations D and E. The private `principal_reflector`
helper explicitly transports the reflector properties through the common, unit-normalized
Cech comparison. No arbitrary presentation is silently replaced.

Edge cases: the finite-product argument includes rank zero, and all parameter changes
use the existing unit-power theorem with e >= 1. No nonzero, regularity, Noetherian,
boundedness, quotient-isomorphism or exact-countable-products hypothesis was added.
The conservativity helper imported from the flat ringed ideal equivalence module is
unconditional; that module's stronger equivalence theorem is not invoked.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

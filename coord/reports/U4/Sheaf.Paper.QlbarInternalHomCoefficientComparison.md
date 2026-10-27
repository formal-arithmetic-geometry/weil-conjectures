## What changed

Filled `AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficient_comparison_roof` by
assembling the existing normalized scalar Hom adjunction, section Hom presentations,
section scalar transport, and flat evaluation roof. The scalar-unit equation follows
by applying the transport adjunction equation to the identity and cancelling the inverse
extension comparison, in the private lemma `scalar_unit_transport`. The node records
this argument and its actual dependencies.
The public definition `HomTransportNormalized` now names the existing
`ModuleObjectRingedComparison.internalEvaluation` rather than repeating its exact
body; the proposition is definitionally unchanged. Added its defining module as a
plain import (reviewer correction: a public import broke two importers; the definition
is now `@[no_expose]`) and its existing definition node as a statement dependency. The change
record is `coord/changes/qlbar-hom-transport-evaluation.md`; all five downstream
modules were checked and need no adaptation.
All public statements and constructions are retained. Transparency is respected globally,
with permissive elaboration scoped to the regular-module proofs, the abstract unit
calculation, and the localization normalization conversion.

## Proved and sorry left

Closed (1 of the original 3 holes):

- `AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficient_comparison_roof`.

Remaining (2), both owned by `lem-sfb-qlbar-internal-hom-coefficient-comparison`:

- `AlgebraicGeometry.ProEtale.QlbarInternalHom.coefficient_colimit_formula`.
- `AlgebraicGeometry.ProEtale.QlbarInternalHom.qlbar_internalHom_coefficient_comparison`.

No holes added and no new split-off statements. The complete delivered Lean module
compiled cleanly through `lcompile.py` in 47.2 seconds (exit code 0) before the return.
The repaired packet compiled cleanly through a fresh server `lcompile.py` request
in 51.3 seconds (exit code 0).

## No longer needed

No modules, nodes, or existing imports pruned. The two remaining obligations retain
their existing dependency route. Experimental colimit and tensor proof imports were
removed from the delivered module after retaining only the roof proof.

## Where the brief, the DAG or earlier work was wrong

Repair of returned head `042fc66d1af` (reviewer C-042fc): the proof passed review,
but landing rejected the reviewer override filename. The change record is retained
at `coord/changes/qlbar-hom-transport-evaluation.md`. Its reviewer override must be
named `qlbar-hom-transport-evaluation.change.md`, as required by
`tools/batch_land.py`'s `fixes` filename map. This naming contract is now documented
in the record itself. The node was refreshed from current main with only the four
delivery-owned fields reapplied; no mathematical change was requested. The delivery
tool will construct the new commit on current `sheaf-dag` and run its server preflight.

The original normalization definition repeated a large native evaluation expression.
Kernel profiling isolated the two evaluation-field conversions as the main cost;
the definition now uses the existing named map with precisely the same body.

The complete normalized comparison data already exist in the section-Hom transport API.
The roof clause can be assembled from those declarations without a new intermediate
obligation. Drafts for the other two obligations are retained only in the sandbox scratchpad;
their finite-freeness and representative transports need further elaboration work.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

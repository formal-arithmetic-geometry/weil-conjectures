## What changed

Repair of returned head `6d20c9f414d` (reviewer C-6d20c). The reader passed the
mathematics; landing failed while resolving a change-record override. The packet
retains both change records at their repository paths. The landing tool's
`batch_land.fixes` requires the following filenames in a reviewer's fix directory:

| Delivered path | Reviewer override filename |
| --- | --- |
| `coord/changes/T7-internal-section-scalar-hom-folding.md` | `T7-internal-section-scalar-hom-folding.change.md` |
| `coord/changes/T7-representative-computes-formula.md` | `T7-representative-computes-formula.change.md` |

The bare filename `T7-internal-section-scalar-hom-folding.md` is not an accepted
reviewer override alias. Both records now document their accepted aliases, so this
packet needs no filename correction at landing. Its Lean and DAG changes were
compared with the current shared sources: no intervening change to their original
statements, proof dependencies or node metadata needs reconciliation. The delivery
tool recreates the packet on freshly fetched `sheaf-dag`.

Filled `continuity_iff` using the exact equivalence on complexes, the existing
representative comparison, and preservation and reflection of quasi-isomorphisms.
The inverse equivalence recovers every section diagram with its termwise lower bound.
Filled `coefficient_diagram_evaluation_transport` from `ScalarTransport.hom`,
`internalScalarHom_composition`, `Under.w`, naturality of the representative map,
and naturality of `preservesColimitNatIso`.

The theorem statements retain their original mathematical content. Private proved
helpers express the categorical transport of comparison arrows and filtered diagrams.
The transport-data module expresses `internalScalarHom` through the generic
`scalarHomMate`, with the same adjunction transpose. Its two large transport equations
are named `ScalarTransportTensor` and `ScalarTransportHom`; the structure fields
refer to those predicates. These are definitional refactors, recorded in
`coord/changes/T7-internal-section-scalar-hom-folding.md`, with no added theorem holes.
The comparison-data module also names the original representative/localization
condition as `RepresentativeComputes`, without changing any part of its formula.
The post-colimit, bounded continuity and induced-colimit-map formulas likewise use
`PostComparisonSquare`, `BoundedFilteredContinuity` and `ColimitMapSquare`. All
four types are definitionally their former formulas. The representative theorem
retains its original hole. The record is
`coord/changes/T7-representative-computes-formula.md`. The compact colimit predicates prevent repeated elaboration of concrete endpoint
constructions.
Earlier presentation and ring reconstruction experiments remain under scratchpad
and are not part of this delivery.

## Proved and sorry left

Closed two of eleven original holes, with zero holes added and zero split off:

- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.continuity_iff`.
- `AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.coefficient_diagram_evaluation_transport`.

Nine original holes remain. Each belongs to
`lem-sfb-internal-section-hom-continuity-comparison` and has its original source and
natural-language proof in the declaration docstring. All names below are in
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison`:

- `homPresentation_nonempty`.
- `internalHomRepresentative_computes`.
- `algebra_colimit_iff`.
- `internalScalarHom_identity`.
- `internalScalarHom_composition`.
- `scalarTransport_composition`.
- `restricted_hom_transport`.
- `internal_section_hom_continuity_comparison`.
- `scalarTransport_identity`.

## No longer needed

No node or module is withdrawn. The original dependencies remain relevant to the
nine unfinished clauses. Continuity transport itself needs only the categorical
colimit comparisons and Mathlib's quasi-isomorphism transport, not an additional
exact-filtered-colimit theorem. No public import is removed. No new lemma is split off.

Validation for this repair: `LCOMPILE_NO_LOCAL=1 lcompile.py --all` compiled all three
modules on the server with no errors or warnings: comparison data 20.6 s, scalar
transport data 31.3 s, main item 41.6 s, exit code 0.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed and the unit route is preserved. The earlier
server temporary-storage failure has cleared. Earlier candidate proofs had not passed
the combined check. This packet delivers the two completed clauses with the definition
refactors described above. The node proof describes these clauses explicitly and
retains the route for the remaining original holes.

The returned delivery was not rejected for a proof or definition error. Its landing
failed because change-record overrides use `<record stem>.change.md`, as checked
in `tools/batch_land.py`, rather than the delivered Markdown basename. The alias
mapping above and in both records repairs the packet's landing instructions.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

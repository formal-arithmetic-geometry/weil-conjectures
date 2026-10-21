## What changed

In `Sheaf.Paper.DerivedInternalHomFilteredColimit`, proved
`WeilConjectures.SfbHomFilteredColimit.derivedInternalHom_filteredColimit_comparison`
from the existing `scalarComparison_quasiIso`: its two conjuncts provide the
numerator and denominator quasi-isomorphisms. After registering those instances,
localization sends the numerator to an isomorphism, and the denominator inverse
and `coefficientHomResolutionIso` inverse are isomorphisms. Their composite is
the exact prescribed `derivedComparison`.

Also proved `WeilConjectures.SfbHomFilteredColimit.comparison_diagram_naturality`
by applying naturality of the existing natural transformation `comparison` to
`colimMap τ`. This covers arbitrary transition maps and uses no finite bases.

No statement, definition, public visibility, or import changed. No new nodes or
intermediate obligations were introduced. The node's existing route remains the
route of the Lean proofs: localization assembly and strict diagram naturality.

## Proved and sorry left

Closed 2 of the original 8 holes, both in namespace
`WeilConjectures.SfbHomFilteredColimit`:

- `derivedInternalHom_filteredColimit_comparison`.
- `comparison_diagram_naturality`.

Added 0 holes. Six original holes remain, all attached to
`lem-sfb-dc-hom-filtered-colimit`:

- `WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique`.
- `WeilConjectures.SfbHomFilteredColimit.filteredColimit_comparison`.
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_existsUnique`.
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_quasiIso`.
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_restriction`.
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_naturality`.

These are the original named whole-theorem holes, with their original source and
natural-language proofs. The main theorem is proved relative to the existing
scalarComparison_quasiIso obligation; this does not establish a sorry-free
transitive closure. On resumption, comparison against current sources confirmed that only these two
proof bodies differ. Launcher single-file compilation checked the retained file
again without errors or warnings in 10.3 seconds. An earlier experimental
scalar-naturality argument remains outside the delivery: its representative
transports and map formulas were not completed. No experimental helper enters
the delivery.

## No longer needed

None. No imports were removed and no nodes or modules were pruned: the six
remaining obligations still follow the recorded chain-level tensor/Hom,
K-injective and filtered-colimit argument. The two closed proofs require no
additional imports or new dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The assigned file was briefly absent
during the shared-tree refresh at session start; it subsequently became readable.
The original node and unit route are unchanged. The canonical comparison is the
specified roof, so the localization proof establishes invertibility of that map.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

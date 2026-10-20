## What changed

Filled the six infrastructure proofs in `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
`comparison_essentiallySmall`, `comparison_sheafTensorLeft`, `comparison_sheafTensorRight`,
`comparison_internalColimits`, `comparison_additive`, and `comparison_internalTotalExists`.
The existing tensor comparison theorem and its complete downstream proof are unchanged.
The proofs use the universe-smallness lemma, the closed sheaf tensor structure and symmetry,
the colimits transported across `sectionModuleEquivalence`, and the resulting colimit for
cochain totalization.

## Proved and sorry left

Closed six sorries, by declaration name:

- `CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall`
- `CategoryTheory.InternalAbelianSheafModule.comparison_sheafTensorLeft`
- `CategoryTheory.InternalAbelianSheafModule.comparison_sheafTensorRight`
- `CategoryTheory.InternalAbelianSheafModule.comparison_internalColimits`
- `CategoryTheory.InternalAbelianSheafModule.comparison_additive`
- `CategoryTheory.InternalAbelianSheafModule.comparison_internalTotalExists`

Zero sorries remain in the item. No statements were split off.

## No longer needed

None. No imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The item source still contained six infrastructure sorries even though the downstream tensor
comparison proof was already present. The DAG route remains valid; these declarations now
implement its stated infrastructure steps directly.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
